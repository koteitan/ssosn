"""Descend every seed standard-not-new failure, with exact least-n search.

timeout 600 python3 work/inversion29.py [--resume]
Worst partners are the prefix maximum and suffix minimum in the extended §27
reference set. Both sides are followed if both fail. Spelling weights retained.
"""
import argparse
import bisect
import collections
from functools import lru_cache
import gzip
import json
import time

import harness
import std
import token_tree as T
from ordinal import cmp,cmp_p,succ
from token_targets import pretty
from above_p_data26 import HERE,raw
from self_consistency28 import configure


def tokens(s):
    for terminal in ((),(0,1),(0,)):
        tail=s[4:] if not terminal else s[4:-len(terminal)]
        if terminal and s[-len(terminal):]!=terminal:continue
        try:return dict(tokens=T.parse(tail,True),terminal=terminal)
        except T.Unknown:pass
    return dict(tokens=None,terminal=None,raw=s)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--resume',action='store_true')
    parser.add_argument('--budget',type=float,default=520)
    parser.add_argument('--case-budget',type=float,default=15)
    args=parser.parse_args()
    configure('seed')
    start=time.monotonic()
    data=json.load(gzip.open(HERE/'above-p26-data.json.gz','rt'))
    old=json.load(gzip.open(HERE/'value-new26-seed.json.gz','rt'))
    labels={};weights=collections.Counter()
    for row in data['rows']:
        if row['standard']:
            s=raw(row['tokens']);word=tuple(row['tokens']);weights[s]+=1
            if s not in labels or (len(word),word)<(len(labels[s]),labels[s]):labels[s]=word
    refs=set(labels)
    for row in old['mismatches']:
        if 'outside_witness' in row:refs.add(tuple(row['outside_witness']['raw']))
    calls=0
    @lru_cache(maxsize=50000)
    def value(s):
        nonlocal calls
        try:return T.value(s)
        finally:
            calls+=1
            if calls%512==0:
                T.value_tree.cache_clear();T.body_tree.cache_clear();T.block_tree.cache_clear()
            if calls%4096==0:cmp.cache_clear();cmp_p.cache_clear()
    @lru_cache(maxsize=32768)
    def pieces(s):
        c=harness.Seq(s,'new').cut()
        return s[:c],s[c:-1]+(s[-1]-1,)
    refs=sorted(refs)
    for s in refs:value(s)
    lower=[];upper=[None]*len(refs);best=None
    for i,s in enumerate(refs):
        if best is None or cmp(value(s),value(refs[best]))>0:best=i
        lower.append(best)
    best=None
    for i in range(len(refs)-1,-1,-1):
        if best is None or cmp(value(refs[i]),value(refs[best]))<0:best=i
        upper[i]=best
    pairs=[];failed_sources=set();both=0
    for s in sorted(labels,key=lambda s:(len(labels[s]),labels[s])):
        i=bisect.bisect_left(refs,s);j=bisect.bisect_right(refs,s);count=0
        if i and cmp(value(refs[lower[i-1]]),value(s))>=0:
            pairs.append(dict(source=s,source_tokens=labels[s],weight=weights[s],side='lower',
                              a=refs[lower[i-1]],b=s));count+=1
        if j<len(refs) and cmp(value(s),value(refs[upper[j]]))>=0:
            pairs.append(dict(source=s,source_tokens=labels[s],weight=weights[s],side='upper',
                              a=s,b=refs[upper[j]]));count+=1
        if count:failed_sources.add(s)
        if count==2:both+=1
    assert len(failed_sources)==1139 and sum(weights[s] for s in failed_sources)==1892
    out=HERE/'inversion29.json.gz'
    if args.resume:
        report=json.load(gzip.open(out,'rt'))
        assert report['total_pairs']==len(pairs)
    else:
        report=dict(total_pairs=len(pairs),sources=1139,source_spellings=1892,
            sources_with_both_sides=both,pair_spelling_weight=sum(p['weight'] for p in pairs),
            processed=0,complete=False,rows=[],seconds=0,
            partner_method='all extended references; max lower, min upper; follow both failing sides')
    prior=report['seconds']
    @lru_cache(maxsize=32768)
    def standard(s):return std.is_standard(s)
    def save():
        report['seconds']=prior+time.monotonic()-start
        pending=out.with_name(out.name+'.pending')
        with gzip.open(pending,'wt') as target:json.dump(report,target,ensure_ascii=False,separators=(',',':'))
        pending.replace(out)
    for number in range(report['processed'],len(pairs)):
        pair=pairs[number];a,b=pair['a'],pair['b'];va=value(a)
        assert a<b and cmp(va,value(b))>=0
        path=[];begin=time.monotonic();result=None
        for step in range(4000):
            if time.monotonic()-begin>args.case_budget:
                result=dict(status='case_timeout',b=b);break
            vb=value(b)
            assert a<b and cmp(va,vb)>=0
            if b[-1]==0:
                pred=b[:-1];vp=value(pred)
                path.append(dict(b=b,kind='successor',predecessor=pred))
                if vb!=succ(vp):
                    result=dict(status='successor_root',b=b,term=pred,n=None,parent=pretty(vb),child=pretty(vp));break
                if pred<a:
                    result=dict(status='successor_gap',b=b,term=pred);break
                b=pred;continue
            g,repeat=pieces(b)
            high=max(1,(len(a)-len(g))//len(repeat)+1)
            if g+repeat*high<a:
                result=dict(status='no_gaps_failure',b=b);break
            left,right=1,high
            while left<right:
                mid=(left+right)//2
                if g+repeat*mid>=a:right=mid
                else:left=mid+1
            n=left;term=g+repeat*n
            assert term>=a and (n==1 or g+repeat*(n-1)<a)
            assert term<b
            try:vt=value(term)
            except T.Unknown as error:
                result=dict(status='Unknown',b=b,n=n,term=term,reason=str(error));break
            path.append(dict(b=b,n=n,term=term,vs_parent=cmp(vt,vb)))
            if cmp(vt,vb)>=0:
                result=dict(status='term_root',b=b,n=n,term=term,parent=pretty(vb),child=pretty(vt),
                    parent_shape=tokens(b),child_shape=tokens(term),
                    parent_standard=standard(b),term_standard=standard(term),
                    vs_parent=cmp(vt,vb));break
            b=term
        if result is None:result=dict(status='step_limit',b=b)
        report['rows'].append(dict(**pair,result=result,path=path,steps=len(path),seconds=time.monotonic()-begin))
        report['processed']=number+1
        if (number+1)%100==0:
            save();print(number+1,'/',len(pairs),dict(collections.Counter(r['result']['status'] for r in report['rows'])),
                         'seconds',round(report['seconds'],1),flush=True)
        if time.monotonic()-start>=args.budget:break
    report['complete']=report['processed']==len(pairs)
    save()
    print('FINAL',report['complete'],'pairs',len(pairs),'counts',dict(collections.Counter(r['result']['status'] for r in report['rows'])),
          'seconds',round(report['seconds'],2),flush=True)


if __name__=='__main__':main()
