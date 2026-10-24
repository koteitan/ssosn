"""Evaluate common relative tails from the D^10 A0 reference expansions."""
import argparse
import collections
import gzip
import json
import time

import harness
import std
import token_tree as T
from above_p_data26 import HERE, raw
from reltail31_reference import Reference, Undecided, memoize_cut
from self_consistency28 import configure
from token_targets import pretty
from ordinal import cmp

REF = ('D',)*10+('A0',)
ALPHABET = ('A0','A1','A2','W','D')


def shift(word, amount):
    result=[]
    for token in word:
        if token.startswith('A'):
            k=int(token[1:])+amount
            if k<0: raise ValueError((word,amount))
            result.append('A'+str(k))
        else: result.append(token)
    return tuple(result)


def seed_relative(base, physical_tail, depth):
    base_raw=T.raw_tokens(base)
    a=T.ordinal(T.fold(T.parse(base_raw,True),general=True))
    b=T.ordinal(T.fold(T.parse(base_raw+physical_tail,True),general=True))
    for _ in range(depth):
        if not a or not b or a[:-1]!=b[:-1] or a[-1][1] or b[-1][1]:
            raise T.Unknown('active-depth indices do not share a power prefix')
        a,b=a[-1][2],b[-1][2]
    i=0
    while i<min(len(a),len(b)) and a[i]==b[i]:i+=1
    delta=b[i:]
    # Check the ordinal subtraction by reusing ordinal.add on the stored tuples.
    from ordinal import add
    if cmp(b,a)<0 or add(a,delta)!=b:
        raise T.Unknown('no right-relative ordinal')
    return delta


def collect():
    data=json.load(gzip.open(HERE/'reltail-cap31.json.gz','rt'))
    out={}
    for row in data['rows']:
        tail=tuple(row['tail'])
        if len(tail)<=7 and row['standard'][4] and T.raw_tokens(tail)<T.raw_tokens(('W',)+('D',)*10+('A1',)):
            out[T.raw_tokens(tail)]={'tail':tail,'source':['common-reference-language']}
    inv=json.load(gzip.open(HERE/'inversion29.json.gz','rt'))
    for row in inv['rows']:
        physical=tuple(row['result']['parent_shape']['tokens'])
        j=max(i for i,t in enumerate(physical) if t.startswith(('A','E')))
        base,tail=physical[:j+1],physical[j+1:]
        depth=int(base[-1][1:]) if base[-1].startswith('A') else 0
        normalized=shift(tail,-depth)
        key=T.raw_tokens(normalized)
        entry=out.setdefault(key,{'tail':normalized,'source':[]})
        item=dict(base=base,tail=tail,depth=depth,normalized=normalized)
        if item not in entry.setdefault('clusters',[]):entry['clusters'].append(item)
        if 'inversion29' not in entry['source']:entry['source'].append('inversion29')
    return sorted(out.values(),key=lambda x:(0 if 'common-reference-language' in x['source'] else 1,
                                              len(x['tail']),x['tail']))


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--seconds',type=float,default=.4)
    ap.add_argument('--nodes',type=int,default=15000)
    ap.add_argument('--budget',type=float,default=480)
    args=ap.parse_args();configure('seed');memoize_cut();start=time.monotonic()
    rows=[];ref=Reference(raw(REF),samples=5,seconds=args.seconds,max_nodes=args.nodes,max_memo=30000)
    selected=collect()
    for item in selected:
        tail=item['tail']; physical=T.raw_tokens(tail);r=dict(tail=tail,source=item['source'])
        try:
            if 'common-reference-language' not in item['source']:
                s=raw(REF)+physical
                if not std.is_standard(s) or physical>=T.raw_tokens(('W',)+('D',)*10+('A1',)):
                    raise Undecided('outside common-reference cap/language')
            value=ref.evaluate(physical)
            r.update(status='inferred5',value=value,pretty=pretty(value))
            try:
                seventh=Reference(raw(REF),samples=7,seconds=args.seconds,max_nodes=args.nodes,
                                  max_memo=30000).evaluate(physical)
                r['value7']=pretty(seventh)
                r['status']='stable3_5_7' if value==seventh else 'unstable5_7'
            except Undecided as e:r['seven_undecided']=str(e)
        except Undecided as e:r.update(status='undecided',reason=str(e))
        try:
            seed=seed_relative(REF+('A0',),physical,0)
            r['seed']=pretty(seed)
            if 'value' in r:r['vs_seed']=cmp(r['value'],seed)
        except Exception as e:r['seed_unknown']=str(e)
        if 'clusters' in item:
            r['clusters']=[]
            for cl in item['clusters']:
                try:
                    base=tuple(cl['base']);tailraw=T.raw_tokens(cl['tail'])
                    sv=seed_relative(base,tailraw,int(cl['depth']))
                    r['clusters'].append(dict(base=base,physical_tail=cl['tail'],
                        depth=cl['depth'],seed=pretty(sv),vs_F=None if 'value' not in r else cmp(r['value'],sv)))
                except Exception as e:
                    r['clusters'].append(dict(base=cl['base'],physical_tail=cl['tail'],
                                               depth=cl['depth'],seed_unknown=str(e)))
        rows.append(r)
        if len(rows)%50==0:print(len(rows),collections.Counter(x['status'] for x in rows),
                                  'seconds',round(time.monotonic()-start,1),flush=True)
        if time.monotonic()-start>=args.budget:break
    # The finite order audit uses only values whose 3-, 5-, and 7-sample
    # inferences coincide. Equal raw spellings are already deduplicated.
    ordered=sorted((r for r in rows if r['status']=='stable3_5_7' and
                    'common-reference-language' in r['source']),key=lambda r:T.raw_tokens(r['tail']))
    violations=[]
    for a,b in zip(ordered,ordered[1:]):
        if cmp(a['value'],b['value'])>=0:
            violations.append(dict(left=a['tail'],left_value=a['pretty'],right=b['tail'],right_value=b['pretty']))
    report=dict(reference_base=REF,cap=('W',)+('D',)*10+('A1',),max_tokens=7,
        tail_count=len(selected),processed=len(rows),complete=len(rows)==len(selected),
        counts=dict(collections.Counter(r['status'] for r in rows)),rows=rows,
        order_audit=dict(stable_values=len(ordered),adjacent_violations=len(violations),examples=violations[:30]),
        method='induced reference cut, strip exact outer terminal, recurse on contracted tails; evalord.sup first 3 and 5, then independently 7; all unstable, timeout, cap, escape, and unknown cases retained')
    with gzip.open(HERE/'reltail31-common.json.gz','wt') as f:json.dump(report,f,ensure_ascii=False,separators=(',',':'))
    with open(HERE/'reltail31-common-summary.json','w') as f:json.dump({k:v for k,v in report.items() if k!='rows'},f,ensure_ascii=False,indent=2)
    print('FINAL',report['complete'],report['processed'],report['counts'],report['order_audit'],
          'seconds',round(time.monotonic()-start,2),flush=True)


if __name__=='__main__':main()
