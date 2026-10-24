"""Measure the existing above-P candidates; never change a value rule.

timeout 600 python3 work/value_new26.py cut
Variants: cut (§21), movable (§18), general (§17), seed (§27), iterate (§28).
"""
import argparse
import bisect
import collections
from functools import lru_cache
import gzip
import json
from pathlib import Path
import time

import std
import harness
import token_tree as T
from ordinal import cmp,cmp_p
from token_targets import pretty
from above_p_data26 import HERE,raw,P,UPPER


def run(data,variant):
    start=time.monotonic()
    T.CUT_COPY_ACTION_EXPERIMENT=variant in ('cut','seed','iterate','reltail')
    T.CONSISTENT_COPY_SEED_EXPERIMENT=variant in ('seed','iterate','reltail')
    T.WD_AFTER_ITERATION_EXPERIMENT=variant=='iterate'
    T.GENERAL_COPY_EXPERIMENT=variant in ('general','movable')
    T.MOVABLE_ONE_EXPERIMENT=variant=='movable'
    T.RELTAIL_CAP_EXPERIMENT=variant=='reltail'
    T.RELTAIL_CAP_COUNTS={'eligible':0,'table':0,'fallback':0}
    if variant=='reltail':
        T.reltail_cap_load(HERE/'reltail31-common.json.gz')
    seq_class=harness.Seq
    original_cut=seq_class.cut
    @lru_cache(maxsize=32768)
    def cut(s,mode):return original_cut(seq_class(s,mode))
    seq_class.cut=lambda self:cut(self.S,self.mode)
    @lru_cache(maxsize=32768)
    def verified_standard(s):return std.is_standard(s)
    rows=sorted(data['rows'],key=lambda r:(len(r['tokens']),r['tokens']))
    standard_raw={raw(r['tokens']) for r in rows if r['standard']}
    # Raw sequences, rather than spellings, are the ordering keys.
    labels={}
    for row in rows:labels.setdefault(raw(row['tokens']),tuple(row['tokens']))
    values={};unknown={};calls=0
    def evaluate(s):
        nonlocal calls
        s=tuple(s)
        if s in values:return values[s]
        if s in unknown:return None
        try:values[s]=T.value(s)
        except T.Unknown as error:unknown[s]=str(error)
        calls+=1
        if calls%512==0:
            T.value_tree.cache_clear();T.body_tree.cache_clear();T.block_tree.cache_clear()
        if calls%4096==0:
            cmp.cache_clear();cmp_p.cache_clear()
        return values.get(s)
    def witness(s):
        value=evaluate(s)
        return dict(tokens=labels.get(s),raw=s,value=None if value is None else pretty(value),
                    unknown=unknown.get(s))
    def sides(s,value,refs,keys,lower,upper):
        left=bisect.bisect_left(keys,s)
        right=bisect.bisect_right(keys,s)
        lo=refs[lower[left-1]] if left else None
        up=refs[upper[right]] if right<len(refs) else None
        return (lo is None or cmp(evaluate(lo),value)<0,
                up is None or cmp(value,evaluate(up))<0,lo,up)
    def reference_index(refs):
        refs=sorted(refs);lower=[];upper=[None]*len(refs);best=None
        for i,s in enumerate(refs):
            if best is None or cmp(evaluate(s),evaluate(refs[best]))>0:best=i
            lower.append(best)
        best=None
        for i in range(len(refs)-1,-1,-1):
            if best is None or cmp(evaluate(refs[i]),evaluate(refs[best]))<0:best=i
            upper[i]=best
        return refs,refs,lower,upper
    for i,s in enumerate(sorted(standard_raw),1):
        evaluate(s)
        if i%2000==0:print(variant,'standard values',i,'elapsed',round(time.monotonic()-start,1),flush=True)
    known_refs=[s for s in standard_raw if s in values]
    index=reference_index(known_refs)
    refs=index[0]
    adjacent=[dict(left=witness(a),right=witness(b),relation=cmp(evaluate(a),evaluate(b)))
              for a,b in zip(refs,refs[1:]) if cmp(evaluate(a),evaluate(b))>=0]
    counts=collections.Counter();unique_counts=collections.Counter();seen=set()
    side_counts=collections.Counter();mismatches=[];unknown_rows=[]
    external=set();external_all=set();boundaries=[]
    for i,row in enumerate(rows,1):
        word=tuple(row['tokens']);s=raw(word);actual=row['standard'];value=evaluate(s)
        if value is None:
            counts[f'{actual}:Unknown']+=1
            if s not in seen:unique_counts[f'{actual}:Unknown']+=1;seen.add(s)
            unknown_rows.append(dict(tokens=word,standard=actual,reason=unknown[s]))
            continue
        lo,up,left,right=sides(s,value,*index)
        passes=lo and up
        counts[f'{actual}:{passes}']+=1
        if s not in seen:unique_counts[f'{actual}:{passes}']+=1;seen.add(s)
        if not actual:side_counts[f'lower={lo},upper={up}']+=1
        if passes!=actual:
            result=dict(tokens=word,raw=s,standard=actual,value_new=passes,value=pretty(value),
                lower_pass=lo,upper_pass=up,lower_witness=None if left is None else witness(left),
                upper_witness=None if right is None else witness(right))
            if not actual:
                ceiling=std.ceil(s)
                ceiling_standard=std.is_standard(ceiling)
                pv=evaluate(ceiling)
                outside=ceiling not in standard_raw
                result['ceiling_partner']=dict(**witness(ceiling),standard_verified=ceiling_standard,
                    outside_data=outside,raw_above=s<ceiling,
                    candidate_vs_partner=None if pv is None else cmp(value,pv))
                try:result['ceiling_partner']['canonical_tokens']=T.parse(ceiling[4:],True)
                except T.Unknown:pass
                if ceiling_standard and outside and pv is not None:
                    external_all.add(ceiling)
                    if s<ceiling and cmp(value,pv)>=0:
                        boundaries.append(result);external.add(ceiling)
                        result['outside_witness']=dict(method='ceil',**result['ceiling_partner'])
                if 'outside_witness' not in result and ceiling_standard:
                    # A missing lower witness may be a longer real term of
                    # ceil(s). Check its standardness and value directly.
                    # This adds test data only; it never adjusts the rule.
                    probes=[]
                    for n in range(1,6):
                        term=harness.fs(ceiling,n)
                        tv=evaluate(term)
                        term_standard=verified_standard(term)
                        probe=dict(n=n,raw=term,value=None if tv is None else pretty(tv),
                            standard_verified=term_standard,raw_below=term<s,
                            candidate_vs_partner=None if tv is None else cmp(value,tv))
                        probes.append(probe)
                        if term_standard and tv is not None and term not in standard_raw:
                            if term<s and cmp(tv,value)>=0:
                                external_all.add(term);external.add(term);boundaries.append(result)
                                result['outside_witness']=dict(method='ceil real term',**probe)
                                break
                    result['outside_probes']=probes
            mismatches.append(result)
        if i%5000==0:print(variant,'candidates',i,'elapsed',round(time.monotonic()-start,1),flush=True)
    # Evaluate all known external ceil witnesses globally. This can expose
    # additional failures among previously passing standard words.
    extended_index=reference_index(set(known_refs)|external_all)
    extended_counts=collections.Counter();extended_unique=collections.Counter();seen=set()
    extended_examples=collections.defaultdict(list)
    for row in rows:
        s=raw(row['tokens']);v=evaluate(s);actual=row['standard']
        if v is None:
            extended_counts[f'{actual}:Unknown']+=1
            if s not in seen:extended_unique[f'{actual}:Unknown']+=1;seen.add(s)
            continue
        lo,up,left,right=sides(s,v,*extended_index)
        extended_counts[f'{actual}:{lo and up}']+=1
        if s not in seen:extended_unique[f'{actual}:{lo and up}']+=1;seen.add(s)
        if actual!=(lo and up) and len(extended_examples[str(actual)])<20:
            extended_examples[str(actual)].append(dict(tokens=row['tokens'],raw=s,standard=actual,
                value=pretty(v),lower_pass=lo,upper_pass=up,
                lower_witness=None if left is None else witness(left),
                upper_witness=None if right is None else witness(right)))
    extended_refs=extended_index[0]
    extended_adjacent=[dict(left=witness(a),right=witness(b),relation=cmp(evaluate(a),evaluate(b)))
         for a,b in zip(extended_refs,extended_refs[1:]) if cmp(evaluate(a),evaluate(b))>=0]
    # Inspect the historical counterexample and its immediate standard
    # neighbours, as well as its actual real terms (including terminal 01).
    target_tokens=('D','W','A2','A1');target=raw(target_tokens)
    focus=dict(standard=std.is_standard(target),**witness(target))
    # witness already supplies tokens; preserve the requested spelling.
    focus['tokens']=target_tokens
    pos=bisect.bisect_left(extended_refs,target)
    focus['neighbours']=[witness(s) for s in extended_refs[max(0,pos-3):pos+4]]
    target_value=evaluate(target)
    if target_value is not None:
        lo,up,left,right=sides(target,target_value,*extended_index)
        focus.update(value_new=lo and up,lower_pass=lo,upper_pass=up,
            lower_witness=None if left is None else witness(left),
            upper_witness=None if right is None else witness(right))
    focus['terms']=[]
    for n in range(1,6):
        term=harness.fs(target,n);v=evaluate(term)
        entry=dict(n=n,standard=std.is_standard(term),**witness(term))
        if v is not None and target_value is not None:entry['vs_parent']=cmp(v,target_value)
        try:entry['body_tokens']=T.parse(term[4:-2],True);entry['terminal']=(0,1)
        except T.Unknown:pass
        focus['terms'].append(entry)
    return dict(variant=variant,flags=dict(CUT_COPY_ACTION_EXPERIMENT=T.CUT_COPY_ACTION_EXPERIMENT,
        GENERAL_COPY_EXPERIMENT=T.GENERAL_COPY_EXPERIMENT,MOVABLE_ONE_EXPERIMENT=T.MOVABLE_ONE_EXPERIMENT,
        CONSISTENT_COPY_SEED_EXPERIMENT=T.CONSISTENT_COPY_SEED_EXPERIMENT,
        WD_AFTER_ITERATION_EXPERIMENT=T.WD_AFTER_ITERATION_EXPERIMENT,
        RELTAIL_CAP_EXPERIMENT=T.RELTAIL_CAP_EXPERIMENT),
        max_tokens=data['max_tokens'],lower_bound=P,upper_bound=UPPER,
        spelling_counts=dict(counts),unique_raw_counts=dict(unique_counts),nonstandard_sides=dict(side_counts),
        references_total=len(standard_raw),references_known=len(known_refs),
        references_unknown=len(standard_raw)-len(known_refs),
        pass_means='passes against known references only; Unknown references are not silently validated',
        adjacent_failures=adjacent,mismatches=mismatches,unknown_rows=unknown_rows,
        confirmed_outside_collisions=len(boundaries),outside_collision_witnesses=len(external),
        outside_known_witnesses=len(external_all),extended_reference_count=len(extended_refs),
        unknown_external_probes=sum(p['value'] is None for r in mismatches for p in r.get('outside_probes',[])),
        extended_counts=dict(extended_counts),
        extended_unique_raw_counts=dict(extended_unique),extended_examples=dict(extended_examples),
        extended_adjacent_failures=extended_adjacent,focus92=focus,
        reltail_cap_counts=dict(T.RELTAIL_CAP_COUNTS),
        seconds=time.monotonic()-start)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('variant',choices=('cut','movable','general','seed','iterate','reltail'))
    parser.add_argument('--data',type=Path,default=HERE/'above-p26-data.json.gz')
    args=parser.parse_args()
    with gzip.open(args.data,'rt') as source:data=json.load(source)
    if data['max_tokens']!=data['requested_max_tokens']:
        parser.error('data generation is not complete yet')
    report=run(data,args.variant)
    out=HERE/f'value-new26-{args.variant}.json.gz'
    with gzip.open(out,'wt',encoding='utf-8') as target:json.dump(report,target,ensure_ascii=False,separators=(',',':'))
    print(args.variant,'counts',report['spelling_counts'],'extended',report['extended_counts'],
        'unknown refs',report['references_unknown'],'adjacent',len(report['adjacent_failures']),
        'boundary',report['confirmed_outside_collisions'],'seconds',round(report['seconds'],2),flush=True)
    print('focus92',report['focus92'],flush=True)


if __name__=='__main__':main()
