"""Cross-context capped membership, using cofinal markers rather than values.

timeout 600 python3 work/reltail_cap31.py --N 9
The common-language reference is an independent larger base D^(N+1) A_l.
This is a finite consistency test, not a global binary-map construction.
"""
import argparse
import collections
from functools import lru_cache
import gzip
import json
import time
import harness
import std
from above_p_data26 import HERE,raw
from reltail30_check import shifted

ALPHABET=('A0','A1','A2','W','D')


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--N',type=int,default=9)
    args=ap.parse_args();start=time.monotonic()
    if not 4<=args.N<=12:ap.error('N must be 4..12 so the independent reference is above the tested bases')
    configs=[('DW_A0',('D','W'),0),('DD_A0',('D','D'),0),('DDD_A0',('D','D','D'),0),
             ('DDD_A1',('D','D','D'),1),
             ('ref_A0',('D',)*(args.N+1),0),('ref_A1',('D',)*(args.N+1),1),
             ('check_A0',('D',)*(args.N+2),0),('check_A1',('D',)*(args.N+2),1)]
    cls=harness.Seq;original=cls.cut
    @lru_cache(maxsize=32768)
    def cut(s,mode):return original(cls(s,mode))
    cls.cut=lambda self:cut(self.S,self.mode)
    @lru_cache(maxsize=150000)
    def standard(s):return std.is_standard(s)
    bases=[z+('A'+str(d),) for _,z,d in configs]
    assert all(standard(raw(base)) for base in bases)
    markers=[];certificates=[]
    for i,(name,z,d) in enumerate(configs[:4]):
        base=bases[i];reference=bases[4 if d==0 else 5]
        sibling=raw(z+('A'+str(d+1),));marker=('W',)+z+('A'+str(d+1),)
        q=raw(('W',)+z+('A'+str(d),))[4:];v=(0,1)
        cap_cut=harness.Seq(sibling,'new').cut();g=sibling[:cap_cut];b=sibling[cap_cut:-1]+(sibling[-1]-1,)
        assert standard(sibling) and g+b==raw(base)+v and v+b==q+v
        upper=raw(reference+marker);c=harness.Seq(upper,'new').cut()
        gu,bu=upper[:c],upper[c:-1]+(upper[-1]-1,)
        assert standard(upper) and gu+bu==raw(reference)+q+v and v+bu==q+v
        markers.append(raw(marker)[4:])
        certificates.append(dict(base=base,sibling=sibling,reference=reference,marker=marker,Q=q,
            sibling_cut=cap_cut,marker_cut=c,all_n_word_identities=True))
    # Every descendant of a prefix rejected in all contexts is rejected
    # in every context. Such words also fail the reference predicate; they
    # contribute only true negatives. Keep their counts implicit.
    frontier={():[True]*len(configs)};rows=[dict(tail=(),standard=[True]*len(configs))]
    tested=1;levels=[]
    for length in range(1,args.N+1):
        following={};counts=[0]*len(configs)
        for prefix,prior in frontier.items():
            for token in ALPHABET:
                if not prefix and token=='D':continue  # tail<D: same unit only
                word=prefix+(token,);flags=[]
                for j,(_,z,d) in enumerate(configs):
                    good=prior[j] and standard(raw(bases[j]+shifted(word,d)))
                    flags.append(good)
                    if good:counts[j]+=1
                rows.append(dict(tail=word,standard=flags));tested+=1
                if any(flags):following[word]=flags
        frontier=following;levels.append(dict(length=length,standard=counts,tested=tested))
        print(levels[-1],'seconds',round(time.monotonic()-start,1),flush=True)
    matrices=[collections.Counter() for _ in range(4)];mismatches=[[] for _ in range(4)]
    unique=[{} for _ in configs]
    for row in rows:
        word=tuple(row['tail']);flags=row['standard']
        for i,(_,_,d) in enumerate(configs):
            key=raw(shifted(word,d))[4:]
            if key in unique[i]:assert unique[i][key]==flags[i]
            unique[i][key]=flags[i]
        for i,(_,_,d) in enumerate(configs[:4]):
            reference=flags[4 if d==0 else 5]
            physical=raw(shifted(word,d))[4:]
            predicted=reference and physical<markers[i]
            matrices[i][f'{flags[i]}:{predicted}']+=1
            if predicted!=flags[i]:mismatches[i].append(dict(tail=word,standard=flags[i],predicted=predicted))
    universe=5**args.N
    for matrix in matrices:matrix['False:False']+=universe-tested
    initial=[]
    for i,(_,_,d) in enumerate(configs[:4]):
        reference=unique[4 if d==0 else 5];rejected=None;bad=[]
        # A source-positive word absent from the reference is already a
        # membership mismatch; include the union in the initial-segment audit.
        for t in sorted(set(reference)|set(unique[i])):
            if not (reference.get(t,False) or unique[i].get(t,False)):continue
            if not unique[i].get(t,False):
                if rejected is None:rejected=t
            elif rejected is not None:bad.append(dict(earlier=rejected,later=t))
        initial.append(dict(violations=len(bad),examples=bad[:20]))
    saturation=[[],[]]
    for row in rows:
        for d in (0,1):
            if row['standard'][4+d]!=row['standard'][6+d]:saturation[d].append(row['tail'])
    report=dict(max_tokens=args.N,configs=configs,domain='tail raw < (0,2), next sibling excluded',
        reference_method='independent D^(N+1) unit at the same depth, finite empirical common language',
        cap_method='same cofinal copy Q in sibling and reference marker; no guessed ordinal values',
        full_spelling_universe=universe,explicitly_tested=tested,levels=levels,rows=rows,
        matrices=[dict(m) for m in matrices],mismatches=mismatches,
        standard_spellings=[sum(r['standard'][i] for r in rows) for i in range(len(configs))],
        unique_standard=[sum(u.values()) for u in unique],initial_segment_audit=initial,
        larger_reference_differences=saturation,
        certificates=certificates,seconds=time.monotonic()-start)
    with gzip.open(HERE/'reltail-cap31.json.gz','wt') as target:json.dump(report,target,ensure_ascii=False,separators=(',',':'))
    (HERE/'reltail-cap31-summary.json').write_text(json.dumps({k:v for k,v in report.items() if k!='rows'},ensure_ascii=False,indent=2)+'\n')
    print('FINAL',report['matrices'],'mismatches',[len(m) for m in mismatches],
          'initial',[a['violations'] for a in initial],'seconds',round(report['seconds'],2),flush=True)


if __name__=='__main__':main()
