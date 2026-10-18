"""Measure the proposed same-index FS relation without fitting new values.

Ordinary mode uses token_tree with every experimental flag off. The separate
#92 probe uses exactly the rejected §21 setting. Rank/cut structures are rebuilt
for each sequence. Finite diagnostics do not establish all-n cofinality.
"""
import argparse
import collections
import gzip
import itertools
import json
import time
from pathlib import Path
import harness
import lift
import std
import token_tree as T
from cut_structure import CutTree
from ordinal import cmp,fs,nat,succ,is_limit,cmp_p
from token_targets import pretty

HERE=Path(__file__).resolve().parent

def value(s):
    return nat(len(s)) if not any(s) else T.value(s)

def clear():
    fs.cache_clear();cmp.cache_clear();cmp_p.cache_clear()
    T.value_tree.cache_clear();T.body_tree.cache_clear();T.block_tree.cache_clear()

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--N',type=int,default=5);ap.add_argument('--C',type=int,default=8)
    args=ap.parse_args();started=time.monotonic()
    report=dict(N=args.N,C=args.C,phases={},diagnostic_lower_zero='only for two-sided-shift diagnostic: index <=0 means ordinal zero')
    def save():
        report['seconds']=time.monotonic()-started
        (HERE/'fs-translation-check.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    def phase(name,seqs):
        counts=collections.Counter();upperhist=collections.Counter();bhist=collections.Counter();twohist=collections.Counter()
        lower_by_n=collections.Counter();first={};rows=[];exact_global=set(range(args.C+1))
        for i,s in enumerate(seqs,1):
            s=tuple(s)
            try:
                x=value(s)
                if s[-1]==0:
                    ok=x==succ(value(s[:-1]));counts['successor_agree' if ok else 'successor_DIFFER']+=1
                    if not ok:first.setdefault('successor',dict(sequence=s,value=pretty(x)))
                    continue
                counts['limit_input']+=1
                if not is_limit(x):counts['nonlimit_value']+=1;continue
                structure=CutTree.build(s);terms=[value(structure.repeat(n)) for n in range(1,args.N+1)]
                standard=[None]+[fs(x,k) for k in range(1,args.N+args.C+1)]
            except T.Unknown as exc:
                counts['unresolved']+=1
                first.setdefault('unresolved',dict(sequence=s,reason=str(exc)));continue
            lowers=[n for n,y in enumerate(terms,1) if cmp(standard[n],y)>0]
            for n in lowers:lower_by_n[n]+=1
            uppers=[c for c in range(args.C+1) if all(cmp(y,standard[n+c])<=0 for n,y in enumerate(terms,1))]
            exact=[c for c in range(args.C+1) if all(y==standard[n+c] for n,y in enumerate(terms,1))]
            two=[c for c in range(args.C+1) if all((n<=c or cmp(standard[n-c],y)<=0) and cmp(y,standard[n+c])<=0
                                                      for n,y in enumerate(terms,1))]
            below=all(cmp(y,x)<0 for y in terms)
            counts['terms_below_parent' if below else 'term_exceeds_or_equals_parent']+=1
            counts['lower_agree' if not lowers else 'lower_FAIL']+=1
            if exact:counts['exact_shift_exists']+=1
            else:counts['exact_shift_absent']+=1
            exact_global.intersection_update(exact)
            upper=uppers[0] if uppers else None
            upperhist[str(upper)]+=1
            if not lowers and upper is not None:bhist[str(upper)]+=1;counts['b_satisfied']+=1
            else:counts['b_FAILED']+=1
            twohist[str(two[0] if two else None)]+=1
            row=dict(sequence=''.join(map(str,s)),lower_fail_n=lowers,min_upper_shift=upper,
                     exact_shifts=exact,min_two_sided_shift=two[0] if two else None,terms_below_parent=below)
            rows.append(row)
            for reason,condition in [('lower',bool(lowers)),('upper',not uppers),('exact',not exact),('two_sided',not two)]:
                if condition and reason not in first:
                    first[reason]=dict(**row,parent=pretty(x),terms=[pretty(y) for y in terms],
                                      fundamental={str(k):pretty(standard[k]) for k in range(1,args.N+args.C+1)})
            if i%2000==0:
                print(name,i,dict(counts),flush=True);clear()
        result=dict(counts=counts,upper_shift_histogram=upperhist,b_shift_histogram=bhist,two_sided_shift_histogram=twohist,
                    lower_failures_by_n=lower_by_n,common_exact_shifts=sorted(exact_global),first=first)
        report['phases'][name]=result
        with gzip.open(HERE/('fs-translation-'+name+'.json.gz'),'wt') as stream:json.dump(rows,stream,separators=(',',':'))
        save();clear();print(name,'FINAL',dict(counts),'upper',dict(upperhist),'two',dict(twohist),flush=True)
    def binary():
        for size in range(13):
            for bits in itertools.product((0,1),repeat=size):
                s=(0,0)+bits
                if std.is_standard(s):yield s
    phase('binary',binary())
    lift.unlift((2,1));phase('lift5350',((0,0)+u for u in lift._INV))
    core=json.loads((HERE/'token-laws-check.json').read_text())
    phase('core17828',(tuple(map(int,r['sequence'])) for r in core['rows']))
    boundary=json.loads((HERE/'token-boundary-check.json').read_text())
    phase('boundary3064',(tuple(map(int,r['sequence'])) for r in boundary['rows']))
    closure=sorted(s for s in harness.closure([(0,0,2,1,0,2)],nmax=3,maxlen=24) if s[:2]==(0,0))
    phase('closure87976',closure)
    save();print('FINAL seconds',report['seconds'],flush=True)

if __name__=='__main__':main()
