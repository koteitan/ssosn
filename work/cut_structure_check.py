"""Exhaustive definition-derived cut check, then fixed-subtree stability test."""
import argparse
import collections
import itertools
import json
from pathlib import Path
import harness
import std
from cut_structure import CutTree

HERE=Path(__file__).resolve().parent

def check(s):
    t=CutTree.build(s);oracle=harness.Seq(s,'new');trace=t.locate()
    errors=[]
    if any(t.parent[p]!=oracle.sp(p) for p in range(1,len(s)+1)):errors.append('sp')
    if any(t.record[p]!=oracle.mbp(p) for p in range(1,len(s)+1)):errors.append('mbp')
    if trace['br']!=oracle.br():errors.append('br')
    if trace['cut']!=oracle.cut():errors.append('cut')
    if trace['parents']!=[oracle.p(i) for i in range(1,oracle.br()+1)]:errors.append('p_path')
    return t,trace,errors

def main():
    ap=argparse.ArgumentParser();ap.add_argument('L',type=int,nargs='?',default=12);args=ap.parse_args()
    counts=collections.Counter();rows=[];levels=[];standards=[]
    for length in range(2,args.L+1):
        local=collections.Counter()
        for tail in itertools.product(range(3),repeat=length-2):
            s=(0,0)+tail
            tree,trace,errors=check(s)
            counts['all_sequences']+=1
            counts['all_positive_ended' if s[-1] else 'all_zero_ended']+=1
            if errors:
                failure=dict(sequence=s,errors=errors,trace=trace)
                (HERE/'cut-structure-check.json').write_text(json.dumps(dict(counts=counts,first_counterexample=failure),indent=2)+'\n')
                print('FIRST EXACT CUT COUNTEREXAMPLE',failure,flush=True);return
            local['all_agree']+=1
            if not std.is_standard(s):continue
            if s[-1]:standards.append(s)
            local['standard']+=1;counts['standard']+=1
            counts['standard_limit' if s[-1] else 'standard_successor']+=1
            counts['br_'+str(trace['br'])]+=1
            rows.append(dict(sequence=s,sp_parents=tree.parent[1:],suffix_ranks=tree.suffix_rank[1:],**trace))
        levels.append(dict(length=length,**local));print('CUT',levels[-1],flush=True)
    report=dict(max_length=args.L,counts=counts,levels=levels,rows=rows,cut_failures=0)
    (HERE/'cut-structure-check.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print('CUT FINAL',dict(counts),'failures 0',flush=True)
    # A fixed subtree copied by appending another B would retain the parent
    # edges of all previously present positions. Test this additional claim
    # separately: it is not needed for the exact record-maximum cut above.
    tried=0
    for s in standards:
        original=CutTree.build(s);trace=original.locate();c=trace['cut']
        g=s[:c];b=s[c:-1]+(s[-1]-1,)
        previous=CutTree.build(g+b)
        for n in range(2,6):
            current=CutTree.build(g+b*n)
            changed=[dict(position=p,old_parent=previous.parent[p],new_parent=current.parent[p])
                     for p in range(1,len(previous.sequence)+1) if previous.parent[p]!=current.parent[p]]
            if changed:
                failure=dict(parent=s,cut=c,G=g,B=b,n=n,
                    old_sequence=previous.sequence,new_sequence=current.sequence,
                    old_parents=previous.parent[1:],new_parents=current.parent[1:],changed=changed,
                    parent_standard=True,old_standard=std.is_standard(previous.sequence),new_standard=std.is_standard(current.sequence),
                    old_suffix_ranks=previous.suffix_rank[1:],new_suffix_ranks=current.suffix_rank[1:])
                report['fixed_subtree']=dict(tested_parents=tried+1,first_counterexample=failure,stopped=True)
                (HERE/'cut-structure-check.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
                print('FIRST FIXED SUBTREE COUNTEREXAMPLE',failure,flush=True);return
            previous=current
        tried+=1
    report['fixed_subtree']=dict(tested_parents=tried,first_counterexample=None,stopped=False)
    (HERE/'cut-structure-check.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print('FIXED SUBTREE PASS',tried,flush=True)

if __name__=='__main__':main()
