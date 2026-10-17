"""Audit NOREGION or RELLIFT valuations, never importing old numeric values."""
import argparse
import csv
import gzip
import json
from pathlib import Path
import pickle
import sys

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE),str(HERE.parent)]
import harness
import std
import rule6
import evalord as E
from ordinal import cmp,succ
from order_region import pretty


def txt(s):return ''.join(map(str,s))


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--state',type=Path,required=True)
    ap.add_argument('--results',type=Path,required=True)
    ap.add_argument('--evaluation',type=Path,required=True)
    ap.add_argument('--primary-from',type=Path,
                    help='reuse only the sequence column of an earlier standard corpus')
    ap.add_argument('--superset',action='store_true',
                    help='audit all valued entries; zero violations then also holds for every standard subset')
    args=ap.parse_args()
    with args.state.open('rb') as f:state=pickle.load(f)
    assert state['signature'][0] in ('noregion-no-II-v1','rellift-no-II-v2')
    evaluation=json.loads(args.evaluation.read_text())
    assert evaluation['resolved']==sum(state['memo'].get(tuple(map(int,r['sequence']))) is not None
                                       for r in evaluation['rows'])
    p=(0,0)+rule6.NO_REGION_PREFIX
    derived={}
    def cached(s):
        if s in state['memo']:return state['memo'][s]
        base=s;zeros=0
        while len(base)>2 and base[-1]==0:base=base[:-1];zeros+=1
        value=state['memo'].get(base)
        if value is None:return None
        for _ in range(zeros):value=succ(value)
        if zeros:derived[s]=value
        return value
    for row in evaluation['rows']:
        if row['ordinal'] is not None:
            s=tuple(map(int,row['sequence']))
            for n in range(1,6):cached(harness.fs(s,n))
    rows={}
    for s,x in state['memo'].items():
        if s[:len(p)]==p:rows.setdefault(s,{})['R']=x
    for u,x in state['hmemo'].items():
        s=(0,0)+u
        if s[:len(p)]==p:rows.setdefault(s,{})['hook']=x
    for s,x in derived.items():
        if s[:len(p)]==p:rows.setdefault(s,{})['successor']=x
    # Use the previously cross-checked descending-target membership algorithm.
    top=std.TOP
    standard=set()
    if args.superset:standard.update(rows)
    for s in ([] if args.superset else sorted(rows,reverse=True)):
        for _ in range(100000):
            if s==top:standard.add(s);break
            assert top>s
            if top[-1]==0:
                new=top[:-1]
                if new<s:break
            else:
                c=harness.Seq(top,'new').cut();g,b=top[:c],top[c:-1]+(top[-1]-1,)
                if std.above_all_terms(g,b,s):break
                lo,hi=1,len(s)//len(b)+2
                while lo<hi:
                    mid=(lo+hi)//2
                    if g+b*mid>=s:hi=mid
                    else:lo=mid+1
                new=g+b*lo
            top=new
        else:raise RuntimeError('membership cap')
    ordered=sorted(standard)
    if not args.superset:
        for s in ordered[::max(1,len(ordered)//30)]:assert std.is_standard(s)
    violations=[]
    for left,right in zip(ordered,ordered[1:]):
        x=max(rows[left].values(),key=E._Key);y=min(rows[right].values(),key=E._Key)
        if cmp(x,y)>=0:
            violations.append({'left':txt(left),'left_ordinal':x,'right':txt(right),'right_ordinal':y})
    conflicts=[txt(s) for s in ordered if len(set(rows[s].values()))>1]
    term_checks=[]
    focused=[]
    for row in evaluation['rows']:
        if row['ordinal'] is None:continue
        s=tuple(map(int,row['sequence']));root=state['memo'][s]
        for n in range(1,6):
            t=harness.fs(s,n);x=cached(t)
            if x is not None and cmp(x,root)>=0:
                term_checks.append({'root':txt(s),'n':n,'term':txt(t),'ordinal':x,'root_ordinal':root})
    for text in ('0021012101202','00210121012020121','002101210120201210121','002101210120202'):
        s=tuple(map(int,text));xs=[];terms=[]
        for n in range(1,6):
            t=harness.fs(s,n);x=cached(t);xs.append(x)
            terms.append({'n':n,'sequence':txt(t),'ordinal':x})
        focused.append({'sequence':text,'ordinal':state['memo'].get(s),'terms':terms,
                        'sup4':E.sup(xs[:4]) if all(x is not None for x in xs[:4]) else None,
                        'sup5':E.sup(xs) if all(x is not None for x in xs) else None})
    report={'signature':state['signature'],'all_valued_region':len(rows),
            'membership_filter_applied':not args.superset,
            'checked_region_sequences':len(ordered),
            'standard_valued_region':len(standard) if not args.superset else None,
            'nonstandard_region':len(rows)-len(standard) if not args.superset else None,
            'adjacent_violations':violations,'same_sequence_conflicts':conflicts,
            'term_decrease_violations':term_checks,'focused':focused,
            'corpus_resolved':evaluation['resolved'],'corpus_unresolved':evaluation['unresolved'],
            'derived_successors':len(derived)}
    if args.primary_from:
        with args.primary_from.open() as f:
            primary={tuple(map(int,r['sequence'])) for r in csv.DictReader(f,delimiter='\t')}
        known=sorted(s for s in primary if s in rows)
        bad=[]
        for left,right in zip(known,known[1:]):
            x=max(rows[left].values(),key=E._Key);y=min(rows[right].values(),key=E._Key)
            if cmp(x,y)>=0:bad.append({'left':txt(left),'right':txt(right),'left_value':x,'right_value':y})
        report['primary_11_8']={'total':len(primary),'resolved':len(known),
                                'unresolved':len(primary)-len(known),'adjacent_violations':bad}
    args.results.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    with gzip.open(args.results.with_suffix('.tsv.gz'),'wt') as f:
        w=csv.writer(f,delimiter='\t');w.writerow(('sequence','source','value'))
        for s in ordered:
            for source,x in rows[s].items():w.writerow((txt(s),source,pretty(x)))
    print('audit fresh checked',len(ordered),'adjacent violations',len(violations),
          'same sequence conflicts',len(conflicts),'term violations',len(term_checks))


if __name__=='__main__':main()
