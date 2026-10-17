"""Regression first, then stop at the first counterexample to the tree state."""
import collections
import csv
import gzip
import json
import time
from pathlib import Path
import harness
import token_tree as T
import token_value as Reference
import lift
import conj
from ordinal import cmp, P, ONE, add, show, succ
from token_targets import pretty
from token_boundary_check import components

HERE=Path(__file__).resolve().parent
OUT=HERE/'token-tree-check.json'


def freeze(x):
    return tuple(map(freeze,x)) if isinstance(x,list) else x


def order_audit(values):
    ordered=sorted(values)
    return [dict(left=a,right=b,left_value=values[a],right_value=values[b])
            for a,b in zip(ordered,ordered[1:]) if cmp(values[a],values[b])>=0]


def main():
    started=time.monotonic()
    report=dict(method='CNF trees with origin/depth/copy/frame; references used only by this checker',
                phases={},first_counterexample=None)

    def save():
        report['seconds']=time.monotonic()-started
        OUT.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')

    def compare_phase(name,items):
        counts=collections.Counter()
        changes=[]
        for i,(s,expected) in enumerate(items,1):
            try:
                x=T.value(s)
                status='agree' if cmp(x,expected)==0 else 'differ'
            except T.Unknown as exc:
                x=None;status='unresolved'
            counts[status]+=1
            if status!='agree':changes.append(dict(sequence=s,status=status,expected=expected,actual=x))
            if i%10000==0:print(name,i,dict(counts),flush=True)
        report['phases'][name]=dict(counts=counts,changes=changes)
        save()
        print(name,dict(counts),flush=True)
        if changes:raise RuntimeError('old regression failed: '+name)

    lift.unlift((2,1))
    compare_phase('lift5350',(((0,0)+u,P(ONE,add(Reference.E0,conj.v(y)))) for u,y in lift._INV.items()))

    syntax=json.loads((HERE/'token-laws-check.json').read_text())
    values={}
    counts=collections.Counter()
    failures=[]
    for i,row in enumerate(syntax['rows'],1):
        s=tuple(map(int,row['sequence']))
        parent=T.value(s)
        if cmp(parent,Reference.value(s))!=0:failures.append(dict(kind='changed',sequence=s))
        values[s]=parent
        xs=[]
        cut=harness.Seq(s,'new').cut()
        g,b=s[:cut],s[cut:-1]+(s[-1]-1,)
        for n in range(1,6):
            term=g+b*n
            x=T.value(term)
            values[term]=x
            xs.append(x)
        if all(cmp(x,parent)<0 for x in xs) and all(cmp(a,b)<0 for a,b in zip(xs,xs[1:])):
            counts['local_pass']+=1
        else:failures.append(dict(kind='local',sequence=s,parent=parent,terms=xs))
        if i%2000==0:print('core',i,'failures',len(failures),flush=True)
    violations=order_audit(values)
    report['phases']['core17828']=dict(counts=counts,failures=failures,valued_sequences=len(values),adjacent_violations=violations)
    save();print('core FINAL',counts,'fail',len(failures),'order',len(violations),flush=True)
    if failures or violations:raise RuntimeError('old core failed')
    del values

    closure=harness.closure([(0,0,2,1,0,2)],nmax=3,maxlen=24)
    closure=sorted(s for s in closure if s[:2]==(0,0))
    compare_phase('closure87976',((s,Reference.value(s)) for s in closure))

    old=json.loads((HERE/'toktable2-comparison.json').read_text())
    counts=collections.defaultdict(collections.Counter)
    for row in old['rows']:
        s=tuple(map(int,row['sequence']))
        x=T.value(s)
        if cmp(x,freeze(row['new']))!=0:raise RuntimeError('old table changed relative to current evaluator')
        counts[row['region']]['agree' if cmp(x,freeze(row['old']))==0 else 'differ']+=1
    report['phases']['old977']=dict(counts)
    save();print('old977',dict(counts),flush=True)

    # All known values from §16, including its new safe relative-tail rules.
    counts=collections.Counter()
    with gzip.open(HERE/'token-extension-values.tsv.gz','rt') as stream:
        for i,row in enumerate(csv.DictReader(stream,delimiter='\t'),1):
            x=T.value(tuple(map(int,row['sequence'])))
            counts['agree' if pretty(x)==row['value'] else 'differ']+=1
            if counts['differ']:raise RuntimeError('safe extension reference changed at '+row['sequence'])
            if i%20000==0:print('current',i,dict(counts),flush=True)
    report['phases']['current103434']=dict(counts)
    save()

    counts=collections.Counter()
    with gzip.open(HERE/'token-comparison-final-values.tsv.gz','rt') as stream:
        for i,row in enumerate(csv.DictReader(stream,delimiter='\t'),1):
            x=T.value(tuple(map(int,row['sequence'])))
            counts['agree' if show(x)==row['value'] else 'differ']+=1
            if counts['differ']:raise RuntimeError('historical reference changed at '+row['sequence'])
            if i%100000==0:print('historical',i,dict(counts),flush=True)
    report['phases']['historical870281']=dict(counts)
    save();print('all old checks passed',flush=True)

    source=json.loads((HERE/'token-boundary-check.json').read_text())
    values={}
    counts=collections.Counter()
    for row in source['rows']:
        tokens=tuple(row['tokens'])
        s=tuple(map(int,row['sequence']))
        parent=T.value(s)
        cut=harness.Seq(s,'new').cut()
        g,b=s[:cut],s[cut:-1]+(s[-1]-1,)
        h,q,v=components(tokens)
        terms=[]
        for n in range(1,6):
            term=g+b*n
            x=T.value(term)
            terms.append(dict(n=n,sequence=term,ordinal=x,rendered=pretty(x),
                              below_parent=cmp(x,parent)<0))
        local=all(t['below_parent'] for t in terms) and all(cmp(a['ordinal'],b['ordinal'])<0 for a,b in zip(terms,terms[1:]))
        values[s]=parent
        for t in terms:values[t['sequence']]=t['ordinal']
        adjacent=order_audit(values)
        counts['tested']+=1
        if not local or adjacent:
            result=dict(kind='real_term_order' if not local else 'adjacent_order',
                        enumeration='increasing token count, original A0/A1/A2/E1/W/D enumeration',
                        tokens=tokens,sequence=s,parent=parent,parent_rendered=pretty(parent),
                        terms=terms,all_n_law_certificate=(g+b==h+v and v+b==q+v),
                        G=g,B=b,H=h,Q=q,V=v,adjacent_violations=adjacent,
                        tree=T.dump(T.value_tree(s)))
            report['first_counterexample']=result
            report['phases']['new_region']=dict(counts=counts,stopped_on_first_counterexample=True,
                                                preceding_local_pass=counts['tested']-1,
                                                valued_sequences=len(values))
            save();print('FIRST COUNTEREXAMPLE',tokens,result['kind'],pretty(parent),flush=True)
            for t in terms:print(t['n'],t['rendered'],t['below_parent'],flush=True)
            return
        counts['local_pass']+=1
        if counts['tested']%200==0:print('new region',counts['tested'],'all pass',flush=True)
    report['phases']['new_region']=dict(counts=counts,stopped_on_first_counterexample=False,
                                       valued_sequences=len(values),adjacent_violations=[])
    save();print('new region ALL PASS',dict(counts),flush=True)


if __name__=='__main__':main()
