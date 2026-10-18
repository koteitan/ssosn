"""Fresh-cut regression and first actual value-rule counterexample (§21)."""
import collections
import json
import time
from pathlib import Path
import harness
import lift
import conj
import token_tree as T
import token_value as Reference
import std
from cut_structure import CutTree
from ordinal import cmp,P,ONE,add
from token_targets import pretty

HERE=Path(__file__).resolve().parent

def freeze(x):return tuple(map(freeze,x)) if isinstance(x,list) else x

class Stop(Exception):pass

def main():
    T.CUT_COPY_ACTION_EXPERIMENT=True
    started=time.monotonic();report=dict(phases={},first_counterexample=None)
    def save():
        report['seconds']=time.monotonic()-started
        (HERE/'cut-value-check.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    def compare(name,items):
        counts=collections.Counter();changes=[]
        for s,ref in items:
            try:
                x=T.value(s);status='agree' if cmp(x,ref)==0 else 'differ'
            except T.Unknown as exc:x=None;status='unresolved'
            counts[status]+=1
            if status!='agree':changes.append(dict(sequence=s,status=status,actual=x,expected=ref))
        report['phases'][name]=dict(counts=counts,changes=changes);save()
        print(name,dict(counts),flush=True)
    def actual_phase(name,sequences,incremental=False):
        values={};counts=collections.Counter();last=None
        def audit():
            ordered=sorted(values)
            return [dict(left=a,right=b,left_rendered=pretty(values[a]),right_rendered=pretty(values[b]))
                    for a,b in zip(ordered,ordered[1:]) if cmp(values[a],values[b])>=0]
        for number,s in enumerate(sequences,1):
            s=tuple(s);structure=CutTree.build(s);trace=structure.locate()
            try:
                parent=T.value(s);terms=[]
                for n in range(1,6):
                    term=structure.repeat(n)
                    # Every term gets its own structure. No parent's sp tree
                    # or ranks are carried over to an appended copy.
                    child=CutTree.build(term)
                    x=T.value(term)
                    terms.append(dict(n=n,sequence=term,ordinal=x,rendered=pretty(x),
                                      below_parent=cmp(x,parent)<0,
                                      fresh_structure_cut=child.locate()['cut']))
            except T.Unknown as exc:
                counts['unresolved']+=1;continue
            values[s]=parent
            for term in terms:values[term['sequence']]=term['ordinal']
            local=all(t['below_parent'] for t in terms) and all(cmp(a['ordinal'],b['ordinal'])<0 for a,b in zip(terms,terms[1:]))
            adjacent=audit() if incremental or not local else []
            if not local or adjacent:
                for t in terms:t['standard']=std.is_standard(t['sequence'])
                result=dict(phase=name,number=number,sequence=s,parent=parent,parent_rendered=pretty(parent),
                            terms=terms,cut_trace=trace,adjacent_violations=adjacent,tree=T.dump(T.value_tree(s)),
                            kind='real_term_order' if not local else 'adjacent_order',standard=std.is_standard(s))
                c=trace['cut'];g=s[:c];b=s[c:-1]+(s[-1]-1,)
                result.update(G=g,B=b,oracle_cut_agree=harness.Seq(s,'new').cut()==c)
                if s[:4]==(0,0,2,1):
                    result['tokens']=T.parse(s[4:],True)
                if all(tuple(t['sequence'][-2:])==(0,1) for t in terms):
                    v=(0,1);h=terms[0]['sequence'][:-2];q=terms[1]['sequence'][len(h):-2]
                    result.update(H=h,Q=q,V=v,all_n_word_certificate=(g+b==h+v and v+b==q+v))
                    for t in terms:
                        t.update(tokens=T.parse(t['sequence'][4:-2],True),terminal=v,
                                 oracle_fs_agree=harness.fs(s,t['n'])==t['sequence'])
                if result.get('tokens')==('D','W','A2','A1'):
                    origin=T.Origin('counterexample copy diagnosis')
                    copies=T.fresh_copy_from_cut(('D','W','A2'),2)
                    result['rule_diagnosis']=dict(actual_copy=copies,
                        fresh_A2_seed=pretty(T.ordinal(T.plus(T.typed_copy_rank(copies,1,origin),T.one(origin),origin))),
                        opened_A0_copy_seed=pretty(T.ordinal(T.plus(T.typed_copy_rank(copies,0,origin),T.one(origin),origin))))
                report['first_counterexample']=result
                counts['counterexample']+=1
                report['phases'][name]=dict(counts=counts,valued_sequences=len(values),stopped=True)
                save();print('FIRST COUNTEREXAMPLE',name,number,s,pretty(parent),flush=True)
                for t in terms:print(t['n'],t['rendered'],t['below_parent'],flush=True)
                raise Stop
            counts['local_pass']+=1
            last=dict(sequence=s,parent_rendered=pretty(parent),terms=terms)
            if number%2000==0:print(name,number,dict(counts),flush=True)
        adjacent=audit()
        report['phases'][name]=dict(counts=counts,valued_sequences=len(values),adjacent_violations=adjacent,last=last)
        save();print(name,dict(counts),'values',len(values),'order',len(adjacent),flush=True)
        if adjacent:
            report['first_counterexample']=dict(phase=name,kind='adjacent_order',adjacent_violations=adjacent);save();raise Stop
    try:
        lift.unlift((2,1))
        compare('lift5350',(((0,0)+u,P(ONE,add(Reference.E0,conj.v(y)))) for u,y in lift._INV.items()))
        core=json.loads((HERE/'token-laws-check.json').read_text())
        compare('core17828_values',((tuple(map(int,r['sequence'])),Reference.value(tuple(map(int,r['sequence'])))) for r in core['rows']))
        actual_phase('core17828_terms',(tuple(map(int,r['sequence'])) for r in core['rows']))
        closure=sorted(s for s in harness.closure([(0,0,2,1,0,2)],nmax=3,maxlen=24) if s[:2]==(0,0))
        compare('closure87976',((s,Reference.value(s)) for s in closure))
        old=json.loads((HERE/'toktable2-comparison.json').read_text())
        compare('old_outside585',((tuple(map(int,r['sequence'])),freeze(r['old'])) for r in old['rows'] if r['region']=='outside'))
        boundary=json.loads((HERE/'token-boundary-check.json').read_text())
        actual_phase('boundary3064',(tuple(map(int,r['sequence'])) for r in boundary['rows']))
        source=json.loads((HERE/'token-tree-extended-check.json').read_text())
        actual_phase('extended828',(tuple(r['sequence']) for r in source['rows']+[source['first_counterexample']]),True)
        roots=['0021021','00211','0022','003']
        actual_phase('four_roots',(tuple(map(int,s)) for s in roots),True)
    except Stop:pass
    save();print('FINAL seconds',report['seconds'],'counterexample',report['first_counterexample'] is not None,flush=True)

if __name__=='__main__':main()
