"""Prerequisite copy words for the four upper roots; stop at first contradiction."""
import collections
import itertools
import json
from pathlib import Path
import harness
import std
import token_tree as T
from ordinal import cmp
from token_targets import pretty

HERE=Path(__file__).resolve().parent
ALPHABET=('A0','A1','A2','E1','W','D')


def raw(tokens):
    return sum(((0,2) if t=='D' else T.W if t=='W' else
                T.A(int(t[1:]))+((1,) if t.startswith('E') else ()) for t in tokens),())


def main():
    T.GENERAL_COPY_EXPERIMENT=True
    values={}
    counts=collections.Counter()
    rows=[]
    candidates=set()
    # The leading W/D words that occur in the previously unresolved roots.
    for size in range(1,7):
        candidates.update(itertools.product(('W','D'),repeat=size))
    # Canonical fresh-tail strings, now including D after E and W after D.
    frontier=[('D',)]
    for size in range(6):
        new=[]
        for prefix in frontier:
            for atom in ALPHABET:
                tokens=prefix+(atom,)
                s=(0,0,2,1)+raw(tokens)
                if T.parse(raw(tokens),True)!=tokens or not std.is_standard(s):continue
                new.append(tokens);candidates.add(tokens)
        frontier=new
    order={a:i for i,a in enumerate(ALPHABET)}
    for tokens in sorted(candidates,key=lambda ts:(len(ts),tuple(order[t] for t in ts))):
        s=(0,0,2,1)+raw(tokens)
        if not std.is_standard(s):continue
        try:
            parent=T.value(s)
            terms=[]
            for n in range(1,6):
                t=harness.fs(s,n);x=T.value(t)
                terms.append(dict(n=n,sequence=t,ordinal=x,rendered=pretty(x),below_parent=cmp(x,parent)<0))
        except T.Unknown as exc:
            counts['unresolved']+=1
            rows.append(dict(tokens=tokens,sequence=s,status='unresolved',reason=str(exc)))
            continue
        values[s]=parent
        for t in terms:values[t['sequence']]=t['ordinal']
        ordered=sorted(values)
        adjacent=[dict(left=a,right=b,left_value=values[a],right_value=values[b])
                  for a,b in zip(ordered,ordered[1:]) if cmp(values[a],values[b])>=0]
        local=all(t['below_parent'] for t in terms) and all(cmp(a['ordinal'],b['ordinal'])<0 for a,b in zip(terms,terms[1:]))
        if not local or adjacent:
            cut=harness.Seq(s,'new').cut()
            g,b=s[:cut],s[cut:-1]+(s[-1]-1,)
            for term in terms:
                term['standard']=std.is_standard(tuple(term['sequence']))
                if tuple(term['sequence'][-1:])==(0,):
                    term['tokens']=T.parse(tuple(term['sequence'][4:-1]),True)
                    term['terminal']=(0,)
            counter=dict(tokens=tokens,sequence=s,parent=parent,parent_rendered=pretty(parent),terms=terms,
                         kind='real_term_order' if not local else 'adjacent_order',
                         standard=std.is_standard(s),G=g,B=b,
                         adjacent_violations=adjacent,tree=T.dump(T.value_tree(s)))
            if tokens==('D','W','A0','W','D','W'):
                h=(0,0,2,1)+raw(tokens[:-1])
                q,v=T.A(1),T.A(0)+(0,)
                counter.update(H=h,Q=q,V=v,all_n_word_certificate=(g+b==h+v and v+b==q+v))
            (HERE/'token-tree-first-counterexample.json').write_text(json.dumps(counter,ensure_ascii=False,indent=2)+'\n')
            report=dict(counts=counts,first_counterexample=counter,rows=rows,stopped=True,
                        valued_sequences=len(values),counterexample_number=len(rows)+1)
            (HERE/'token-tree-extended-check.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
            print('FIRST COUNTEREXAMPLE',tokens,counter['kind'],pretty(parent),flush=True)
            for t in terms:print(t['n'],t['rendered'],t['below_parent'],flush=True)
            return
        counts['pass']+=1
        rows.append(dict(tokens=tokens,sequence=s,status='pass'))
        if counts['pass']%200==0:print(dict(counts),flush=True)
    report=dict(counts=counts,first_counterexample=None,rows=rows,stopped=False,valued_sequences=len(values))
    (HERE/'token-tree-extended-check.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print('FINAL',dict(counts),'order 0',flush=True)


if __name__=='__main__':main()
