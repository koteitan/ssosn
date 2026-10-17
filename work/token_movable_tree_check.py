"""Replay the exact §17 828 inputs with the movable-one experiment."""
import collections
import json
from pathlib import Path
import harness
import std
import token_tree as T
import token_movable as M
from ordinal import cmp
from token_targets import pretty

HERE=Path(__file__).resolve().parent

def main():
    source=json.loads((HERE/'token-tree-extended-check.json').read_text())
    inputs=source['rows']+[source['first_counterexample']]
    T.GENERAL_COPY_EXPERIMENT=True
    T.MOVABLE_ONE_EXPERIMENT=True
    values={};rows=[];counts=collections.Counter();first=None
    for number,row in enumerate(inputs,1):
        s=tuple(row['sequence'])
        try:
            parent=T.value(s)
            terms=[]
            for n in range(1,6):
                t=harness.fs(s,n);x=T.value(t)
                terms.append(dict(n=n,sequence=t,tokens=M.names(M.parse(t[4:])),ordinal=x,rendered=pretty(x),
                                  standard=std.is_standard(t),below_parent=cmp(x,parent)<0))
        except T.Unknown as exc:
            counts['unresolved']+=1;rows.append(dict(number=number,sequence=s,status='unresolved',reason=str(exc)))
            continue
        values[s]=parent
        for t in terms:values[t['sequence']]=t['ordinal']
        ordered=sorted(values)
        adjacent=[dict(left=a,right=b,left_rendered=pretty(values[a]),right_rendered=pretty(values[b]))
                  for a,b in zip(ordered,ordered[1:]) if cmp(values[a],values[b])>=0]
        local=all(t['below_parent'] for t in terms) and all(cmp(a['ordinal'],b['ordinal'])<0 for a,b in zip(terms,terms[1:]))
        result=dict(number=number,sequence=s,tokens=M.names(M.parse(s[4:])),status='pass' if local and not adjacent else 'counterexample',
                    parent=parent,parent_rendered=pretty(parent),terms=terms,adjacent_violations=adjacent)
        rows.append(result)
        if not local or adjacent:
            first=result;counts['counterexample']+=1
            cut=harness.Seq(s,'new').cut()
            g,b=s[:cut],s[cut:-1]+(s[-1]-1,)
            v=(0,1)
            h=terms[0]['sequence'][:-len(v)]
            q=terms[1]['sequence'][len(h):-len(v)]
            result.update(G=g,B=b,H=h,Q=q,V=v,
                          all_n_word_certificate=(g+b==h+v and v+b==q+v),
                          tree=T.dump(T.value_tree(s)),
                          term_trees=[T.dump(T.value_tree(t['sequence'])) for t in terms])
            print('FIRST COUNTEREXAMPLE',number,result['tokens'],pretty(parent),flush=True)
            for t in terms:print(t['n'],t['rendered'],t['below_parent'],flush=True)
            break
        counts['pass']+=1
        if number%200==0:print(number,dict(counts),flush=True)
    report=dict(input_count=len(inputs),counts=counts,first_counterexample=first,rows=rows,
                valued_sequences=len(values),stopped=first is not None)
    (HERE/'token-movable-tree-check.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print('FINAL',dict(counts),'values',len(values),'stopped',first is not None,flush=True)

if __name__=='__main__':main()
