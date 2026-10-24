"""Check finite-stem W bounds on the lower-depth candidate."""
import collections
import itertools
import json
from pathlib import Path
import harness
import std
import token_laws as L
import token_grammar24 as G
HERE=Path(__file__).resolve().parent

def main():
    refs=json.loads((HERE/'token-laws-check.json').read_text())['rows']
    standard={tuple(r['tokens']) for r in refs};counts=collections.Counter();neg=[]
    for ts in standard:
        if not G.accept(ts,True,True,True):neg.append(dict(tokens=ts,reason=G.explain(ts,True,True,True)))
    counts['reference_accept']=len(standard)-len(neg)
    false_positive=[];accepted=[]
    for size in range(1,7):
        for ts in itertools.product(L.TOK,repeat=size):
            pred=G.accept(ts,True,True,True);actual=ts in standard
            counts[('true' if actual else 'false')+('_accept' if pred else '_reject')]+=1
            if pred:accepted.append(ts)
            if pred and not actual:false_positive.append(dict(tokens=ts,sequence=L.seq(ts)))
    print(dict(counts),'false positives',false_positive[:5],flush=True)
    closure=collections.Counter();bad=[]
    for ts in accepted:
        if ts[-1]=='A0':continue
        for n in range(1,6):
            term=harness.fs(L.seq(ts),n)
            terminal=(0,) if ts[-1] in ('W','E1') else (0,1)
            try:child=G.parse(term[4:-len(terminal)])
            except ValueError:closure['parse_failure']+=1;continue
            okay=G.accept(child,True,True,True);closure['agree' if okay else 'DIFFER']+=1
            if not okay:
                bad.append(dict(tokens=ts,n=n,child_tokens=child,term=term,reason=G.explain(child,True,True,True),
                                parent_standard=ts in standard))
    print('closure',dict(closure),'first',bad[:5],flush=True)
    result=dict(counts=counts,false_negative=neg,false_positive=false_positive,
                closure_counts=closure,closure_failures=bad)
    (HERE/'token-grammar24-bounded.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')

if __name__=='__main__':main()
