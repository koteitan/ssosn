"""Compare the value-free grammar with standardness and core rewrite closure."""
import collections
import itertools
import json
from pathlib import Path
import harness
import std
import token_laws as L
import token_grammar24 as G

HERE=Path(__file__).resolve().parent
ALPHABET=('A0','A1','A2','E1','W')

def main():
    reference=json.loads((HERE/'token-laws-check.json').read_text())
    counts=collections.Counter();false_negative=[]
    for row in reference['rows']:
        ts=tuple(row['tokens']);okay=G.accept(ts)
        counts['reference_accept' if okay else 'reference_REJECT']+=1
        if not okay:false_negative.append(dict(tokens=ts,sequence=L.seq(ts),reason=G.explain(ts)))
    print('reference',dict(counts),'first false negatives',false_negative[:5],flush=True)
    fullcounts=collections.Counter();false_positive=[];full_negative=[];accepted=[]
    for size in range(1,7):
        for ts in itertools.product(ALPHABET,repeat=size):
            s=L.seq(ts);pred=G.accept(ts);actual=std.is_standard(s)
            fullcounts[('true' if actual else 'false')+('_accept' if pred else '_reject')]+=1
            if pred:accepted.append(ts)
            if pred and not actual:false_positive.append(dict(tokens=ts,sequence=s))
            if actual and not pred:full_negative.append(dict(tokens=ts,sequence=s,reason=G.explain(ts)))
        print('all words size',size,dict(fullcounts),flush=True)
    # Reduced core rewrites remove only the terminal 0 or terminal 01.
    closurecounts=collections.Counter();closure_failures=[]
    for ts in accepted:
        if ts[-1]=='A0':continue
        for n in range(1,6):
            term=harness.fs(L.seq(ts),n)
            terminal=(0,) if ts[-1] in ('W','E1') else (0,1)
            try:child=G.parse(term[4:-len(terminal)])
            except ValueError:
                closurecounts['parse_failure']+=1;continue
            okay=G.accept(child);closurecounts['agree' if okay else 'DIFFER']+=1
            if not okay and len(closure_failures)<100:
                closure_failures.append(dict(tokens=ts,n=n,child_tokens=child,term=term,reason=G.explain(child),
                                             parent_standard=std.is_standard(L.seq(ts))))
    report=dict(reference_counts=counts,false_negative=false_negative,full_max_tokens=6,full_counts=fullcounts,
                false_positive=false_positive,full_false_negative=full_negative,
                closure_counts=closurecounts,closure_failures=closure_failures)
    (HERE/'token-grammar24-check.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print('closure',dict(closurecounts),'first',closure_failures[:5],flush=True)

if __name__=='__main__':main()
