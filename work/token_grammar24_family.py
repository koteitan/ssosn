"""Unboundedly delayed closure failure and held-out standard rewrites."""
import collections
import json
from pathlib import Path
import harness
import std
import token_laws as L
import token_grammar24 as G
HERE=Path(__file__).resolve().parent

def candidate(ts):return G.accept(tuple(ts),True,True,True)

def main():
    families=[];counts=collections.Counter()
    for r in list(range(33))+[100]:
        ts=('A2',)*r+('A1','W','A2','W');s=L.seq(ts)
        assert candidate(ts)
        tested=[]
        ns=range(1,r+4) if r<=32 else (r+1,r+2)
        for n in ns:
            expected=('A2',)*r+('A1','W')+('A2',)*n+('A0',)
            term=harness.fs(s,n)
            assert term==L.seq(expected)+(0,)
            okay=candidate(expected)
            assert okay==(n<=r+1)
            counts['child_pass' if okay else 'child_reject']+=1
            tested.append(dict(n=n,accepted=okay))
        ceiling=L.seq(('A2',)*(r+1));q=harness.Seq(ceiling,'new');c=q.cut()
        assert c==2
        g,b=ceiling[:c],ceiling[c:-1]+(ceiling[-1]-1,)
        enough=len(s)//len(b)+2;periodic_prefix=(g+b*enough)[:len(s)]
        assert periodic_prefix<s<ceiling
        result=dict(r=r,parent_tokens=ts,first_failing_n=r+2,tests=tested,
                    ceiling=ceiling,G=g,B=b,gap_prefix=periodic_prefix,
                    boundary_child_reason=G.explain(('A2',)*r+('A1','W')+('A2',)*(r+2)+('A0',),True,True,True))
        if r<=12:
            assert not std.is_standard(s) and std.is_standard(ceiling) and std.ceil(s)==ceiling
            prefix_standard=std.is_standard(L.seq(ts[:-1]))
            assert prefix_standard==(r>=1)
            result.update(parent_standard=False,ceiling_standard=True,greedy_ceiling_agree=True,
                          prefix_before_final_W_standard=prefix_standard)
        families.append(result)
    print('family',dict(counts),'r=0..32 and 100, all expected thresholds agree',flush=True)
    reference=json.loads((HERE/'token-laws-check.json').read_text())['rows']
    closure=collections.Counter();failures=[]
    for i,row in enumerate(reference,1):
        ts=tuple(row['tokens']);assert candidate(ts)
        if ts[-1]=='A0':continue
        for n in range(1,6):
            term=harness.fs(L.seq(ts),n)
            terminal=(0,) if ts[-1] in ('W','E1') else (0,1)
            child=G.parse(term[4:-len(terminal)])
            okay=candidate(child);closure['pass' if okay else 'FAIL']+=1
            if not okay:
                failures.append(dict(tokens=ts,n=n,child=child,reason=G.explain(child,True,True,True),
                                     child_standard=std.is_standard(L.seq(child))))
        if i%4000==0:print('reference rewrite',i,dict(closure),flush=True)
    # A direct check of the first-copy decrement identity, before standardness.
    import itertools
    onecopy=collections.Counter()
    for size in range(1,10):
        for tail in itertools.product(range(3),repeat=size):
            if tail[-1]==0:continue
            seq=(0,0)+tail
            assert harness.fs(seq,1)==seq[:-1]+(seq[-1]-1,)
            onecopy['agree']+=1
    report=dict(family_counts=counts,families=families,reference_closure=closure,
                reference_closure_failures=failures,one_copy_decrement=onecopy)
    (HERE/'token-grammar24-family.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print('reference closure',dict(closure),'failure examples',failures[:3],flush=True)
    print('one-copy decrement',dict(onecopy),flush=True)

if __name__=='__main__':main()
