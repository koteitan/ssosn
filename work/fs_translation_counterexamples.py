"""Exact FS-relation obstructions, with no new values or sup fitting."""
import json
import gzip
from pathlib import Path
import harness
import conj
import lift
import token_tree as T
from cut_structure import CutTree
from ordinal import ZERO,ONE,OMEGA,P,add,w,nat,fs,cmp
from token_targets import pretty

HERE=Path(__file__).resolve().parent
E0=P(ONE,ZERO)

def probe(s,N=5,K=12):
    x=T.value(s);structure=CutTree.build(s)
    terms=[]
    for n in range(1,N+1):
        raw=structure.repeat(n);y=T.value(raw)
        terms.append(dict(n=n,sequence=raw,value=y,rendered=pretty(y),below_parent=cmp(y,x)<0,
                          same_index_lower=cmp(fs(x,n),y)<=0,oracle_fs_agree=raw==harness.fs(s,n)))
    return dict(sequence=s,parent=x,parent_rendered=pretty(x),terms=terms,
                fundamental=[dict(k=k,value=fs(x,k),rendered=pretty(fs(x,k))) for k in range(1,K+1)])

def main():
    root=probe((0,0,2,1))
    binary=probe((0,0,1,0,1))
    s=(0,0,2,1)+T.A(1);strong=probe(s,N=12,K=14)
    alpha=P(ONE,add(E0,w(nat(2))))
    assert T.value(s)==alpha
    checks=[]
    for n in range(1,13):
        ybits=(0,) if n==1 else (1,0,0)*(n-2)+(1,0)
        inner=(2,1)+T.A(0)+(T.W+T.A(0))*(n-1)
        index=add(E0,add(OMEGA*(n-1),ONE))
        value=w(add(P(ONE,index),ONE))
        raw=CutTree.build(s).repeat(n)
        expected=(0,0)+inner+(0,1)
        assert lift.lift(ybits)==inner
        assert conj.v(ybits)==add(OMEGA*(n-1),ONE)
        assert raw==expected and T.value(raw)==value
        standard=P(ONE,add(E0,OMEGA*n))
        assert fs(alpha,n)==standard and cmp(value,standard)<0
        checks.append(dict(n=n,binary_preimage=ybits,term_rendered=pretty(value),standard_rendered=pretty(standard)))
    strong['all_n_family_finite_sanity_checks']=checks
    # Prefix-length dependence of the upper shift. Exact algebra is explained
    # separately; these are finite sanity checks of its closed formula.
    upper_family=[]
    for j in range(11):
        s=(0,0,2,1)+T.W*j+T.A(1)+T.W
        x=T.value(s);beta=E0 if j==0 else P(ONE,w(nat(j)))
        assert x==P(ONE,add(beta,w(OMEGA)))
        rows=[]
        for n in range(1,6):
            y=T.value(CutTree.build(s).repeat(n))
            expected=add(P(ONE,add(beta,add(w(nat(j+n+1)),ONE))),ONE)
            assert y==expected
            assert cmp(fs(x,n+j+1),y)<0 and cmp(y,fs(x,n+j+2))<0
            rows.append(dict(n=n,term=pretty(y),insufficient_upper=pretty(fs(x,n+j+1)),sufficient_upper=pretty(fs(x,n+j+2))))
        upper_family.append(dict(j=j,sequence=s,min_upper_shift=j+2,rows=rows))
    overflow=[]
    with gzip.open(HERE/'fs-translation-core17828.json.gz','rt') as stream:
        unresolved_upper=[r for r in json.load(stream) if r['min_upper_shift'] is None]
    for row in unresolved_upper:
        s=tuple(map(int,row['sequence']));x=T.value(s)
        ys=[T.value(CutTree.build(s).repeat(n)) for n in range(1,6)]
        shifts=[c for c in range(17) if all(cmp(y,fs(x,n+c))<=0 for n,y in enumerate(ys,1))]
        assert shifts and shifts[0]==9
        overflow.append(dict(sequence=s,min_upper_shift=shifts[0]))
    T.value_tree.cache_clear();T.body_tree.cache_clear();T.block_tree.cache_clear()
    T.CUT_COPY_ACTION_EXPERIMENT=True
    failure=probe(tuple(map(int,'0021020121012020201202')),N=5,K=12)
    T.CUT_COPY_ACTION_EXPERIMENT=False
    T.value_tree.cache_clear();T.body_tree.cache_clear();T.block_tree.cache_clear()
    report=dict(root0021=root,binary_exact_shift_obstruction=binary,lift_A1_all_n_obstruction=strong,
                upper_shift_family=upper_family,upper_overflow_followups=overflow,rejected_rule92=failure,
                scope='Closed-form identities are conditional on retaining the existing lift translation; no new parent value is fitted.')
    (HERE/'fs-translation-counterexamples.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print('known lift: lower bound fails for every n in closed family; finite checks n=1..12 OK',flush=True)
    print('upper family j=0..10 requires c=j+2; checks n=1..5 OK',flush=True)
    print('#92',failure['parent_rendered'],flush=True)
    for row in failure['terms']:print(row['n'],row['rendered'],row['below_parent'],flush=True)

if __name__=='__main__':main()
