"""Standard <=> value is new (2026-10-24, Claude).

For every word Q⌢t with Q standard (token words after (0,0,2,1), below (0,0,2,1,0,2)), compare
V(Q⌢t) = token_value.index with the values of all enumerated standard words: the word passes when
its value is above every lexicographically smaller standard word and below every larger one.
Prints (standard, passes) counts and, for non-standard words, which side catches them.
usage: python3 work/value_monotone_check.py N A0,A1,...,E1,W
"""
import sys, collections
sys.path[:0]=['/home/koteitan/proofs/ssosn/work','/home/koteitan/proofs/ssosn']
import token_laws as L, std, token_value as TV
from ordinal import cmp, show
P=(0,0,2,1,0,2); toks=sys.argv[2].split(',')
N=int(sys.argv[1])
stdl=[()]; frontier=[()]; cand=[]
for n in range(1,N+1):
    new=[]
    for S in frontier:
        for t in toks:
            T=S+(t,)
            if L.seq(T)>=P: continue
            st=std.is_standard(L.seq(T)); cand.append((T,st))
            if st: new.append(T)
    frontier=new; stdl+=new
def V(ts):
    try: return TV.index(tuple(ts))
    except Exception: return None
stds=[(L.seq(T),V(T)) for T in stdl if T]
stds.sort()
res=collections.Counter(); ex=collections.defaultdict(list)
import bisect
keys=[s for s,_ in stds]
for T,st in cand:
    s=L.seq(T); v=V(T)
    if v is None: res[(st,'UNK')]+=1; continue
    i=bisect.bisect_left(keys,s)
    lower=[x for k,x in stds[:i] if x is not None and k!=s]
    upper=[x for k,x in stds[i:] if x is not None and k!=s]
    lo=all(cmp(x,v)<0 for x in lower); up=all(cmp(v,x)<0 for x in upper)
    ok=lo and up
    if not st: res[('side', lo, up)]+=1
    res[(st,ok)]+=1
    if st!=ok and len(ex[(st,ok)])<10: ex[(st,ok)].append((' '.join(T),show(v)))
print(dict(res))
for k,v in ex.items(): print(k); [print('   ',a) for a in v]
