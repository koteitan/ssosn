"""Heuristic ill-foundedness detector for lex order on standard sequences.
For standard S = P ⌢ 0^k ⌢ (x) with x>0 and P not ending in 0, record k.
If for a fixed (P, x) k grows with the length bound, lex order has an
infinite descending chain P⌢0^k⌢x > P⌢0^(k+1)⌢x > ... among standard seqs."""
import sys, ssos
from explore import closure
from collections import defaultdict
ssos.MBP=sys.argv[1]; ssos.CUT=sys.argv[2]
top=tuple(int(x) for x in sys.argv[3].split(","))
for ml in map(int, sys.argv[4].split(",")):
    Ss=closure([top],nmax=3,maxlen=ml)
    fam=defaultdict(set)
    for S in Ss:
        if len(S)<2 or S[-1]==0: continue
        j=len(S)-1
        while j>0 and S[j-1]==0: j-=1
        k=len(S)-1-j
        if k>=1: fam[(S[:j],S[-1])].add(k)
    worst=sorted(fam.items(), key=lambda kv:-max(kv[1]))[:4]
    print("maxlen",ml,"#std",len(Ss)," largest gaps:",[(P,x,max(ks)) for (P,x),ks in worst])
