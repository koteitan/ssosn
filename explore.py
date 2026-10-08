import sys, ssos
from ssos import fs
def closure(roots, nmax=3, maxlen=14):
    seen=set(); st=list(roots)
    while st:
        S=st.pop()
        if S in seen or len(S)>maxlen: continue
        seen.add(S)
        if not S: continue
        if S[-1]==0: st.append(S[:-1]); continue
        for n in range(1,nmax+1):
            st.append(fs(S,n))
    return seen
def check(Ss):
    bad=0
    for S in Ss:
        if S and S[-1]!=0:
            for n in (1,2,3):
                T=fs(S,n)
                if not T<S: bad+=1; print("NOT DECREASING",S,n,T)
    return bad
if __name__=="__main__":
    ssos.MBP=sys.argv[1]; ssos.CUT=sys.argv[2]
    top=tuple(int(x) for x in sys.argv[3].split(","))
    ml=int(sys.argv[4])
    Ss=sorted(closure([top],maxlen=ml))
    print(len(Ss),"sequences; bad",check(Ss))
    if len(sys.argv)>5:
        for S in Ss:
            if S and S[-1]!=0 and len(S)<=int(sys.argv[5]):
                print(S,"->",fs(S,1),fs(S,2),fs(S,3))
