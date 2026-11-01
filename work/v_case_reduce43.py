"""§43 (Claude): case split of the v2 sup lemma on all limit copy words (bounded check, not a proof).

For each limit copy word (same input as v_unit_shapes43) the class R1/R2/R3 and copy start s come
from matching real terms. Cases: last block reduced by T/T2 to the same rule (shift d);
R3 starting at a lone 0 unit = R2 on the last block; R1 base (lone final 2 removed by T2);
trailing-zero additive copies. Run: timeout 600 python3 work/v_case_reduce43.py
"""
import sys, os
sys.path[:0]=[os.path.dirname(os.path.abspath(__file__)), os.path.dirname(os.path.dirname(os.path.abspath(__file__)))]
os.chdir(os.path.dirname(os.path.abspath(__file__)))
from collections import Counter
import v_unit_shapes43 as S, conj2, v_bits43 as vb
from v_inequality43 import words_u

def rule(y, cls, s, n):
    y=tuple(y)
    if cls=='R1': return y[:-1]+(1,)*(n+1)
    if cls=='R2': a=y[:-1]; return a+((0,)+a)*(n-1)
    h,q=y[:s],y[s+1:-1]; return h+((0,)+q)*n

def red(u):
    t=conj2.T(u)
    if t!=u: return 'T',t
    try: return 'T2',vb.T2(u)
    except ValueError: return 'X',None

words=set()
for core in words_u(S.MAX_TOKENS):
    if core[-1] not in S.LIMITS: continue
    for prefix in S.PREFIXES:
        words.add(prefix+core)
C=Counter(); ex={}
for w in sorted(words,key=lambda w:(len(w),w)):
    real=[S.real_copy_word(w,n) if hasattr(S,'real_copy_word') else None for n in (1,2,3)]
    m=S.match_classes(w,real)
    r3=[p for c,p in m if c=='R3']
    cls,pos=('R3',max(r3)) if r3 else m[0]
    y=vb.bits(w)
    if cls=='R1': s=max(i for i,b in enumerate(y) if b==2)
    elif cls=='R2': s=0
    else: s=len(vb.bits(w[:pos]))
    # bit rule must reproduce real bits
    ok=all(rule(y,cls,s,n)==vb.bits(real[n-1]) for n in (1,2,3))
    if not ok: C['bitrule_mismatch']+=1; ex.setdefault('bitrule_mismatch',w); continue
    units,spans=S.unit_spans(y)
    j=next(i for i,(lo,hi) in enumerate(spans) if lo<=s<hi)
    lo=spans[j][0]
    last=(j==len(units)-1)
    tz = (cls=='R2' and y[-2:-1]==(0,)) or (cls=='R3' and (s+1==len(y)-1 or y[-2]==0))
    key=(cls, 'last' if last else 'notlast', 'tz' if tz else 'pos')
    if last and not tz:
        u=tuple(y[lo:]); us=s-lo
        kind,tu=red(u)
        if kind=='X': C[key+('noreduce',)]+=1; ex.setdefault(key+('noreduce',),w); continue
        # find same-class instance on tu reproducing reduced terms with shift d
        terms=[red(tuple(rule(y,cls,s,n)[lo:]))[1] for n in (1,2,3,4)]
        found=None
        for cls2 in ('R1','R2','R3'):
            for s2 in range(len(tu)):
                for d in (-1,0,1):
                    try:
                        if all(n+d>=1 and rule(tu,cls2,s2,n+d)==terms[n-1] for n in (2,3,4)):
                            found=(cls2,d); break
                    except Exception: pass
                if found: break
            if found: break
        k=key+(kind, 'same' if found and found[0]==cls else ('other:'+found[0] if found else 'none'), found[1] if found else None)
        C[k]+=1; ex.setdefault(k,w)
    elif not last and not tz:
        # last block of y vs last blocks of terms
        ulo=spans[-1][0]; u=tuple(y[ulo:])
        tl=[]
        for n in (1,2,3,4):
            yn=rule(y,cls,s,n); un,sp=S.unit_spans(yn)
            tl.append((tuple(yn[:sp[-1][0]])==tuple(y[:ulo]) or tuple(yn[:ulo])==tuple(y[:ulo]), tuple(yn[ulo:])))
        found=None
        if all(a for a,_ in tl):
            for cls2 in ('R1','R2','R3'):
                for s2 in range(len(u)):
                    for d in (-1,0,1):
                        try:
                            if all(n+d>=1 and rule(u,cls2,s2,n+d)==tl[n-1][1] for n in (2,3,4)):
                                found=(cls2,s2,d); break
                        except Exception: pass
                    if found: break
                if found: break
        k=key+('lastblock', found[0] if found else 'none')
        C[k]+=1; ex.setdefault(k,w)
    else:
        C[key]+=1; ex.setdefault(key,w)
for k,v in sorted(C.items(),key=lambda x:-x[1]): print(v,k,''.join(ex.get(k,'')))
