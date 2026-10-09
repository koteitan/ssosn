"""Consistency harness: a candidate valuation R must satisfy, on standard forms,
R(S) = R(S[:-1]) + 1 if S ends in 0, and R(S) = sup_n R(S[n]) otherwise."""
import sys, os
sys.path[:0] = [os.path.dirname(os.path.abspath(__file__)), os.path.dirname(os.path.dirname(os.path.abspath(__file__)))]
os.chdir(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.setrecursionlimit(100000)
import evalord as E
from ordinal import show, succ, lt, cmp
ns = {}; exec(compile(open('ssosn').read(), 'ssosn', 'exec'), ns)
Seq = ns['Seq']
def fs(S, n):
    S = tuple(S)
    c = Seq(S, 'new').cut()
    return S[:c] + (S[c:-1] + (S[-1] - 1,)) * n

def closure(roots, nmax=3, maxlen=14):
    seen = set(); st = list(roots)
    while st:
        S = st.pop()
        if S in seen or len(S) > maxlen: continue
        seen.add(S)
        if not S: continue
        if S[-1] == 0: st.append(S[:-1]); continue
        for n in range(1, nmax + 1): st.append(fs(S, n))
    return seen

def check(R, Ss, NS=(1, 2, 3, 4, 5), K=3, verbose=True, limit=30):
    bad = []
    for S in sorted(Ss):
        if len(S) < 3 or S[-1] == 0: continue
        r = R(S)
        if r is None: continue
        xs = [R(fs(S, n)) for n in NS]
        if any(x is None for x in xs): continue
        if not E.check(r, xs, K):
            bad.append((S, r, xs, E.sup(xs)))
    if verbose:
        for S, r, xs, s in bad[:limit]:
            print(''.join(map(str, S)).ljust(28), show(r).ljust(22), 'sup', s and show(s), '|', ', '.join(show(x) for x in xs[:3]))
        print(len(bad), 'bad')
    return bad

def order_check(R, Ss, verbose=True):
    L = [(S, R(S)) for S in sorted(Ss)]
    L = [(S, r) for S, r in L if r is not None]
    bad = [(a, b) for a, b in zip(L, L[1:]) if not lt(a[1], b[1])]
    if verbose:
        for (S, r), (T, q) in bad[:20]:
            print('ORDER', ''.join(map(str, S)), show(r), '>=', ''.join(map(str, T)), show(q))
        print(len(bad), 'order violations among', len(L))
    return bad
