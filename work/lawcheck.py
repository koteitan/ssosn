"""check the syntactic expansion laws L_A, L_W, L_E on standard token strings after (2,1)"""
import sys
import os; _h = os.path.dirname(os.path.abspath(__file__)); sys.path[:0] = [_h, os.path.dirname(_h)]
import harness, std
from collections import Counter
def A(k): return (0,1,2) + (0,2) * k
W = (0,1,2,1)
def units(toks):
    """group tokens into units: (base, nW) where base is ('A',k) or ('E',k); leading root W's separate"""
    return toks
def seq(toks):
    s = (0,0,2,1)
    for t in toks:
        if t == 'W': s += W
        elif t[0] == 'A': s += A(int(t[1:]))
        elif t[0] == 'E': s += A(int(t[1:])) + (1,)
    return s
def expected(toks, n):
    j = 0
    while j < len(toks) and toks[j] == 'W': j += 1
    last = toks[-1]
    if last == 'W':
        if j == len(toks):                       # all W: W^(j) (E1 W^(j-1))^(n-1) A0 0
            jj = j - 1
            return seq(['W'] * jj + (['E1'] + ['W'] * jj) * (n - 1) + ['A0']) + (0,)
        i = len(toks) - 2                         # unit Z = last non-W token + its W's (before final W)
        while toks[i] == 'W': i -= 1
        if i < j: return None                     # unit would be a root W: not covered
        P, Z = toks[:i], toks[i:-1]
        return seq(P + Z * n + ['A0']) + (0,)
    if last[0] == 'E':
        k = int(last[1:])
        return seq(toks[:-1] + ['A%d' % (k + n - 1)]) + (0,)
    k = int(last[1:])
    if k == 0: return None
    T = toks[j:-1]; C = ['W'] * (j + 1); a = 'A%d' % (k - 1)
    return seq(['W'] * j + T + [a] + (C + T + [a]) * (n - 1)) + (0, 1)
TOK = ['A0', 'A1', 'A2', 'E1', 'W']
HI = (0,0,2,1,0,2)
stats = Counter(); bad = []
frontier = [[]]
for depth in range(int(sys.argv[1])):
    new = []
    for t in frontier:
        for k in TOK:
            u = t + [k]; S = seq(u)
            if S >= HI or not std.is_standard(S): continue
            new.append(u)
            ok = True; cov = True
            for n in range(1, 5):
                e = expected(u, n)
                if e is None: cov = False; break
                if harness.fs(S, n) != e: ok = False; break
            if not cov: stats['not covered'] += 1
            elif ok: stats['law holds'] += 1
            else: stats['law FAILS'] += 1; bad.append(' '.join(u))
    frontier = new
    print('depth', depth + 1, dict(stats), flush=True)
print("fails by last token:", Counter(b.split()[-1] for b in bad))
for b in bad[:30]: print("FAIL", b)
