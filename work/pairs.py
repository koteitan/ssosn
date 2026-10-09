import harness, rule3, util, lower
from ordinal import show, P, ONE
Ss = harness.closure([util.s2t('002102012101202102')], maxlen=21)
rule3.iterate(Ss, rounds=200, log=False)
idx = {}
for S in sorted(Ss, key=lambda s: (len(s), s)):
    r = rule3.R(S)
    if r is not None: idx.setdefault(show(r), S)
out = []
for S in sorted(Ss):
    if len(S) > 2 and S[-1] != 0 and rule3.single_selfref(S):
        r = rule3.R(S)
        if r is None: continue
        t = r[0]   # leading term (1, a, b) : e_b if a == ONE
        if len(r) != 1 or t[1] != ONE: continue
        iota = t[2]
        from ordinal import add, nat
        X = idx.get(show(add(nat(2), iota)))
        L = lower.lower(S[2:])
        out.append((S[2:], show(r), X and X[2:], L))
for u, v, X, L in out:
    mark = '' if X == L else ('   <-- ② ' + (util.t2s(L) if L else 'None'))
    print(util.t2s(u).ljust(22), v.ljust(20), 'X=', (util.t2s(X) if X is not None else '?'), mark)
