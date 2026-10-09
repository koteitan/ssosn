import harness, rule3, util, std
from ordinal import show, add, nat, ONE
F = {0: (0, 1, 2), 1: (0, 2), 2: (1,)}
def f(Y): return tuple(x for y in Y for x in F[y])
def rho(Y): return std.ceil((0, 0, 2) + f(Y))
Ss = harness.closure([util.s2t('002102012101202102')], maxlen=21)
rule3.iterate(Ss, rounds=200, log=False)
idx = {}
for S in sorted(Ss, key=lambda s: (len(s), s)):
    r = rule3.R(S)
    if r is not None: idx.setdefault(show(r), S)
good = bad = 0
for S in sorted(Ss):
    if len(S) > 2 and S[-1] != 0 and rule3.single_selfref(S):
        r = rule3.R(S)
        if r is None or len(r) != 1 or r[0][1] != ONE: continue
        X = idx.get(show(add(nat(2), r[0][2])))
        if X is None: continue
        u = rho(X[2:])
        if u == S: good += 1
        else:
            bad += 1
            if bad <= 25: print('MISMATCH Y=', util.t2s(X[2:]).ljust(14), 'truth', util.t2s(S).ljust(22), 'ceil(f)', util.t2s(u), show(r))
print('good', good, 'bad', bad)
