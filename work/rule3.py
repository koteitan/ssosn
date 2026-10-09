"""② with an override table V for self-referential blocks, filled by iteration:
when a single-block form S = (0,0)⌢u fails the sup test, set V[u] from the sup of its terms."""
import harness, conj, conj2, lower
import evalord as E
from ordinal import P, ONE, add, nat, succ, show, lt
V = {}
def hook(u):
    u = tuple(u)
    if u in V: return V[u]
    L = lower.lower(u)
    if L is None: return None
    x = R((0, 0) + L)
    return None if x is None else P(ONE, lower.minus2(x))
memo = {}
def single_selfref(S):
    us = conj2.units(S[2:])
    return len(us) == 1 and us[0] != (2,) and conj2.T(us[0]) == us[0]
def R(S):
    S = tuple(S)
    if S in memo: return memo[S]
    if S[:2] != (0, 0): r = None
    elif S[-1] == 0 and len(S) > 2: r = None if (x := R(S[:-1])) is None else succ(x)
    elif max(S, default=0) <= 1: r = conj.o(S)
    else:
        conj2.HOOK = hook
        if single_selfref(S):
            x = hook(S[2:]); r = None if x is None else add(nat(2), x)
        else:
            x = conj2.v(S[2:]); r = None if x is None else add(nat(2), x)
    memo[S] = r
    return r
def iterate(Ss, rounds=20, NS=(1, 2, 3, 4, 5), K=3, log=True):
    Ss = sorted(S for S in Ss if len(S) > 2 and S[-1] != 0 and S[:2] == (0, 0) and single_selfref(S))
    for it in range(rounds):
        changed = 0
        for S in Ss:
            r = R(S)
            xs = [R(harness.fs(S, n)) for n in NS]
            if any(x is None for x in xs): continue
            if r is not None and E.check(r, xs, K): continue
            s = E.sup(xs)
            if s is None or not E.check(s, xs, K):
                if log: print('  no sup for', ''.join(map(str, S)), [show(x) for x in xs[:3]])
                continue
            if log: print('  set', ''.join(map(str, S)).ljust(24), (r and show(r)), '->', show(s))
            V[S[2:]] = P(ONE, ZERO) if False else None
            # store block value: s = 2 + value, value = s for infinite s
            V[S[2:]] = s
            memo.clear(); changed += 1
            break   # restart from the smallest after each change
        if not changed: break
    return V
from ordinal import ZERO
