"""Assumption ② as a pure (non-recursive) valuation."""
import harness, conj, conj2, lower
from ordinal import P, ONE, add, nat, succ
def hook(u):
    L = lower.lower(u)
    if L is None: return None
    x = R((0, 0) + L)
    return None if x is None else P(ONE, lower.minus2(x))
memo = {}
def R(S):
    S = tuple(S)
    if S in memo: return memo[S]
    if S[:2] != (0, 0): r = None
    elif S[-1] == 0 and len(S) > 2: r = None if (x := R(S[:-1])) is None else succ(x)
    elif max(S, default=0) <= 1: r = conj.o(S)
    else:
        conj2.HOOK = hook
        us = conj2.units(S[2:])
        x = conj2.v(S[2:]) if S[:2] == (0, 0) else None
        r = None if x is None else add(nat(2), x)
    memo[S] = r
    return r
