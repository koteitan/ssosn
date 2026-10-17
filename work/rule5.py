"""rule3 + successor rule for self-referential blocks:
  u ⌢ (0,1,2) has value e_(ι+1) when u is a self-referential block of value e_ι.
This replaces ② on every block that ends in (0,1,2), so an override of u
propagates to u⌢(0,1,2)^m (rule3 alone needs one override per m)."""
import harness, conj, conj2, lower, rule3
import evalord as E
from ordinal import P, ONE, ZERO, add, nat, succ, show
V = rule3.V
HMEMO = {}


class _Memo(dict):
    """memo of R; clearing it also clears the hook memo (both depend on V)."""
    def clear(self):
        super().clear(); HMEMO.clear()


memo = _Memo()


def is_selfref(u):
    u = tuple(u)
    return bool(u) and u[0] == 2 and len(conj2.units(u)) == 1 and conj2.T(u) == u


def hook(u):
    u = tuple(u)
    if u in V: return V[u]
    if u not in HMEMO: HMEMO[u] = _hook(u)
    return HMEMO[u]


def _hook(u):
    if len(u) > 3 and u[-3:] == (0, 1, 2) and is_selfref(u[:-3]):
        x = hook(u[:-3])
        if x is not None and x[0][0] == 'p' and x[0][1] == ONE and len(x) == 1:
            return P(ONE, succ(x[0][2]))      # e_ι -> e_(ι+1)
    if EXTRA:
        x = extra(u)
        if x is not None: return x
    L = lower.lower(u)
    if L is None: return None
    x = R((0, 0) + L)
    return None if x is None else P(ONE, lower.minus2(x))


EXTRA = True
E0 = P(ONE, ZERO)


def index_of(u):
    """ι with hook(u) = e_ι, or None."""
    if not is_selfref(u): return None
    x = hook(u)
    if x is not None and len(x) == 1 and x[0][0] == 'p' and x[0][1] == ONE:
        return x[0][2]
    return None


def extra(u):
    """rules found on 2026-10-11 (data: Z_k, X_k, A, C_2, D families):
      u'⌢(0,1,2,0,1,2,1): ι -> ι+w          (ι limit; for ι successor the form is not standard)
      u'⌢(0,1,2,0,2):     β+w^m -> β+w^(m+1)  (m >= 1);  e0 -> e0+w^2
      u'⌢(0,1,2,1):       β+w^m -> β+w^(m+w)  (m >= 1, ι != e0)
      u'⌢(0,1,2)⌢(0,2)^k (k >= 2): sup of the real terms S[1..4] (recursion)"""
    from ordinal import w as wpow, OMEGA, is_limit
    if len(u) > 7 and u[-7:] == (0, 1, 2, 0, 1, 2, 1):
        i = index_of(u[:-7])
        if i is not None and is_limit(i): return P(ONE, add(i, OMEGA))
    if len(u) > 5 and u[-5:] == (0, 1, 2, 0, 2):
        i = index_of(u[:-5])
        if i is not None:
            if i == E0: return P(ONE, add(E0, wpow(nat(2))))
            t = i[-1]
            if t[1] == ZERO and t[2] != ZERO:
                return P(ONE, add(i[:-1], wpow(succ(t[2]))))
    k = 0
    while len(u) > 3 + 2 * (k + 1) and u[len(u) - 2 * (k + 1):len(u) - 2 * k] == (0, 2): k += 1
    if k >= 2 and u[len(u) - 2 * k - 3:len(u) - 2 * k] == (0, 1, 2):
        # u'⌢(0,1,2)⌢(0,2)^k, k >= 2: no closed rule yet; value = sup of the real terms
        S = (0, 0) + u
        xs = [R(harness.fs(S, n)) for n in (1, 2, 3, 4)]
        if all(x is not None for x in xs):
            s = E.sup(xs)
            if s is not None and E.check(s, xs, 3): return s
    if len(u) > 4 and u[-4:] == (0, 1, 2, 1) and u[-7:] != (0, 1, 2, 0, 1, 2, 1):
        # u'⌢(0,1,2,1) = sup_n u'⌢(0,1,2,0,2)^n:  β+w^m -> β+w^(m+w)  (not for ι = e0)
        i = index_of(u[:-4])
        if i is not None and i != E0:
            t = i[-1]
            if t[1] == ZERO and t[2] != ZERO:
                return P(ONE, add(i[:-1], wpow(add(t[2], OMEGA))))
    return None


def R(S):
    S = tuple(S)
    if S in memo: return memo[S]
    if S[:2] != (0, 0): r = None
    elif S[-1] == 0 and len(S) > 2: r = None if (x := R(S[:-1])) is None else succ(x)
    elif max(S, default=0) <= 1: r = conj.o(S)
    else:
        conj2.HOOK = hook
        if rule3.single_selfref(S):
            x = hook(S[2:])
        else:
            x = conj2.v(S[2:])
        r = None if x is None else add(nat(2), x)
    memo[S] = r
    return r


def iterate(Ss, rounds=300, NS=(1, 2, 3, 4, 5), K=3, log=True):
    """as rule3.iterate, with R = this module's R."""
    Ss = sorted(S for S in Ss if len(S) > 2 and S[-1] != 0 and rule3.single_selfref(S))
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
            V[S[2:]] = s
            memo.clear(); changed += 1
            break
        if not changed: break
    return V


VERIFIED = set()


def blocks_used(S, NS):
    """self-referential blocks whose hook value is needed by R(S[n]), n in NS."""
    seen = []
    global hook
    orig = hook

    def spy(u):
        seen.append(tuple(u))
        return orig(u)
    hook = spy
    memo.clear()
    try:
        for n in NS: R(harness.fs(S, n))
    finally:
        hook = orig
        memo.clear()
    out = []
    for u in seen:
        if u not in out and (0, 0) + u != tuple(S): out.append(u)
    return out


def verify(S, depth=2, NS=(1, 2, 3, 4), K=3, log=True, ind=''):
    """Re-check a single self-referential form S: first verify (depth-1) the blocks its
    terms use, then set V from the sup of its terms if R(S) fails the test.
    Blocks reached at depth 0 keep their current (② / V / successor) value."""
    S = tuple(S)
    if S in VERIFIED or depth < 0: return
    VERIFIED.add(S)
    if depth > 0:
        for u in blocks_used(S, NS):
            if (0, 0) + u not in VERIFIED and is_selfref(u):
                verify((0, 0) + u, depth - 1, NS, K, log, ind + '  ')
    memo.clear()
    r = R(S)
    xs = [R(harness.fs(S, n)) for n in NS]
    if any(x is None for x in xs): return
    if r is not None and E.check(r, xs, K): return
    s = E.sup(xs)
    if s is None or not E.check(s, xs, K):
        if log: print(ind + 'no sup for', ''.join(map(str, S)), [show(x) for x in xs[:3]])
        return
    if log: print(ind + 'set', ''.join(map(str, S)).ljust(24), (r and show(r)), '->', show(s))
    V[S[2:]] = s
    memo.clear()


def deps(roots, maxlen=40, NS=(1, 2, 3, 4), limit=5000):
    """all single self-referential forms reachable from roots through blocks_used,
    with length <= maxlen (the frontier keeps its current value)."""
    seen = set(); st = [tuple(S) for S in roots]
    while st and len(seen) < limit:
        S = st.pop()
        if S in seen or len(S) > maxlen: continue
        seen.add(S)
        for u in blocks_used(S, NS):
            if is_selfref(u) and (0, 0) + u not in seen: st.append((0, 0) + u)
    return seen


def bottom_up(roots, maxlen=40, NS=(1, 2, 3, 4), K=3, rounds=50, log=True):
    """check-and-fix every form of deps(roots) in lex order, repeated until stable."""
    D = sorted(deps(roots, maxlen, NS))
    if log: print('deps', len(D), 'forms, longest', max(map(len, D)))
    for it in range(rounds):
        changed = 0
        for S in D:
            memo.clear()
            r = R(S)
            xs = [R(harness.fs(S, n)) for n in NS]
            if any(x is None for x in xs): continue
            if r is not None and E.check(r, xs, K): continue
            s = E.sup(xs)
            if s is None or not E.check(s, xs, K): continue
            if log: print('  set', ''.join(map(str, S)).ljust(30), (r and show(r)), '->', show(s))
            V[S[2:]] = s; changed += 1
        memo.clear()
        if not changed: break
    return D
