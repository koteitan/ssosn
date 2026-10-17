"""Valuation with taint tracking (2026-10-11 wave 2).

Self-referential block u (value e_ι):
  1. closed rules of rule5.extra (e0-based region), with u'⌢(0,1,2,1) only for u' ending in (0,2);
  2. otherwise the sup of the real terms R(S[n]), n = 1..4, S = (0,0)⌢u  (recursion, depth-limited);
  3. at the depth limit: ② (lower.lower) -- the result is TAINTED.
Only untainted values are memoized, so a value printed with taint 0 does not depend on ② at all.
"""
import harness, conj, conj2, lower, rule3
import evalord as E
from ordinal import P, ONE, ZERO, OMEGA, add, nat, succ, w as wpow, is_limit, show

MAXD = 6
NS = (1, 2, 3, 4)   # terms used for a real-term sup
MORE = False         # retry a failed sup with two more terms (only at depth <= MORE_DEPTH)
MORE_DEPTH = 2
E0 = P(ONE, ZERO)
memo = {}          # clean values of R
hmemo = {}         # clean values of hook
st = {'depth': 0, 'taint': 0}


def is_selfref(u):
    u = tuple(u)
    return bool(u) and u[0] == 2 and len(conj2.units(u)) == 1 and conj2.T(u) == u


def index_of(u):
    if not is_selfref(u): return None
    x = hook(u)
    if x is not None and len(x) == 1 and x[0][0] == 'p' and x[0][1] == ONE:
        return x[0][2]
    return None


USE_LIFT = False
NOREGION = False  # independent experiment; use fresh memo/hmemo when enabled
RELLIFT = False   # relative lift below omega^2; clear memo/hmemo when changing flags
NO_REGION_PREFIX = (2, 1, 0, 1, 2, 1, 0, 1, 2, 0, 2)


def relative_parts(u):
    """Maximal tail emit(Y) for canonical v(Y) = omega*m+n < omega^2.

    Such a tail is ((0,1,2,0,1,2,1)^m) followed by (0,1,2)^n.
    In particular an A1 opener, whose binary value is omega^2, is excluded.
    The base must be the first W base or lie in the NOREGION region.
    """
    p = tuple(u)
    n = m = 0
    while p[-3:] == (0, 1, 2):
        p = p[:-3]; n += 1
    while p[-7:] == (0, 1, 2, 0, 1, 2, 1):
        p = p[:-7]; m += 1
    if not (m or n): return None
    if p != (2, 1, 0, 1, 2, 1) and p[:len(NO_REGION_PREFIX)] != NO_REGION_PREFIX:
        return None
    return p, m, n


def relative_lift(u):
    """Conjectural additive lift with a strictly bounded emitted tail.

    The base value is evaluated separately, never inferred from this formula.
    The rule does not assert a value for the base itself or for an A1 boundary.
    """
    parts = relative_parts(u)
    if parts is None: return None
    p, m, n = parts
    i = index_of(p)
    if i is None: return None
    # The frozen data supports 4334 ordinary-tail bases and the first W base.
    # In particular it does not yet support B, whose index ends in epsilon_omega.
    if p != (2, 1, 0, 1, 2, 1) and (not i or i[-1][1] != ZERO):
        return None
    return P(ONE, add(i, add(OMEGA * m, nat(n))))


def rules(u):
    if RELLIFT:
        x = relative_lift(u)
        if x is not None: return x
    if NOREGION and tuple(u[:len(NO_REGION_PREFIX)]) == NO_REGION_PREFIX:
        return None
    if USE_LIFT:
        import lift, conj
        Y = lift.unlift(u)
        if Y is not None:
            return P(ONE, add(E0, conj.v(Y)))
    if len(u) > 3 and u[-3:] == (0, 1, 2) and is_selfref(u[:-3]):
        i = index_of(u[:-3])
        if i is not None: return P(ONE, succ(i))
    if len(u) > 7 and u[-7:] == (0, 1, 2, 0, 1, 2, 1):
        i = index_of(u[:-7])
        if i is not None and is_limit(i): return P(ONE, add(i, OMEGA))
    # general level rules (2026-10-11 wave 3): u = u'⌢(0,1,2)⌢(0,2)^k with level(u') >= k: op_k;
    # u = u'⌢(0,1,2,1) with level(u') = l >= 1: +w at depth l.  u' = (2,1) has level infinity.
    k = level(u)
    if k:
        up = u[:len(u) - 2 * k - 3]
        if up == (2, 1):
            t = nat(2)
            for _ in range(k - 1): t = wpow(t)
            return P(ONE, add(E0, wpow(t)))
        if is_selfref(up) and (k == 1 or lev(up) >= k):
            x = bump(index_of(up), k, ONE, ext_base(up))
            if x is not None: return P(ONE, x)
    if len(u) > 4 and u[-4:] == (0, 1, 2, 1) and u[-7:] != (0, 1, 2, 0, 1, 2, 1):
        up = u[:-4]
        l = lev(up)
        if 1 <= l < INF and is_selfref(up):
            x = bump(index_of(up), l, OMEGA, ext_base(up))
            if x is not None: return P(ONE, x)
    return None


INF = 10 ** 9


def lev(u):
    """level used by the rules: trailing (0,2)-count after (0,1,2); (2,1) is infinite;
    a block ending in (0,1,2,1) or (0,1,2,0,1,2,1) inherits the level of the part before it
    (except (2,1)⌢(0,1,2,0,1,2,1), level 0)."""
    u = tuple(u)
    k = level(u)
    if k: return k
    if u == (2, 1): return INF
    if ext_base(u): return INF
    if len(u) > 7 and u[-7:] == (0, 1, 2, 0, 1, 2, 1):
        return 0 if u[:-7] == (2, 1) else lev(u[:-7])
    if len(u) > 4 and u[-4:] == (0, 1, 2, 1): return lev(u[:-4])
    return 0


def level(u):
    """number of trailing (0,2) after the last (0,1,2) of u (0 if u does not end that way)."""
    u = tuple(u); k = 0
    while len(u) >= 2 * (k + 1) + 3 and u[len(u) - 2 * (k + 1):len(u) - 2 * k] == (0, 2): k += 1
    if k and u[len(u) - 2 * k - 3:len(u) - 2 * k] == (0, 1, 2): return k
    return 0


def exp_of_last(i):
    """g with i = β + w^g (last term of i a power of w, g >= 1), else None."""
    if i is None or not i or i == E0: return None
    t = i[-1]
    if t[1] == ZERO and t[2] != ZERO: return t[2]
    return None


EXT = False      # 2026-10-17 experiment: epsilon last terms e_x = w^(e_x); bases ending (0,2,1)
EXT121 = False   # independent experiment; clear memo/hmemo when changing flags
EXT121E = False  # narrower experiment: only bases whose index ends in an epsilon term


def ext_base(u):
    """Bases allowed to read a last epsilon term as w^(e_x).

    EXT121 and EXT121E are conjectural. EXT121E additionally requires an
    epsilon last term in the base index. The first W base (2,1,0,1,2,1) is a known
    counterexample and keeps its original rules and level.
    """
    u = tuple(u)
    if EXT and len(u) > 3 and u[-3:] == (0, 2, 1):
        return True
    if len(u) > 4 and u[-4:] == (0, 1, 2, 1) and u != (2, 1, 0, 1, 2, 1):
        if EXT121:
            return True
        if EXT121E:
            i = index_of(u)
            return i is not None and bool(i) and i[-1][1] != ZERO
    return False


def bump(x, d, a, eps=None):
    """add a to the exponent d levels down the last-term tower of x:
    d = 1: β + w^g -> β + w^(g+a);  d = 2: β + w^(γ + w^b) -> β + w^(γ + w^(b+a)); ...
    With EXT, an epsilon last term e_x is read as w^(e_x)."""
    if eps is None: eps = EXT
    if x is None or not x or (x == E0 and not eps): return None
    t = x[-1]
    if eps and t[1] != ZERO:
        e = (t,)
    elif t[1] != ZERO or t[2] == ZERO:
        return None
    else:
        e = t[2]
    e2 = add(e, a) if d == 1 else bump(e, d - 1, a, eps)
    if e2 is None: return None
    return add(x[:-1], wpow(e2))


def bump_last(g, a):
    """γ + w^b -> γ + w^(b+a) on the last term of g (None if the last term is not a power of w)."""
    if not g: return None
    t = g[-1]
    if t[1] != ZERO: return None
    return add(g[:-1], wpow(add(t[2], a)))


def mul_wpow(g, a):
    """g · w^a for g >= 1:  w^(log(lead g) + a)."""
    t = g[0]
    lg = t[2] if t[1] == ZERO else (t,)
    return wpow(add(lg, a))


def sup3(xs, K=3):
    """least sup candidate a with x_n < a and a[k] <= x_last for k <= K"""
    for a in sorted(E.sup_cands(xs), key=E._Key):
        if E.check(a, xs, K): return a
    return None


def hook(u):
    u = tuple(u)
    if u in hmemo: return hmemo[u]
    t0 = st['taint']
    x = rules(u)
    if x is None:
        if st['depth'] < MAXD:
            S = (0, 0) + u
            st['depth'] += 1
            try:
                xs = [R(harness.fs(S, n)) for n in NS]
                s = E.sup(xs) if all(y is not None for y in xs) else None
                if (s is None or not E.check(s, xs, 3)) and MORE and st['depth'] <= MORE_DEPTH:
                    # slowly growing indices: retry with two more terms, checking k <= 3 only
                    xs = xs + [R(harness.fs(S, n)) for n in (NS[-1] + 1, NS[-1] + 2)]
                    s = sup3(xs) if all(y is not None for y in xs) else None
            finally:
                st['depth'] -= 1
            if s is not None and E.check(s, xs, 3): x = s
        if x is None:                      # ② at the frontier
            st['taint'] += 1
            L = lower.lower(u)
            if L is not None:
                y = R((0, 0) + L)
                if y is not None: x = P(ONE, lower.minus2(y))
    if st['taint'] == t0: hmemo[u] = x
    return x


def R(S):
    S = tuple(S)
    if S in memo: return memo[S]
    t0 = st['taint']
    if S[:2] != (0, 0): r = None
    elif S[-1] == 0 and len(S) > 2: r = None if (x := R(S[:-1])) is None else succ(x)
    elif max(S, default=0) <= 1: r = conj.o(S)
    else:
        conj2.HOOK = hook
        x = hook(S[2:]) if rule3.single_selfref(S) else conj2.v(S[2:])
        r = None if x is None else add(nat(2), x)
    if st['taint'] == t0: memo[S] = r
    return r


def value(S, maxd=None):
    """(value, tainted?) of S at depth limit maxd."""
    global MAXD
    if maxd is not None:
        MAXD = maxd; memo.clear(); hmemo.clear()
    st['taint'] = 0; st['depth'] = 0
    r = R(S)
    return r, st['taint'] > 0


def real_sup(u):
    """sup of the real terms of (0,0)⌢u, ignoring the closed rules for u itself.
    returns (value, tainted?)."""
    S = (0, 0) + tuple(u)
    t0 = st['taint']
    st['depth'] += 1
    try:
        xs = [R(harness.fs(S, n)) for n in NS]
    finally:
        st['depth'] -= 1
    s = None
    if all(y is not None for y in xs):
        s = E.sup(xs)
        if s is not None and not E.check(s, xs, 3): s = None
    return s, st['taint'] > t0


def validate(Ss, log=True):
    """for every single self-referential S in Ss where a closed rule applies,
    compare the rule value with the clean sup of the real terms."""
    res = {'agree': 0, 'differ': [], 'tainted': 0, 'nosup': 0}
    for S in sorted(Ss):
        if len(S) < 3 or S[-1] == 0 or not rule3.single_selfref(S): continue
        u = S[2:]
        x = rules(u)
        if x is None: continue
        st['depth'] = 0
        s, tn = real_sup(u)
        if tn: res['tainted'] += 1; continue
        if s is None: res['nosup'] += 1; continue
        if s == x: res['agree'] += 1
        else:
            res['differ'].append(S)
            if log: print('  DIFFER', ''.join(map(str, S)).ljust(30), 'rule', show(x), 'real', show(s))
    return res
