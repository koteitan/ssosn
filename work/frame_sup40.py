"""Conservative frame candidate for a three-term tower progression.

This is experimental.  It recognizes a single position in an ordinal CNF
tree at which each consecutive term applies the same principal operation.
It never extrapolates from just two known terms.
"""

import evalord
from ordinal import ONE, ZERO, P, add, cmp, fs, is_limit, nat, w


def _single_step(a, b, path=()):
    if a == b:
        return None
    if b == w(a):
        return path, 'omega', a, b
    if b == P(ONE, a):
        return path, 'epsilon', a, b
    if len(a) != len(b):
        return None
    differing = [i for i, (x, y) in enumerate(zip(a, b)) if x != y]
    if len(differing) != 1:
        return None
    i = differing[0]
    x, y = a[i], b[i]
    if x[1] == y[1]:
        return _single_step(x[2], y[2], path + (('arg', i),))
    if x[2] == y[2]:
        return _single_step(x[1], y[1], path + (('level', i),))
    return None


def _replace_limit(tree, path, value):
    if not path:
        return value
    kind, i = path[0]
    old = tree[i]
    if kind == 'arg':
        new = P(old[1], _replace_limit(old[2], path[1:], value))
    else:
        new = P(_replace_limit(old[1], path[1:], value), old[2])
    # The variable term approaches a limit.  Any constant suffix following
    # it is absorbed: sup_n (x_n + 1) = sup_n x_n, for example.
    return add(tree[:i], new)


def _common_frame(xs):
    path = ()
    while True:
        if len({len(x) for x in xs}) != 1 or not xs[0]:
            return path, xs
        varying = [i for i in range(len(xs[0]))
                   if not (xs[0][i] == xs[1][i] == xs[2][i])]
        if len(varying) != 1:
            return path, xs
        i = varying[0]
        terms = [x[i] for x in xs]
        if terms[0][1] == terms[1][1] == terms[2][1]:
            xs = [p[2] for p in terms]
            path += (('arg', i),)
        elif terms[0][2] == terms[1][2] == terms[2][2]:
            xs = [p[1] for p in terms]
            path += (('level', i),)
        else:
            return path, xs


def candidate(xs):
    """Return (ordinal, frame path, operation), or None.

    The fundamental-sequence test is a necessary check, not a proof that
    arbitrary later terms follow the observed pattern.
    """
    if len(xs) != 3 or not (cmp(xs[0], xs[1]) < 0 and cmp(xs[1], xs[2]) < 0):
        return None
    first = _single_step(xs[0], xs[1])
    second = _single_step(xs[1], xs[2])
    path = None
    operation = None
    inner = None
    if first is not None and second is not None and first[:2] == second[:2]:
        path, operation = first[:2]
        level = ONE if operation == 'omega' else nat(2)
        inner = evalord.next_fp(level, second[3])
    else:
        path, parts = _common_frame(xs)
        if not path:
            return None
        operation = 'ordinary'
        inner = evalord.sup(parts)
        if inner is None:
            return None
    try:
        result = _replace_limit(xs[2], path, inner)
        if not is_limit(result) or not all(cmp(x, result) < 0 for x in xs):
            return None
        # A surrounding frame can make result[2] much larger than the third
        # sample even for a true tower limit; require the first FS bound here.
        if cmp(fs(result, 1), xs[2]) > 0:
            return None
    except (AssertionError, IndexError, RecursionError, ValueError):
        return None
    return result, path, operation
