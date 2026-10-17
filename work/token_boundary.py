"""Candidate fresh-tail fold above P=(2,1,0,2).

The copy in L_A is W D, whose A0-unit increment is omega^omega.
Thus the first A1 opens omega^(omega+1), rather than omega^2.
Leading W/D and a W after a rank-limit D are deliberately unsupported.
"""
from functools import lru_cache
import token_value as V
from ordinal import ONE, ZERO, OMEGA, P, add, nat, w

BASE = (2, 1, 0, 2)


def parse(tail):
    tail = tuple(tail)
    out = []
    while tail:
        if tail[:2] == (0, 2):
            out.append('D')
            tail = tail[2:]
            continue
        if tail[:3] != V.A(0):
            raise V.Unknown(('boundary non-token suffix', tail))
        size, k = 3, 0
        while tail[size:size+2] == (0, 2):
            size += 2
            k += 1
        if tail[size:size+1] == (1,):
            out.append('W' if k == 0 else 'E'+str(k))
            size += 1
        else:
            out.append('A'+str(k))
        tail = tail[size:]
    return tuple(out)


def epsilon_iter(value, depth, iterated, amount):
    if depth:
        t = value[-1]
        exponent = t[2] if t[1] == ZERO else (t,)
        if not exponent:
            raise V.Unknown('boundary epsilon depth')
        return add(value[:-1], w(epsilon_iter(exponent, depth-1, iterated, amount)))
    eps = V.next_fp(ONE, (value[-1],))
    q = eps[0][2]
    if iterated:
        q = add(q, amount)
    return add(value[:-1], P(ONE, q))


@lru_cache(maxsize=100000)
def index(tokens):
    base = V.block_value(BASE)[0][2]
    value = base
    fresh, active_depth, i = True, 0, 0
    while i < len(tokens):
        token = tokens[i]
        if token in ('W', 'D'):
            raise V.Unknown(('boundary leading/unattached operator', token))
        i += 1
        m = 0
        while i < len(tokens) and tokens[i] == 'W':
            i += 1
            m += 1
        amount = w(nat(m))
        if i < len(tokens) and tokens[i] == 'D':
            if not m:
                raise V.Unknown('boundary rank limit without W')
            amount = w(OMEGA)
            i += 1
        k = int(token[1:])
        if token.startswith('A'):
            if k == 0:
                value = add(value, amount)
            elif fresh:
                seed = add(OMEGA, amount)
                for _ in range(k):
                    seed = w(seed)
                value = add(base, seed)
            else:
                value = V.bump_last(value, k, amount)
            active_depth = k
        elif token == 'E1':
            if fresh:
                value = add(base, P(ONE, amount if m else ZERO))
            else:
                value = epsilon_iter(value, active_depth, m != 0, amount)
        else:
            raise V.Unknown(('boundary unsupported token', token))
        fresh = False
    return value


def block_value(block):
    if tuple(block[:len(BASE)]) != BASE or tuple(block) == BASE:
        raise V.Unknown('outside boundary fresh-tail family')
    return P(ONE, index(parse(block[len(BASE):])))
