"""Experimental 0/1/2/3 copy ranks for the P1 region (§44)."""
from functools import lru_cache
import sys
from pathlib import Path

sys.path[:0] = [str(Path(__file__).resolve().parent),
                str(Path(__file__).resolve().parent.parent)]

import conj2
import v_bits43
from ordinal import ZERO, ONE, P, add, nat, w


class Unknown(Exception):
    pass


def bits3(tokens):
    out = []
    for token in tokens:
        if token == 'W':
            out.append(0)
        elif token == 'D':
            out.append(1)
        elif token == 'V':
            if out and out[-1] == 1:
                out[-1] = 2
            else:
                out.append(3)
        else:
            raise Unknown(('bits3: unsupported token', token))
    return tuple(out)


def bits4(tokens):
    """W->0, D->1; V increments a positive final bit, else appends 3."""
    out = []
    for token in tokens:
        if token == 'W':
            out.append(0)
        elif token == 'D':
            out.append(1)
        elif token == 'V':
            if out and out[-1] >= 1:
                out[-1] += 1
            else:
                out.append(3)
        else:
            raise Unknown(('bits4: unsupported token', token))
    return tuple(out)


def T3(word):
    """Drop the first 3 from every nonzero run; all runs must start in 3."""
    runs, cur = [], []
    for digit in word:
        if digit == 0:
            runs.append(cur)
            cur = []
        else:
            cur.append(digit)
    runs.append(cur)
    if not all(run and run[0] == 3 for run in runs):
        raise Unknown(('T3: run not led by 3', tuple(word)))
    out = []
    for i, run in enumerate(runs):
        if i:
            out.append(0)
        out.extend(run[1:])
    return tuple(out)


def Tk(word, k):
    """Drop each nonzero run's leading symbol k, requiring all heads to equal k."""
    runs = _runs(tuple(word))
    if k < 2 or not all(run and run[0] == k for run in runs):
        raise Unknown(('Tk: run heads do not all equal k', k, tuple(word), runs))
    out = []
    for i, run in enumerate(runs):
        if i:
            out.append(0)
        out.extend(run[1:])
    return tuple(out)


def Tstar_k(word, k):
    """Drop leading k only in runs headed k; preserve runs headed above k."""
    runs = _runs(tuple(word))
    if k < 2 or not runs or any(not run or run[0] < k for run in runs):
        raise Unknown(('Tstar_k: run head below k', k, tuple(word), runs))
    out = []
    for i, run in enumerate(runs):
        if i:
            out.append(0)
        out.extend(run[1:] if run[0] == k else run)
    return tuple(out)


def _runs(word):
    runs, cur = [], []
    for digit in word:
        if digit == 0:
            runs.append(tuple(cur))
            cur = []
        else:
            cur.append(digit)
    runs.append(tuple(cur))
    return tuple(runs)


@lru_cache(maxsize=300000)
def v3(word):
    word = tuple(word)
    value = ZERO
    for unit in conj2.units(word):
        if unit == (0,):
            value = add(value, ONE)
            continue
        if unit == (2,):
            value = add(value, P(ONE, ZERO))
            continue
        smaller = tuple(conj2.T(unit))
        if smaller != unit:
            value = add(value, w(add(ONE, v3(smaller))))
            continue
        runs = _runs(unit)
        heads = tuple(run[0] if run else None for run in runs)
        if heads and all(head == 2 for head in heads):
            value = add(value, P(ONE, v3(v_bits43.T2(unit))))
        elif heads and all(head == 3 for head in heads):
            value = add(value, P(nat(2), v3(T3(unit))))
        else:
            raise Unknown(('self-reference with mixed/unsupported run heads', unit, heads))
    return value


def rank(tokens):
    return v3(bits3(tuple(tokens)))


def B(tokens):
    """Candidate block value φ(1,φ(1,ω^(v3(bits3(tokens)))))."""
    inner = P(ONE, w(v3(bits3(tuple(tokens)))))
    return P(ONE, inner)


@lru_cache(maxsize=300000)
def v4(word):
    """The v2 fold with a uniform leading-k rule for self-reference."""
    word = tuple(word)
    value = ZERO
    for unit in conj2.units(word):
        if unit == (0,):
            value = add(value, ONE)
            continue
        if unit == (2,):
            value = add(value, P(ONE, ZERO))
            continue
        smaller = tuple(conj2.T(unit))
        if smaller != unit:
            value = add(value, w(add(ONE, v4(smaller))))
            continue
        runs = _runs(unit)
        heads = tuple(run[0] if run else None for run in runs)
        if not heads or any(head < 2 for head in heads):
            raise Unknown(('v4: self-reference with mixed/unsupported run heads',
                           unit, heads))
        k = min(heads)
        reduced = Tk(unit, k) if all(head == k for head in heads) else Tstar_k(unit, k)
        value = add(value, P(nat(k - 1), v4(reduced)))
    return value


def rank4(tokens):
    return v4(bits4(tuple(tokens)))


def B4(tokens):
    """The same outer block transform, with v4 on the 4-bit encoding."""
    inner = P(ONE, w(v4(bits4(tuple(tokens)))))
    return P(ONE, inner)


def bits6(tokens):
    """The v6 encoding; the initial V is tagged as the root symbol kR."""
    out = []
    for token in tokens:
        if token == 'W':
            out.append(0)
        elif token == 'D':
            out.append(1)
        elif token == 'V':
            if not out:
                out.append(('R', 2))
            elif isinstance(out[-1], tuple) and out[-1][0] == 'R':
                out[-1] = ('R', out[-1][1] + 1)
            elif out[-1] >= 1:
                out[-1] += 1
            else:
                out.append(2)
        else:
            raise Unknown(('bits6: unsupported token', token))
    return tuple(out)


def _decode_bits6(word):
    digits = []
    root = None
    for i, item in enumerate(word):
        if isinstance(item, tuple) and len(item) == 2 and item[0] == 'R':
            if i != 0 or root is not None:
                raise Unknown(('v6: misplaced root marker', word))
            root = item[1]
            digits.append(item[1])
        else:
            digits.append(item)
    return tuple(digits), root


@lru_cache(maxsize=300000)
def v6(word):
    """The v4 fold with a marked root seed in its first self-referential unit."""
    word = tuple(word)
    digits, root = _decode_bits6(word)
    value = ZERO
    offset = 0
    for index, unit in enumerate(conj2.units(digits)):
        rooted = root is not None and index == 0 and offset == 0
        offset += len(unit)
        if unit == (0,):
            value = add(value, ONE)
            continue
        if unit == (2,) and not rooted:
            value = add(value, P(ONE, ZERO))
            continue
        smaller = tuple(conj2.T(unit))
        if smaller != unit:
            value = add(value, w(add(ONE, v6(smaller))))
            continue
        runs = _runs(unit)
        heads = tuple(run[0] if run else None for run in runs)
        if not heads or any(head < 2 for head in heads) or len(set(heads)) != 1:
            raise Unknown(('v6: self-reference with mixed/unsupported run heads',
                           unit, heads))
        k = heads[0]
        reduced = Tk(unit, k)
        if rooted:
            seed = P(nat(k), ZERO)
            value = add(value, P(nat(k - 1), add(seed, v6(reduced))))
        else:
            value = add(value, P(nat(k - 1), v6(reduced)))
    return value


def B6_copy(tokens):
    """The v6 value of a real copy tail (without adding a new root marker)."""
    return v6(bits6(tuple(tokens)))


def v7(tokens):
    """Root value: the marked root seed plus the ordinary v4 value of its tail."""
    encoded = bits6(tuple(tokens))
    digits, root = _decode_bits6(encoded)
    if root is None:
        return v4(digits)
    if len(digits) == 1:
        return P(nat(root), ZERO)
    seed = P(nat(root), ZERO)
    units = conj2.units(digits)
    # The root's singleton unit is already represented by seed.  Drop it
    # before evaluating the remainder; joined units such as 201 stay whole.
    if units and units[0] == (root,):
        digits = digits[1:]
    return add(seed, v4(digits))


def B7(tokens):
    """Outer block transform B(r)=φ(1,φ(1,ω^r)) for the v7 root rank."""
    r = v7(tuple(tokens))
    inner = P(ONE, w(r))
    return P(ONE, inner)


if __name__ == '__main__':
    from ordinal import show
    for arg in sys.argv[1:]:
        tokens = tuple(x for x in arg.split() if x)
        try:
            print(tokens, bits3(tokens), show(v3(bits3(tokens))), show(B(tokens)),
                  '|', bits4(tokens), show(v4(bits4(tokens))), show(B4(tokens)),
                  '|', bits6(tokens), show(v6(bits6(tokens))),
                  show(B6_copy(tokens)), '| v7', show(v7(tokens)),
                  'B7', show(B7(tokens)))
        except Unknown as exc:
            print(tokens, 'UNKNOWN', exc)
