"""Check whether recursive proof states are genuine SSOS copy words.

For every C1/C2 recursive edge of v_case_prove43, invert the child's bits to
W/D/V, check the representative's standardness, then compare its real-term
class and copy start with the recursive state.

Run: timeout 600 python3 work/v_case_cut43.py [--tokens 15]
"""
import argparse
from collections import Counter, defaultdict
from functools import lru_cache
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE.parent)]

import std
import v_bits43 as vb
import v_case_prove43 as VP
import v_unit_shapes43 as shapes
from v_constraints_real43 import RAW, Unknown, real_copy_word

SEQ_BASE = (0, 0, 2, 1)
INV = {0: 'W', 1: 'D', 2: 'DV'}


def inverse(y):
    return tuple(t for bit in y for t in INV[bit])


def raw_word(word):
    return SEQ_BASE + tuple(x for token in word for x in RAW[token])


@lru_cache(maxsize=None)
def actual_class(word):
    """Return (category, actual class, actual s, matching alternatives)."""
    raw = raw_word(word)
    if not std.is_standard(raw):
        return 'nonstandard', None, None, ()
    try:
        terms = tuple(real_copy_word(word, n) for n in (1, 2, 3))
    except Unknown as exc:
        return 'unknown', None, None, (str(exc.args[0]),)
    matches = shapes.match_classes(word, terms)
    if not matches:
        return 'available', 'OTHER', None, ()
    r3 = [pos for cls, pos in matches if cls == 'R3']
    if r3:
        cls, pos = 'R3', max(r3)
        s = len(vb.bits(word[:pos]))
    else:
        cls, pos = matches[0]
        bits = vb.bits(word)
        s = max(i for i, bit in enumerate(bits) if bit == 2) if cls == 'R1' else 0
    return 'available', cls, s, tuple(matches)


def child_edges(y, cls, s):
    """Yield (edge_kind, child_y, expected_class, expected_s)."""
    y = tuple(y)
    units, unit_spans = VP.spans(y)
    j = next(i for i, (lo, hi) in enumerate(unit_spans) if lo <= s < hi)
    if y == (1,) and cls == 'R2' or y == (2,) and cls == 'R1':
        return
    case = VP.case_of(y, cls, s, j)
    if case == 'C1':
        reason, data = VP.c1_reduce(y, cls, s, j)
        if data is None:
            return
        reduced, s2, _d, op = data
        yield 'C1-' + op, tuple(reduced), cls, s2
    elif case == 'C2':
        yield 'C2', tuple(units[-1]), 'R2', 0


def collect(max_tokens):
    counts = Counter()
    examples = defaultdict(list)
    edges_seen = 0

    def walk(y, cls, s, active=()):
        nonlocal edges_seen
        key = (tuple(y), cls, s)
        if key in active:
            return
        active = active + (key,)
        for kind, child_y, expected_cls, expected_s in child_edges(*key):
            edges_seen += 1
            child_y = tuple(child_y)
            child_word = inverse(child_y)
            if vb.bits(child_word) != child_y:
                raise AssertionError(('inverse mismatch', child_y, child_word,
                                      vb.bits(child_word)))
            status, actual_cls, actual_s, alternatives = actual_class(child_word)
            counts[(kind, status if status != 'available' else
                    ('agree' if (actual_cls, actual_s) ==
                     (expected_cls, expected_s) else 'differ'))] += 1
            if status == 'available' and (actual_cls, actual_s) != (expected_cls, expected_s):
                examples[kind].append({
                    'word': child_word, 'bits': child_y,
                    'expected': (expected_cls, expected_s),
                    'actual': (actual_cls, actual_s),
                    'matches': alternatives,
                })
            walk(child_y, expected_cls, expected_s, active)

    roots = VP.all_words(max_tokens)
    for root in roots:
        cls, s = VP.class_and_start(root)
        walk(vb.bits(root), cls, s)

    print('tokens', max_tokens, 'roots', len(roots), 'edge occurrences', edges_seen)
    for kind in ('C1-T', 'C1-T2', 'C2'):
        print(kind, {label: counts[(kind, label)]
                     for label in ('agree', 'differ', 'nonstandard', 'unknown')})
        rows = sorted(examples[kind], key=lambda row: (len(row['word']), row['word']))[:5]
        print(' ', 'shortest mismatches', [
            (''.join(row['word']), ''.join(map(str, row['bits'])),
             row['expected'], row['actual'], row['matches']) for row in rows])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--tokens', type=int, default=13)
    args = ap.parse_args()
    collect(args.tokens)


if __name__ == '__main__':
    main()
