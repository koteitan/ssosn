"""Bounded FS sandwich test for the recursive W/D/V grammar.

Run: timeout 60 python3 work/v_inequality43.py --tokens 12 --terms 6
This is a measurement, not an induction proof.
"""
import argparse
from collections import Counter
from functools import lru_cache
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE.parent)]

import ordinal
import v_bits43
from v_bit_normal43 import canon
from v_constraints_real43 import real_copy_word
from v_symbolic_cut43 import classify


@lru_cache(maxsize=None)
def rank(word):
    return v_bits43.rank(word)


def words_u(max_tokens):
    frontier = {('D', 'V')}
    yield ('D', 'V')
    for _ in range(3, max_tokens+1):
        nxt = set()
        for word in frontier:
            for token in 'WDV':
                if token == 'V' and word[-1] != 'D':
                    continue
                child = word+(token,)
                if canon(v_bits43.bits(child)):
                    nxt.add(child)
        for word in nxt:
            yield word
        frontier = nxt


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--tokens', type=int, default=12)
    ap.add_argument('--terms', type=int, default=6)
    ap.add_argument('--budget', type=float, default=50)
    args = ap.parse_args()
    t0 = time.monotonic()
    counts = Counter()
    failures = []
    for core in words_u(args.tokens):
        if core[-1] == 'W':
            continue
        for prefix in ((), ('W',)):
            word = prefix+core
            kind, _ = classify(word)
            parent = rank(word)
            counts['limit_words'] += 1
            if not ordinal.is_limit(parent):
                counts['rank_not_limit'] += 1
                if len(failures) < 10:
                    failures.append(('rank_not_limit', ''.join(word)))
                continue
            for n in range(1, args.terms+1):
                term = rank(real_copy_word(word, n))
                low = ordinal.fs(parent, n-1)
                high = ordinal.fs(parent, n+2)
                counts['terms'] += 1
                if ordinal.cmp(term, parent) >= 0:
                    counts['term_ge_parent'] += 1
                    if len(failures) < 10:
                        failures.append(('term_ge_parent', ''.join(word), n))
                if ordinal.cmp(low, term) > 0:
                    counts['below_lower_fs'] += 1
                    if len(failures) < 10:
                        failures.append(('below_lower_fs', ''.join(word), n))
                if ordinal.cmp(term, high) > 0:
                    counts['above_upper_fs'] += 1
                    if len(failures) < 10:
                        failures.append(('above_upper_fs', ''.join(word), n))
                counts[kind] += 1
        if time.monotonic()-t0 > args.budget:
            counts['budget_stop'] += 1
            break
    print(dict(counts), 'seconds', round(time.monotonic()-t0, 2))
    print('failures', failures)


if __name__ == '__main__':
    main()
