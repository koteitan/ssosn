"""Explore the infinite copy-word closure from the 30 seed words.

Run: timeout 60 python3 work/v_closure43.py --nmax 30 --maxlen 60
The language check uses the purely syntactic recursive grammar in
v_bit_normal43.py.  The actual cut is measured once per source word.
"""
import argparse
from collections import Counter, deque
from functools import lru_cache
import time

import v_bits43
from v_bit_normal43 import canon
from v_copy_grammar43 import SEEDS
from v_symbolic_cut43 import classify, symbolic_term


@lru_cache(maxsize=None)
def accepted(word):
    return (word[:2] == ('D', 'V') and
            all(word[i] != 'V' or word[i-1] == 'D'
                for i in range(2, len(word))) and
            canon(v_bits43.bits(word)))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--nmax', type=int, default=30)
    ap.add_argument('--maxlen', type=int, default=60)
    ap.add_argument('--budget', type=float, default=45)
    args = ap.parse_args()
    seen = {tuple(x) for x in SEEDS}
    queue = deque(seen)
    counts = Counter()
    issues = []
    t0 = time.monotonic()
    while queue:
        if time.monotonic()-t0 > args.budget:
            counts['budget_stop'] = len(queue)
            break
        word = queue.popleft()
        counts['processed'] += 1
        if not accepted(word):
            issues.append(('grammar', ''.join(word)))
        kind, pos = classify(word)
        counts[kind] += 1
        if word[-1] == 'W':
            continue
        for n in range(1, args.nmax+1):
            term = symbolic_term(word, n, kind, pos)
            if len(term) > args.maxlen:
                break
            if 'V' not in term:
                counts['binary_term'] += 1
                continue
            counts['terms_checked'] += 1
            if not accepted(term):
                issues.append(('closure', ''.join(word), n, ''.join(term)))
            if term not in seen:
                seen.add(term)
                queue.append(term)
    print('counts', dict(counts), 'words', len(seen),
          'maxlen', max(map(len, seen)), 'seconds', round(time.monotonic()-t0, 2))
    print('issues', len(issues), issues[:10])


if __name__ == '__main__':
    main()
