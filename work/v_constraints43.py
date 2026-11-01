"""Partial copy-rank evaluator from the stated constraints, without v2.

The evaluator uses the old W/D binary rank, ADD for a trailing W, and the
real V expansion as a supremum.  A D after a V needs a new continuation law:
the §42 WD-ii rule is for a D following a W-run with an A_k depth and does
not specify this case.  Unknown is therefore a result, not a fitted value.

Run: timeout 60 python3 work/v_constraints43.py
"""
from collections import Counter
from functools import lru_cache
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE.parent)]

import evalord
import token_tree
from ordinal import ONE, add, lt, show


class Unknown(Exception):
    pass


@lru_cache(maxsize=None)
def rank(word):
    word = tuple(word)
    if any(t not in ('W', 'D', 'V') for t in word):
        raise Unknown(('outside alphabet', word))
    if 'V' not in word:
        bits = tuple(0 if t == 'W' else 1 for t in word)
        return token_tree.ordinal(token_tree.binary_index(bits))
    if word[-1] == 'W':
        return add(rank(word[:-1]), ONE)
    if word[-1] == 'V':
        xs = [rank(word[:-1] + ('D',)*n) for n in range(1, 5)]
        if any(not lt(x, y) for x, y in zip(xs, xs[1:])):
            raise Unknown(('V terms not strictly increasing', word))
        s3, s4 = evalord.sup(xs[:3]), evalord.sup(xs)
        if s3 is None or s3 != s4 or not all(lt(x, s4) for x in xs):
            raise Unknown(('V sup not certified by samples', word))
        return s4
    # The §42 WD-ii formula has a depth k and a copy subword R1.  Neither is
    # specified for a D immediately after V; assigning a number here would
    # add a fourth rule rather than derive one from (i)-(iii).
    raise Unknown(('D continuation after V lacks a depth/copy law', word))


def main():
    import v_bits43  # comparison only; rank() above never calls it
    data = json.loads((HERE / 'p1-v-ext43-20.json').read_text())
    counts = Counter()
    rows = []
    for item in data['bits_words']:
        word = tuple(item['word'])
        target = v_bits43.rank(word)
        try:
            got = rank(word)
        except Unknown as error:
            got = None
            reason = error.args[0]
        else:
            reason = None
        counts['agree' if got == target else 'differ' if got is not None else 'unknown'] += 1
        rows.append({'word': item['word'], 'target': show(target),
                     'derived': None if got is None else show(got),
                     'reason': None if reason is None else str(reason)})
    rows.sort(key=lambda row: (len(row['word']), row['word']))
    report = {'constraints': ['binary W/D', 'trailing W = +1',
                              'trailing V = sup of D^n',
                              'WD-ii applies only with a specified depth and copy'],
              'counts': dict(counts), 'rows': rows,
              'shortest_unknown': next((row for row in rows if row['derived'] is None), None),
              'shortest_differ': next((row for row in rows if row['derived'] is not None and
                                      row['derived'] != row['target']), None)}
    (HERE / 'v-constraints43.json').write_text(
        json.dumps(report, ensure_ascii=False, indent=1) + '\n')
    print('counts', dict(counts))
    print('shortest_unknown', report['shortest_unknown'])
    print('shortest_differ', report['shortest_differ'])
    print('first rows', rows[:20])


if __name__ == '__main__':
    main()
