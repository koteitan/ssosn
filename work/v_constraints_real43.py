"""Test real-expansion sup constraints for the 408 W/D/V copy words.

The computation does not call v_bits43; that module is used only to audit the
result and to show the conjectured ranks of real terms.  The representative
sequence for a copy word c is (0,0,2,1) ++ raw(c).  Its real terms are made by
harness.fs, with the final 0 or 01 stripped before tokenization.

Run: timeout 60 python3 work/v_constraints_real43.py
"""
from collections import Counter
from functools import lru_cache
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE.parent)]

import evalord
import harness
import token_tree
from ordinal import ONE, add, lt, show

token_tree.V_ROOT_EXPERIMENT = True
RAW = {'W': (0, 1, 2, 1), 'D': (0, 2), 'V': (0, 2, 1)}


class Unknown(Exception):
    pass


@lru_cache(maxsize=None)
def real_copy_word(word, n):
    """The complete W/D/V word in the nth real term, if one exists."""
    seq = (0, 0, 2, 1) + tuple(x for t in word for x in RAW[t])
    term = harness.fs(seq, n)
    if term[-1] == 0:
        body = term[4:-1]
    elif term[-2:] == (0, 1):
        body = term[4:-2]
    else:
        raise Unknown(('unknown terminal', word, n))
    try:
        parsed = token_tree.parse(body, True)
    except token_tree.Unknown as error:
        raise Unknown(('untokenizable real term', word, n)) from error
    if any(t not in RAW for t in parsed):
        raise Unknown(('real term leaves W/D/V language', word, n, parsed))
    return parsed


@lru_cache(maxsize=None)
def rank(word):
    """Rules (i), (ii') and the stated W successor part of (iii)."""
    if 'V' not in word:
        bits = tuple(0 if t == 'W' else 1 for t in word)
        return token_tree.ordinal(token_tree.binary_index(bits))
    if word[-1] == 'W':
        return add(rank(word[:-1]), ONE)
    # Both D and V are limits.  Real-term copy words may grow rather than
    # shorten, so the first unknown dependency stops the calculation.
    words = tuple(real_copy_word(word, n) for n in range(1, 5))
    if any('V' in w and len(w) >= len(word) for w in words[1:]):
        raise Unknown(('non-decreasing real-term dependency', word,
                       tuple(words[:2])))
    xs = [rank(w) for w in words]
    if any(not lt(a, b) for a, b in zip(xs, xs[1:])):
        raise Unknown(('real-term ranks not increasing', word))
    s3, s4 = evalord.sup(xs[:3]), evalord.sup(xs)
    if s3 is None or s3 != s4 or not all(lt(x, s4) for x in xs):
        raise Unknown(('sampled sup uncertified', word))
    return s4


def main():
    import v_bits43  # comparison only
    items = json.loads((HERE / 'p1-v-ext43-20.json').read_text())['bits_words']
    counts = Counter()
    rows = []
    for item in items:
        word = tuple(item['word'])
        target = v_bits43.rank(word)
        try:
            got = rank(word)
            reason = None
        except Unknown as error:
            got = None
            reason = str(error.args[0])
        counts['agree' if got == target else 'differ' if got is not None else 'unknown'] += 1
        rows.append({'word': ''.join(word), 'target': show(target),
                     'derived': None if got is None else show(got), 'reason': reason})
    rows.sort(key=lambda r: (len(r['word']), r['word']))
    report = {'counts': dict(counts), 'rows': rows,
              'shortest_unknown': next((r for r in rows if r['derived'] is None), None),
              'shortest_differ': next((r for r in rows if r['derived'] is not None and
                                      r['derived'] != r['target']), None)}
    (HERE / 'v-constraints-real43.json').write_text(
        json.dumps(report, ensure_ascii=False, indent=1) + '\n')
    print('counts', dict(counts))
    print('shortest_unknown', report['shortest_unknown'])
    print('shortest_differ', report['shortest_differ'])
    print('DVD real terms:')
    for n in range(1, 7):
        w = real_copy_word(('D', 'V', 'D'), n)
        try:
            direct = show(rank(w))
        except Unknown:
            direct = 'undecided'
        print(n, ''.join(w), direct, 'v2=' + show(v_bits43.rank(w)))


if __name__ == '__main__':
    main()
