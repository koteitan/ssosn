"""Exact bounded token grammar for the 408 copy words of the N=20 audit.

B is the explicit 30-word seed grammar.  The recursive-looking production is
applied once, with n=1..10, matching the actual real-term audit.  The script
checks the seed list against standard forms and the generated set against the
recorded copy-word set; its generation itself never calls Seq/std.

Run: timeout 60 python3 work/v_copy_grammar43.py
"""
from collections import Counter
from itertools import product
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE.parent)]

import std
from v_symbolic_cut43 import grammar_class, symbolic_term, real

SEEDS = '''
DV DVD DVW DVDD DVDV DVDW DVWD DVWW DVDDD DVDDW DVDVD DVDVW DVDWD
DVDWW DVWDD DVWDV DVWDW DVWWD DVDDDD DVDDDW DVDDWD DVDVDD DVDVDV
DVDVDW DVDVWD DVDWDD DVDWDV DVWDDD DVDDDDD DVDVDDD
'''.split()


def generate():
    bases = {tuple(word) for word in SEEDS}
    generated = set(bases)
    for word in bases:
        if word[-1] == 'W':
            continue
        kind, pos = grammar_class(word)
        for n in range(1, 11):
            term = symbolic_term(word, n, kind, pos)
            if 'V' in term:
                generated.add(term)
    return bases, generated | {('W',) + word for word in generated}


def main():
    bases, generated = generate()
    actual = {tuple(item['word']) for item in
              json.loads((HERE / 'p1-v-ext43-20.json').read_text())['bits_words']}
    base_check = Counter()
    for word in bases:
        raw = (0, 0, 2, 1) + tuple(x for t in word for x in real.RAW[t])
        base_check[(len(raw) <= 20, std.is_standard(raw))] += 1
    all_direct = set()
    for length in range(2, 10):
        for tail in product('WDV', repeat=length-2):
            word = ('D', 'V') + tail
            raw = (0, 0, 2, 1) + tuple(x for t in word for x in real.RAW[t])
            if len(raw) <= 20 and std.is_standard(raw):
                all_direct.add(word)
    counts = {'seeds': len(bases), 'generated': len(generated),
              'actual': len(actual), 'missing': len(actual - generated),
              'extra': len(generated - actual), 'base_checks': dict(
                  (str(k), v) for k, v in base_check.items()),
              'all_direct': len(all_direct),
              'direct_seed_difference': len(all_direct ^ bases)}
    print(counts)
    print('missing examples', [''.join(w) for w in list(actual-generated)[:10]])
    print('extra examples', [''.join(w) for w in list(generated-actual)[:10]])


if __name__ == '__main__':
    main()
