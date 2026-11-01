"""Measure the recursive, unbounded W/D/V copy-word grammar.

Language L: words starting D V, with every later V immediately after D,
whose bits are recursively canonical under T/T2 (v_bit_normal43.canon).
No ordinal value is used in the membership decision.  W L is the second
copy context.  The script checks standardness, token-only cuts, and closure
under real-term copy words for a bounded token length and term count.

Run: timeout 60 python3 work/v_infinite_grammar43.py --tokens 12 --terms 6
"""
import argparse
from collections import Counter
from itertools import product
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE.parent)]

import harness
import p1_token_cut43 as cut_rule
import std
import v_bits43
from v_bit_normal43 import canon
from v_constraints_real43 import RAW, real_copy_word
from v_symbolic_cut43 import classify


def admissible(word):
    word = tuple(word)
    return (word[:2] == ('D', 'V') and
            all(word[i] != 'V' or word[i-1] == 'D'
                for i in range(2, len(word))) and
            canon(v_bits43.bits(word)))


def grammar_cut(word, raw):
    tokens = word[1:]  # the first D is in P=(0,0,2,1,D)
    if word[-1] == 'V':
        return len(raw)-2
    if word[-1] == 'W':
        return cut_rule.w_cut(tokens, RAW)[1]
    if 'W' in word:
        return cut_rule.third_parent_cut(raw, tokens, RAW)[2]
    return cut_rule.d_cut(tokens, RAW)[1]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--tokens', type=int, default=12)
    ap.add_argument('--terms', type=int, default=6)
    args = ap.parse_args()
    counts = Counter()
    failures = []
    for length in range(2, args.tokens+1):
        for tail in product('WDV', repeat=length-2):
            word = ('D', 'V') + tail
            if any(word[i] == 'V' and word[i-1] != 'D'
                   for i in range(2, len(word))):
                continue
            raw = (0, 0, 2, 1) + tuple(x for t in word for x in RAW[t])
            predicted = admissible(word)
            actual = std.is_standard(raw)
            counts['normal_words'] += 1
            counts['standard' if actual else 'nonstandard'] += 1
            if predicted != actual:
                failures.append(('membership', ''.join(word), predicted, actual))
            if not predicted:
                continue
            cut = grammar_cut(word, raw)
            if cut != harness.Seq(raw, 'new').cut():
                failures.append(('cut', ''.join(word), cut,
                                 harness.Seq(raw, 'new').cut()))
            counts['cut_checked'] += 1
            prefixed = ('W',) + word
            kind, pos = classify(prefixed)
            own_kind, own_pos = classify(word)
            if word[-1] == 'V':
                expected = ('V_HEAD', None)
            elif word[-1] == 'D':
                expected = ('D_W_HEAD', 0 if own_kind == 'D_ROOT' else own_pos+1)
            elif word[2] == 'W':
                expected = ('W_ROOT', None)
            else:
                expected = ('W_V_HEAD', 2)
            if (kind, pos) != expected:
                failures.append(('W-prefix cut', ''.join(word), expected, (kind, pos)))
            counts['W_prefix_cut_checked'] += 1
            if word[-1] == 'W':
                continue
            for prefix in ((), ('W',)):
                source = prefix + word
                for n in range(1, args.terms+1):
                    term = real_copy_word(source, n)
                    if 'V' in term:
                        core = term[1:] if term[0] == 'W' else term
                        valid = admissible(core)
                    else:
                        valid = True  # W/D-only rank belongs to the old binary domain.
                    counts['closure_checked'] += 1
                    if not valid:
                        failures.append(('closure', ''.join(source), n,
                                         ''.join(term)))
    print(dict(counts))
    print('failures', len(failures), failures[:10])


if __name__ == '__main__':
    main()
