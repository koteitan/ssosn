"""Classify token cuts and verify all-n-shaped copy-word expansions on 408 words.

The class is inferred from the actual cut once per word; the predicted nth
term is then assembled entirely as a token word.  This is a bounded check of
the proposed symbolic laws, not an all-length proof of the cut classifier.

Run: timeout 60 python3 work/v_symbolic_cut43.py
"""
from collections import Counter
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE.parent)]

import harness
import v_constraints_real43 as real


def classify(word):
    seq = (0, 0, 2, 1) + tuple(x for t in word for x in real.RAW[t])
    cut = harness.Seq(seq, 'new').cut()
    if word[-1] == 'V':
        if cut == len(seq) - 2:
            return ('V_HEAD', None)
        return ('OTHER', cut)
    if word[-1] == 'D':
        if cut == 2:
            return ('D_ROOT', None)
        start = 4
        for i, token in enumerate(word):
            if token == 'W' and cut == start + 2:
                return ('D_W_HEAD', i)
            start += len(real.RAW[token])
        return ('OTHER', cut)
    if word[-1] == 'W':
        if cut == 2:
            return ('W_ROOT', None)
        start = 4
        for i, token in enumerate(word):
            if token == 'V' and cut == start + 1:
                return ('W_V_HEAD', i)
            start += len(real.RAW[token])
        return ('OTHER', cut)
    raise AssertionError(word)


def grammar_class(word):
    """Finite-grammar cut class, using tokens alone and no Seq operation."""
    if word[:2] == ('D', 'V'):
        if word[-1] == 'V':
            return ('V_HEAD', None)
        if word[-1] == 'W':
            return ('W_ROOT', None)
        return ('D_W_HEAD', 3) if word == ('D', 'V', 'W', 'W', 'D') else ('D_ROOT', None)
    if word[:3] == ('W', 'D', 'V'):
        core = word[1:]
        if word[-1] == 'V':
            return ('V_HEAD', None)
        if word[-1] == 'D':
            return ('D_W_HEAD', 4) if core == ('D', 'V', 'W', 'W', 'D') else ('D_W_HEAD', 0)
        return ('W_ROOT', None) if core[2] == 'W' else ('W_V_HEAD', 2)
    return ('OTHER', None)


def symbolic_term(word, n, kind, pos):
    if kind == 'V_HEAD':
        return word[:-1] + ('D',) * n
    if kind == 'D_ROOT':
        unit = word[:-1]
        return unit + (('W',) + unit) * (n - 1)
    if kind == 'D_W_HEAD':
        head, after_w = word[:pos], word[pos+1:-1]
        return head + (('W',) + after_w) * n
    return None  # W is the successor +1 case, not a W/D/V limit term.


def main():
    items = json.loads((HERE / 'p1-v-ext43-20.json').read_text())['bits_words']
    counts, failures = Counter(), []
    for item in items:
        word = tuple(item['word'])
        kind, pos = classify(word)
        counts[kind] += 1
        predicted_class, predicted_pos = grammar_class(word)
        if (kind, pos) != (predicted_class, predicted_pos):
            failures.append({'word': ''.join(word), 'kind': 'grammar_class',
                             'actual': (kind, pos),
                             'predicted': (predicted_class, predicted_pos)})
        if kind == 'OTHER':
            failures.append({'word': ''.join(word), 'kind': 'cut', 'position': pos})
            continue
        if word[-1] == 'W':
            continue
        for n in range(1, 11):
            actual = real.real_copy_word(word, n)
            predicted = symbolic_term(word, n, kind, pos)
            counts['checked_terms'] += 1
            if actual != predicted:
                failures.append({'word': ''.join(word), 'n': n,
                                 'actual': ''.join(actual),
                                 'predicted': ''.join(predicted)})
    report = {'counts': dict(counts), 'failures': failures[:20]}
    (HERE / 'v-symbolic-cut43.json').write_text(
        json.dumps(report, ensure_ascii=False, indent=1) + '\n')
    print(report)


if __name__ == '__main__':
    main()
