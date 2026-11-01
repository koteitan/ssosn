"""Find a fundamental-sequence bracket for the 300 limit copy words.

The finite check proposes an inductive invariant; it is not a symbolic proof.
Run: timeout 60 python3 work/v_fs_bracket43.py
"""
from collections import Counter
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE.parent)]

import ordinal
import v_bits43
from v_constraints_real43 import real_copy_word
from v_symbolic_cut43 import grammar_class


def relation(parent, value, n):
    for shift in (-1, 0, 1, 2):
        if value == ordinal.fs(parent, n+shift):
            return f'eq_{shift:+d}'
    if (ordinal.cmp(ordinal.fs(parent, n), value) < 0 and
            ordinal.cmp(value, ordinal.fs(parent, n+1)) < 0):
        return 'between_0_1'
    return 'outside'


def main():
    words = [tuple(item['word']) for item in
             json.loads((HERE / 'p1-v-ext43-20.json').read_text())['bits_words']
             if item['word'][-1] != 'W']
    counts = Counter()
    changing = []
    for word in words:
        parent = v_bits43.rank(word)
        relations = [relation(parent, v_bits43.rank(real_copy_word(word, n)), n)
                     for n in range(1, 7)]
        key = (grammar_class(word)[0], relations[0])
        counts[key] += 1
        if len(set(relations)) != 1:
            changing.append((''.join(word), relations))
    report = {'counts': {str(k): v for k, v in counts.items()},
              'changing': changing[:20], 'changing_count': len(changing)}
    (HERE / 'v-fs-bracket43.json').write_text(
        json.dumps(report, ensure_ascii=False, indent=1) + '\n')
    print(report)


if __name__ == '__main__':
    main()
