"""Audit top-level (2,1) roots in standard forms of [P,P1).

Run after p1_tokens43.py: timeout 60 python3 work/p1_blocks43.py
The tree-root criterion is sp(i)=2 for a 2 at one-based position i.
"""
from collections import Counter
import json
from pathlib import Path

import harness
from p1_tokens43 import P, parse_all, token_map, token_prefix_possible


def main():
    source = Path(__file__).with_name('p1-tokens43-18.json')
    data = json.loads(source.read_text())
    tm = token_map(data['maxlen'])
    counts = Counter()
    examples = []
    for digits in data['standard_raw']:
        raw = tuple(map(int, digits))
        seq = harness.Seq(raw, 'new')
        roots = [i for i in range(3, len(raw)+1)
                 if raw[i-1] == 2 and seq.sp(i) == 2]
        assert roots and roots[0] == 3, (digits, roots)
        counts['sequences'] += 1
        counts[f'block_count_{len(roots)}'] += 1
        starts = [i-1 for i in roots]
        blocks = [raw[starts[j]:starts[j+1] if j+1 < len(starts) else len(raw)]
                  for j in range(len(starts))]
        counts['nonincreasing' if all(a >= b for a, b in zip(blocks, blocks[1:]))
               else 'increasing_pair'] += 1
        if all(block[:2] == (2, 1) for block in blocks):
            counts['all_blocks_start_21'] += 1
        else:
            counts['block_without_21'] += 1
        tail = raw[4:]
        if parse_all(tail, tm):
            counts['block_tail_complete_tokens'] += 1
        elif token_prefix_possible(tail, tm):
            counts['block_tail_token_prefix'] += 1
        else:
            counts['block_tail_outside_token_prefix'] += 1
        if digits in ('002102011', '002102021'):
            pairs = [i for i in range(3, len(raw))
                     if raw[i-1:i+1] == (2, 1)]
            examples.append({'raw': digits, 'roots': roots,
                             'all_21_pairs': pairs,
                             'parents_of_pair_heads': {str(i): seq.sp(i) for i in pairs},
                             'cut': seq.cut()})
    report = {'criterion': 'entry 2 with sp(position)=2 (one-based)',
              'maxlen': data['maxlen'], 'counts': dict(counts),
              'examples': examples}
    path = Path(__file__).with_name('p1-blocks43.json')
    path.write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n')
    print(json.dumps(report, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
