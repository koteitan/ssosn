"""Audit top-level (2,1) blocks in standard forms of [P1,P2).

Run after p2_tokens44.py: timeout 600 python3 work/p2_blocks44.py
Block heads are one-based positions i with S[i]=2 and sp(i)=2.
"""
from collections import Counter, defaultdict
from functools import lru_cache
import json
from pathlib import Path
import time

import harness

HERE = Path(__file__).resolve().parent
DATA = HERE / 'p2-tokens44-18.json'
OUT = HERE / 'p2-blocks44.json'
MAXLEN = 18


@lru_cache(maxsize=100000)
def block_data(raw):
    raw = tuple(raw)
    seq = harness.Seq(raw, 'new')
    roots = tuple(i for i in range(3, len(raw) + 1)
                  if raw[i - 1] == 2 and seq.sp(i) == 2)
    if not roots or roots[0] != 3:
        raise AssertionError(('missing initial top-level root', raw, roots))
    starts = tuple(i - 1 for i in roots)
    blocks = tuple(raw[starts[j]:starts[j + 1] if j + 1 < len(starts)
                          else len(raw)]
                   for j in range(len(starts)))
    return roots, blocks


def spelling(raw):
    return ''.join(map(str, raw))


def row(raw):
    roots, blocks = block_data(tuple(raw))
    return {'raw': spelling(raw),
            'roots': list(roots),
            'blocks': [spelling(block) for block in blocks]}


def main():
    started = time.monotonic()
    data = json.loads(DATA.read_text())
    words = sorted((tuple(map(int, value)) for value in data['standard_raw']
                    if len(value) <= MAXLEN), key=lambda x: (len(x), x))
    counts = Counter()
    nonincreasing = Counter()
    order_failures = []
    one_block = []
    many_blocks = []
    limit_relations = {n: Counter() for n in range(1, 4)}
    limit_rows = []
    all_rows = []

    for raw in words:
        roots, blocks = block_data(raw)
        count = len(blocks)
        counts['sequences'] += 1
        counts[f'blocks_{count}'] += 1
        is_nondecreasing_bad = any(left < right
                                   for left, right in zip(blocks, blocks[1:]))
        if count >= 2:
            nonincreasing['words'] += 1
            if is_nondecreasing_bad:
                nonincreasing['violations'] += 1
                pairs = [(spelling(a), spelling(b))
                         for a, b in zip(blocks, blocks[1:]) if a < b]
                order_failures.append({**row(raw), 'increasing_pairs': pairs})
            else:
                nonincreasing['holds'] += 1
            many_blocks.append(raw)
        else:
            one_block.append(raw)

        if raw[-1] != 0:
            term_data = []
            for n in range(1, 4):
                term = tuple(harness.fs(raw, n))
                term_count = len(block_data(term)[1])
                relation = ('same' if term_count == count else
                            'increases' if term_count > count else 'decreases')
                limit_relations[n][relation] += 1
                term_data.append({'n': n, 'blocks': term_count,
                                  'relation': relation})
            limit_rows.append({'raw': spelling(raw), 'parent_blocks': count,
                               'terms': term_data})
        all_rows.append({'raw': spelling(raw), 'root_positions': list(roots),
                         'blocks': [spelling(block) for block in blocks]})

    report = {
        'range': '[P1,P2)', 'max_raw_length': MAXLEN,
        'criterion': 'one-based i: S[i]=2 and sp(i)=2',
        'counts': dict(counts),
        'multi_block_order': {'words': nonincreasing['words'],
                              'holds': nonincreasing['holds'],
                              'violations': nonincreasing['violations'],
                              'shortest_violations': sorted(
                                  order_failures,
                                  key=lambda x: (len(x['raw']), x['raw']))[:20]},
        'limit_term_block_relations': {
            str(n): dict(limit_relations[n]) for n in range(1, 4)},
        'shortest_one_block': [row(raw) for raw in one_block[:10]],
        'shortest_multi_block': [row(raw) for raw in many_blocks[:10]],
        'rows': all_rows,
        'limit_rows': limit_rows,
        'elapsed_seconds': round(time.monotonic() - started, 3),
    }
    OUT.write_text(json.dumps(report, ensure_ascii=False,
                              separators=(',', ':')) + '\n')
    print('counts', dict(counts))
    print('multi-block order', dict(nonincreasing),
          'shortest violations', report['multi_block_order']['shortest_violations'][:5])
    print('term block relations', report['limit_term_block_relations'])
    print('shortest one-block', report['shortest_one_block'])
    print('shortest multi-block', report['shortest_multi_block'])
    print('saved', OUT, OUT.stat().st_size, 'bytes',
          'elapsed', report['elapsed_seconds'])


if __name__ == '__main__':
    main()
