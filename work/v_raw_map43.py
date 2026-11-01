"""Compare v2 copy ranks with the old evaluator on the 408 used bit words.

Run: timeout 60 python3 work/v_raw_map43.py
The old evaluator's number on a non-standard raw sequence is only diagnostic.
"""
from collections import Counter, defaultdict
from functools import cmp_to_key
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE.parent)]

import std
import v_bits43
import v_raw43
from ordinal import cmp, show


def main():
    data = json.loads((HERE / 'p1-v-ext43-20.json').read_text())
    counts = Counter()
    rows = []
    pairs = defaultdict(set)
    for item in data['bits_words']:
        word = tuple(item['word'])
        bits = v_bits43.bits(word)
        raw = (0, 0) + bits
        bit_rank = v_bits43.rank(word)
        standard = std.is_standard(raw)
        counts['raw_standard' if standard else 'raw_nonstandard'] += 1
        try:
            raw_rank = v_raw43.rank(word)
        except ValueError:
            raw_rank = None
        if raw_rank is None:
            counts['raw_unknown'] += 1
            counts['standard_unknown' if standard else 'nonstandard_unknown'] += 1
        else:
            counts['raw_decided'] += 1
            counts['standard_decided' if standard else 'nonstandard_decided'] += 1
            relation = cmp(bit_rank, raw_rank)
            counts['equal' if relation == 0 else 'bit_less_raw' if relation < 0 else
                   'bit_greater_raw'] += 1
            pairs[bit_rank].add(raw_rank)
        rows.append({'word': item['word'], 'bits': ''.join(map(str, bits)),
                     'raw': ''.join(map(str, raw)), 'raw_standard': standard,
                     'bit_rank': show(bit_rank),
                     'raw_rank': None if raw_rank is None else show(raw_rank)})
    unique = [(a, next(iter(bs))) for a, bs in pairs.items() if len(bs) == 1]
    counts['distinct_bit_ranks_decided'] = len(pairs)
    counts['same_bit_rank_multiple_raw'] = sum(len(bs) > 1 for bs in pairs.values())
    unique.sort(key=cmp_to_key(lambda x, y: cmp(x[0], y[0])))
    order_bad = [(show(a[0]), show(b[0]), show(a[1]), show(b[1]))
                 for a, b in zip(unique, unique[1:]) if cmp(a[1], b[1]) >= 0]
    counts['adjacent_rank_map_bad'] = len(order_bad)
    report = {'counts': dict(counts), 'rows': rows,
              'distinct_pairs': [{'bit_rank': show(a), 'raw_rank': show(b)} for a,b in unique],
              'rank_map_order_bad': order_bad}
    (HERE / 'v-raw-map43.json').write_text(
        json.dumps(report, ensure_ascii=False, indent=1) + '\n')
    print('counts', dict(counts))
    print('rank_map_order_bad', order_bad[:5])
    print('first_differences', [r for r in rows if r['raw_rank'] is not None and
                               r['bit_rank'] != r['raw_rank']][:8])


if __name__ == '__main__':
    main()
