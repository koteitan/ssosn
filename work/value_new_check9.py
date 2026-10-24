"""Global value-new check using the complete positive/negative stdtok table.

timeout 300 python3 work/value_new_check9.py
No valuation rules are modified. Prefix maxima/suffix minima test against ALL
standard references, even if their values themselves fail the order audit.
"""
import argparse
import bisect
import collections
import itertools
import json
from pathlib import Path
import time

from stdtok_data import HERE, bit_rows, read_data
import token_laws as L
import token_value as TV
from ordinal import cmp, show


def standard_words(data):
    alphabet = data['alphabet']
    for length, bits in bit_rows(data):
        for code, tokens in enumerate(itertools.product(alphabet, repeat=length)):
            if bits[code >> 3] & (1 << (code & 7)):
                yield tokens


def run(data):
    started = time.monotonic()
    words = set(standard_words(data))
    references = sorted((L.seq(word), word, TV.index(word)) for word in words)
    keys = [row[0] for row in references]
    lower, upper = [], [None]*len(references)
    best = None
    for i, row in enumerate(references):
        if best is None or cmp(row[2], references[best][2]) > 0:
            best = i
        lower.append(best)
    best = None
    for i in range(len(references)-1, -1, -1):
        if best is None or cmp(references[i][2], references[best][2]) < 0:
            best = i
        upper[i] = best
    order_failures = [dict(left=a[1], right=b[1], left_value=show(a[2]),
                           right_value=show(b[2]))
                      for a,b in zip(references, references[1:]) if cmp(a[2],b[2]) >= 0]
    print(f'references={len(references)} adjacent_order_failures={len(order_failures)}', flush=True)
    counts, sides = collections.Counter(), collections.Counter()
    mismatches = []
    for prefix in sorted(words, key=lambda w:(len(w),w)):
        if len(prefix) >= data['max_tokens']:
            continue
        for token in data['alphabet']:
            word = prefix+(token,)
            raw, actual = L.seq(word), word in words
            try:
                value = TV.index(word)
            except TV.Unknown as error:
                counts[f'{actual}:unknown'] += 1
                mismatches.append(dict(tokens=word, standard=actual, unknown=str(error)))
                continue
            pos = bisect.bisect_left(keys, raw)
            hi = bisect.bisect_right(keys, raw)
            lo_ref = references[lower[pos-1]] if pos else None
            hi_ref = references[upper[hi]] if hi < len(keys) else None
            lo = lo_ref is None or cmp(lo_ref[2], value) < 0
            up = hi_ref is None or cmp(value, hi_ref[2]) < 0
            passes = lo and up
            counts[f'{actual}:{passes}'] += 1
            if not actual:
                sides[f'lower={lo},upper={up}'] += 1
            if actual != passes:
                mismatches.append(dict(tokens=word, raw=raw, standard=actual,
                    value_new=passes, value=show(value), lower_pass=lo, upper_pass=up,
                    lower_witness=None if lo_ref is None else dict(tokens=lo_ref[1],value=show(lo_ref[2])),
                    upper_witness=None if hi_ref is None else dict(tokens=hi_ref[1],value=show(hi_ref[2]))))
    # Confirm finite-alphabet gaps with the actual next standard sequence.
    # ceil and is_standard use the real expansion, never a value rule.
    import std
    boundary = []
    unresolved = []
    partner_words = set()
    for row in mismatches:
        if row['standard'] or 'unknown' in row:
            unresolved.append(row)
            continue
        word = tuple(row['tokens'])
        raw = L.seq(word)
        ceiling = std.ceil(raw)
        try:
            partner = TV.parse_tail(ceiling[4:])
            partner_value = TV.index(partner)
        except (TV.Unknown, TypeError) as error:
            row['boundary_error'] = str(error)
            unresolved.append(row)
            continue
        outside = any(t not in data['alphabet'] for t in partner) or len(partner)>data['max_tokens']
        verified = std.is_standard(ceiling)
        relation = cmp(TV.index(word), partner_value)
        certificate = dict(tokens=partner, raw=ceiling, value=show(partner_value),
                           standard_verified=verified, outside_table=outside,
                           outside_alphabet=sorted(set(partner)-set(data['alphabet'])),
                           candidate_vs_partner=relation)
        row['ceiling_partner'] = certificate
        if L.seq(partner)==ceiling and raw<ceiling and verified and outside and relation>=0:
            boundary.append(row)
            partner_words.add(partner)
        else:
            unresolved.append(row)
    # Include the certified external witnesses globally, including their mutual
    # order and their order against every original standard reference.
    extended = sorted(references+[(L.seq(w),w,TV.index(w)) for w in partner_words])
    extended_order_failures = [dict(left=a[1],right=b[1],left_value=show(a[2]),right_value=show(b[2]))
        for a,b in zip(extended,extended[1:]) if cmp(a[2],b[2])>=0]
    corrected = dict(counts)
    if boundary:
        corrected['False:True'] -= len(boundary)
        corrected['False:False'] += len(boundary)
    return dict(max_tokens=data['max_tokens'], alphabet=data['alphabet'],
                reference_count=len(references), includes_empty_reference=True,
                candidate_scope='nonempty words with standard immediate prefix',
                counts=dict(counts), nonstandard_sides=dict(sides),
                adjacent_order_failures=order_failures, mismatches=mismatches,
                confirmed_boundary_count=len(boundary),
                unique_boundary_partners=len(partner_words),
                boundary_corrected_counts=corrected,
                extended_reference_count=len(extended),
                extended_adjacent_order_failures=extended_order_failures,
                unresolved=unresolved,
                elapsed_seconds=time.monotonic()-started)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data', type=Path, default=HERE/'stdtok-9.json.gz')
    parser.add_argument('--out', type=Path, default=HERE/'value-new9.json')
    args = parser.parse_args()
    report = run(read_data(args.data))
    args.out.write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n')
    print('counts', report['counts'], 'sides', report['nonstandard_sides'], flush=True)
    print('mismatches',len(report['mismatches']),'elapsed',round(report['elapsed_seconds'],3),flush=True)
    print('confirmed_boundary',report['confirmed_boundary_count'],
          'unique_partners',report['unique_boundary_partners'],
          'corrected',report['boundary_corrected_counts'],
          'unresolved',len(report['unresolved']),
          'extended_order_failures',len(report['extended_adjacent_order_failures']),flush=True)
    for row in report['mismatches'][:20]:
        print(row,flush=True)


if __name__ == '__main__':
    main()
