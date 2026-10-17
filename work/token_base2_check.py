"""Check binary-base laws and semantics against actual SSOS expansions."""
import argparse
import collections
import csv
import gzip
import itertools
import json
from pathlib import Path

import harness
import std
import evalord as E
import token_base2 as B
import token_value as V
from ordinal import cmp
from token_targets import pretty

HERE = Path(__file__).resolve().parent
SHAPES = ['202', '2012', '202012', '2012012', '20202', '20201202',
          '202012012', '20201201202', '202012012012', '20201202012',
          '2020120201202', '20201201202012', '202012012012012']


def probe(s):
    value = V.value(s)
    terms = []
    for n in range(1, 6):
        t = harness.fs(s, n)
        x = V.value(t)
        terms.append(dict(n=n, sequence=''.join(map(str, t)), ordinal=x,
                          rendered=pretty(x)))
    return dict(sequence=''.join(map(str, s)), ordinal=value, rendered=pretty(value), terms=terms)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('N', type=int, nargs='?', default=14)
    args = ap.parse_args()
    counts = collections.Counter()
    failures = []
    values = {}
    for size in range(args.N + 1):
        for bits in itertools.product((0, 1), repeat=size):
            s = (0, 0, 2) + B.emit(bits)
            if not std.is_standard(s):
                continue
            counts['standard'] += 1
            predicted_g, predicted_b = B.components(bits)
            cut = harness.Seq(s, 'new').cut()
            actual_g, actual_b = s[:cut], s[cut:-1] + (s[-1] - 1,)
            # Exact G,B equality certifies every n, not only five samples.
            if (actual_g, actual_b) != (predicted_g, predicted_b):
                failures.append(dict(sequence=s, kind='cut', actual=(actual_g, actual_b), predicted=(predicted_g, predicted_b)))
            else:
                counts['all_n_cut_certificate'] += 1
            parent = V.value(s)
            values[s] = parent
            xs = []
            for n in range(1, 6):
                t = actual_g + actual_b * n
                x = V.value(t)
                values[t] = x
                xs.append(x)
                if t != predicted_g + predicted_b * n:
                    failures.append(dict(sequence=s, n=n, kind='law'))
            if all(cmp(x, parent) < 0 for x in xs) and all(cmp(a, b) < 0 for a, b in zip(xs, xs[1:])):
                counts['local_order_pass'] += 1
            else:
                failures.append(dict(sequence=s, kind='local_order', parent=parent, terms=xs))
            if E.check(parent, xs, 3):
                counts['finite_calibration_pass'] += 1
            else:
                failures.append(dict(sequence=s, kind='finite_calibration', parent=parent, terms=xs))
        print(size, dict(counts), 'failures', len(failures), flush=True)
    ordered = sorted(values)
    violations = [dict(left=a, right=b, left_value=values[a], right_value=values[b])
                  for a, b in zip(ordered, ordered[1:]) if cmp(values[a], values[b]) >= 0]
    shapes = []
    for shape in SHAPES:
        s = tuple(map(int, '00' + shape))
        row = probe(s)
        bits = B.parse(s[2:])
        row.update(tokens=['A' if bit == 0 else 'D' for bit in bits],
                   components=B.components(bits), standard=std.is_standard(s))
        shapes.append(row)
    report = dict(N=args.N, counts=counts, failures=failures,
                  adjacent_violations=violations, valued_sequences=len(values), shapes=shapes)
    (HERE / 'token-base2-check.json').write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    with gzip.open(HERE / 'token-base2-values.tsv.gz', 'wt') as stream:
        writer = csv.writer(stream, delimiter='\t')
        writer.writerow(['sequence', 'value'])
        for s in ordered:
            writer.writerow([''.join(map(str, s)), pretty(values[s])])
    print('FINAL', dict(counts), 'values', len(values), 'failures', len(failures), 'order', len(violations))


if __name__ == '__main__':
    main()
