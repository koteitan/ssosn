"""Compare the regenerated legacy table with the independent token evaluator."""
import collections
import csv
import json
import pickle
from pathlib import Path

import token_value as V
from token_targets import pretty
from ordinal import cmp

HERE = Path(__file__).resolve().parent
REGION = tuple(map(int, '0021012101202'))


def main():
    with (HERE / 'toktable2.pkl').open('rb') as stream:
        table = pickle.load(stream)
    rows = []
    counts = collections.defaultdict(collections.Counter)
    for old, (tokens, body) in table.items():
        sequence = (0, 0) + body
        region = 'region' if sequence[:len(REGION)] == REGION else 'outside'
        try:
            new = V.value(sequence)
            status = 'agree' if cmp(old, new) == 0 else 'differ'
            reason = None
        except V.Unknown as exc:
            new = None
            status = 'unresolved'
            reason = str(exc)
        counts[region][status] += 1
        rows.append(dict(sequence=''.join(map(str, sequence)), tokens=tokens,
                         region=region, status=status, old=old, new=new,
                         old_rendered=pretty(old),
                         new_rendered=pretty(new) if new is not None else None,
                         reason=reason))
    rows.sort(key=lambda row: row['sequence'])
    known = [row for row in rows if row['new'] is not None]
    violations = [dict(left=a['sequence'], right=b['sequence'])
                  for a, b in zip(known, known[1:])
                  if cmp(a['new'], b['new']) >= 0]
    legacy_violations = [dict(left=a['sequence'], right=b['sequence'])
                         for a, b in zip(rows, rows[1:])
                         if cmp(a['old'], b['old']) >= 0]
    report = dict(method='fresh legacy toksearch2, five seconds per value; independent token evaluator comparison',
                  unique_legacy_values=len(table), counts=dict(counts),
                  evaluator_adjacent_violations=violations,
                  legacy_adjacent_violations=legacy_violations, rows=rows)
    (HERE / 'toktable2-comparison.json').write_text(
        json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    with (HERE / 'toktable2-comparison.tsv').open('w') as stream:
        writer = csv.writer(stream, delimiter='\t')
        writer.writerow(['sequence', 'tokens', 'region', 'status', 'legacy', 'token_value'])
        for row in rows:
            writer.writerow([row['sequence'], ' '.join(row['tokens']), row['region'],
                             row['status'], row['old_rendered'], row['new_rendered']])
    print(json.dumps(dict(unique=len(table), counts=dict(counts),
                          new_order_violations=len(violations),
                          legacy_order_violations=len(legacy_violations)), ensure_ascii=False))


if __name__ == '__main__':
    main()
