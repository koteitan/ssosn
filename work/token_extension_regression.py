"""Confirm that the extension preserves the 870281 stored evaluator values."""
import csv
import gzip
import json
import time
from pathlib import Path

import token_value as V
from ordinal import show

HERE = Path(__file__).resolve().parent


def main():
    started = time.monotonic()
    changed = []
    count = 0
    with gzip.open(HERE / 'token-comparison-final-values.tsv.gz', 'rt') as stream:
        for row in csv.DictReader(stream, delimiter='\t'):
            count += 1
            try:
                result = show(V.value(tuple(map(int, row['sequence']))))
            except V.Unknown as exc:
                result = 'unresolved: ' + str(exc)
            if result != row['value']:
                changed.append(dict(sequence=row['sequence'], before=row['value'], after=result))
            if count % 100000 == 0:
                print(count, 'changed', len(changed), flush=True)
    report = dict(reference='work/token-comparison-final-values.tsv.gz', count=count,
                  changed=changed, seconds=time.monotonic()-started,
                  BOUNDARY_EXPERIMENT=V.BOUNDARY_EXPERIMENT)
    (HERE / 'token-extension-regression.json').write_text(
        json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    print('FINAL', count, 'changed', len(changed), flush=True)


if __name__ == '__main__':
    main()
