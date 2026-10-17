"""Diagnostic: replace only blocks containing consecutive W with token values.

This mixes evaluators to trace the cause of old-table errors; it is not an
independent semantic validation. rule6.py itself is not changed.
"""
import collections
import json
import signal
from pathlib import Path

import rule6 as R
import token_value as V
from ordinal import cmp

HERE = Path(__file__).resolve().parent


class Timeout(Exception):
    pass


def alarm(*_):
    raise Timeout


def main():
    R.USE_LIFT = R.EXT = R.MORE = True
    R.EXT121 = R.EXT121E = R.NOREGION = R.RELLIFT = False
    R.MAXD = 6
    original_rules = R.rules
    hits = set()

    def patched(u):
        try:
            tokens = V.parse_tail(tuple(u)[2:]) if tuple(u)[:2] == (2, 1) else ()
        except V.Unknown:
            tokens = ()
        if any(a == b == 'W' for a, b in zip(tokens, tokens[1:])):
            hits.add(tokens)
            return V.block_value(tuple(u))
        return original_rules(u)

    R.rules = patched
    signal.signal(signal.SIGALRM, alarm)
    source = json.loads((HERE / 'toktable2-comparison.json').read_text())
    rows = []
    for ref in source['rows']:
        if ref['status'] != 'differ':
            continue
        s = tuple(map(int, ref['sequence']))
        signal.alarm(5)
        try:
            x, taint = R.value(s)
            status = 'tainted/missing' if taint or x is None else 'agree' if cmp(x, V.value(s)) == 0 else 'differ'
        except Timeout:
            x = None
            status = 'timeout'
            R.st['depth'] = 0
        finally:
            signal.alarm(0)
        rows.append(dict(sequence=ref['sequence'], status=status, ordinal=x))
    report = dict(method=__doc__, counts=collections.Counter(r['status'] for r in rows),
                  intercepted_token_strings=sorted(hits), rows=rows)
    (HERE / 'toktable2-ww-probe.json').write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    print(dict(report['counts']), 'intercepted blocks', len(hits))


if __name__ == '__main__':
    main()
