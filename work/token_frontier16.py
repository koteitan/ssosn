"""Bounded discovery only: finite real-term sup guesses above the token boundary.

Guesses are not inserted into token_value. No rule6, lower, or hypothesis II.
The production evaluator remains a structural evaluator, not this recursion.
"""
import collections
import json
import signal
import time
from pathlib import Path

import harness
import conj2
import evalord as E
import token_value as V
from ordinal import ONE, ZERO, add, nat, succ, w
from token_targets import pretty

HERE = Path(__file__).resolve().parent


class Limit(Exception):
    pass


def alarm(*_):
    raise Limit


def main():
    signal.signal(signal.SIGALRM, alarm)
    memo = {}
    counters = collections.Counter()

    def block(u, depth):
        try:
            return V.block_value(u)
        except V.Unknown:
            return value((0, 0) + u, depth)

    def body(s, depth):
        result = ZERO
        for unit in conj2.units(s):
            if unit == (0,):
                x = ONE
            elif unit == (2,):
                x = V.E0
            else:
                t = conj2.T(unit)
                x = block(unit, depth) if t == unit else w(add(ONE, body(t, depth)))
            result = add(result, x)
        return result

    def value(s, depth):
        counters['calls'] += 1
        try:
            return V.value(s)
        except V.Unknown:
            pass
        if s in memo:
            return memo[s]
        if depth <= 0 or len(s) > 180:
            raise V.Unknown(('discovery depth/length budget', len(s), depth, ''.join(map(str,s))[:180]))
        if s[-1] == 0:
            return succ(value(s[:-1], depth))
        if len(s) > 3 and conj2.units(s[2:]) != [s[2:]]:
            return add(nat(2), body(s[2:], depth))
        if len(s) > 3 and conj2.T(s[2:]) != s[2:]:
            return add(nat(2), body(s[2:], depth))
        cut = harness.Seq(s, 'new').cut()
        g, b = s[:cut], s[cut:-1] + (s[-1] - 1,)
        xs = []
        for n in range(1, 6):
            xs.append(value(g + b * n, depth - 1))
        x = E.sup(xs)
        if x is None:
            raise V.Unknown('no finite sup candidate')
        memo[s] = x
        counters['guesses'] += 1
        return x

    rows = []
    for text in ['00210202', '00210202102', '0021021', '00211', '0022', '003']:
        for depth in [8, 24, 64]:
            started = time.monotonic()
            signal.alarm(10)
            try:
                x = value(tuple(map(int, text)), depth)
                status, reason = 'finite-sup guess', None
            except (V.Unknown, Limit) as exc:
                x = None
                status, reason = 'unresolved', str(exc) or '10 second timeout'
            finally:
                signal.alarm(0)
            row = dict(sequence=text, depth=depth, status=status, reason=reason,
                       ordinal=x, rendered=pretty(x) if x is not None else None,
                       seconds=time.monotonic()-started, counters=dict(counters))
            rows.append(row)
            print(text, depth, status, row['rendered'] or reason, flush=True)
            if x is not None:
                break
    guesses = [dict(sequence=''.join(map(str,s)), ordinal=x, rendered=pretty(x))
               for s,x in sorted(memo.items(), key=lambda item:(len(item[0]),item[0]))]
    (HERE / 'token-frontier16.json').write_text(json.dumps(dict(method=__doc__, rows=rows, guesses=guesses), ensure_ascii=False, indent=2) + '\n')
    print('shortest guesses',[(row['sequence'],row['rendered']) for row in guesses[:12]],flush=True)


if __name__ == '__main__':
    main()
