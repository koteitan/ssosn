"""Check real terms 1..8 of sampled F values used by §39 pure words."""

import collections
import argparse
import gzip
import json
import signal
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import evalord
import pure_s39 as runner
import std
import tail_symbolic as S
from above_p_data26 import HERE
from ordinal import cmp, show


class CaseTimeout(BaseException):
    pass


def _alarm(_signum, _frame):
    raise CaseTimeout()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seconds', type=float, default=1.0)
    args = parser.parse_args()
    start = time.monotonic()
    runner.setup(0)
    S.load_cache(runner.TAIL_CACHE)
    with gzip.open(HERE / 'used-F40.json.gz', 'rt') as f:
        used = json.load(f)
    seen = set()
    direct = set()

    def visit(key):
        if key in seen:
            return
        seen.add(key)
        base, flag, tail, depth = key
        if not tail:
            return
        if tail[-3:] == S.A0:
            visit((base, flag, tail[:-3], depth))
            return
        row = S._PERIODIC_CACHE.get((base, tail, depth))
        if row is None or row[0] != 'value':
            raise RuntimeError('missing periodic decomposition')
        head, block, _end, _terms = row[1]
        opened = S.s_block_k(block)
        if opened is None:
            direct.add(key)
        else:
            _level, rest = opened
            visit((base, flag, head, depth))
            visit((base, flag, rest, depth))

    for row in used:
        visit((S.BASE, False, S.seq(row['tokens']), row['depth']))
    ordered = sorted(direct, key=lambda k: (len(S.tokens(k[2])),
                                          S.tokens(k[2]), k[3]))
    signal.signal(signal.SIGALRM, _alarm)
    records = []
    counts = collections.Counter()
    for i, key in enumerate(ordered, 1):
        base, flag, tail, depth = key
        parent = S._F_CACHE[key][1]
        result = dict(tokens=S.tokens(tail), depth=depth,
                      parent=show(parent),
                      standard=std.is_standard(S._base_at_depth(depth) +
                                               S.seq(S._shift_names(S.tokens(tail), depth))),
                      terms=[], first_failure=None)
        decided_values = []
        for n in range(1, 9):
            signal.setitimer(signal.ITIMER_REAL, args.seconds)
            try:
                term = S.induced(tail, n, depth)
                value = S.F(term, depth)
                relation = cmp(value, parent)
                item = dict(n=n, tokens=S.tokens(term), value=show(value),
                            relation=relation)
                result['terms'].append(item)
                decided_values.append(value)
                counts['decided_terms'] += 1
                if relation >= 0:
                    result['first_failure'] = item
                    counts['failure_roots'] += 1
                    print('FAIL', result['tokens'], depth, n,
                          result['parent'], item['value'], flush=True)
                    break
            except (CaseTimeout, Exception) as e:
                result['terms'].append(dict(n=n, undecided=type(e).__name__ + ': ' + str(e)))
                counts['undecided_terms'] += 1
                break
            finally:
                signal.signal(signal.SIGALRM, signal.SIG_IGN)
                signal.setitimer(signal.ITIMER_REAL, 0)
                signal.signal(signal.SIGALRM, _alarm)
        if result['first_failure'] is None and len(result['terms']) == 8 and \
                all('relation' in x for x in result['terms']):
            counts['eight_decided_below'] += 1
            prefix_candidates = []
            for width in range(3, 9):
                guess = evalord.sup(decided_values[:width])
                prefix_candidates.append(None if guess is None else
                                         dict(n=width, value=show(guess),
                                              relation=cmp(guess, parent)))
            result['prefix_candidates'] = prefix_candidates
            if any(x is not None and x['relation'] != 0
                   for x in prefix_candidates):
                counts['candidate_changed'] += 1
                print('CANDIDATE_CHANGED', result['tokens'], depth,
                      result['parent'], prefix_candidates, flush=True)
        records.append(result)
        if i % 100 == 0:
            print('checked', i, 'of', len(ordered),
                  'elapsed', round(time.monotonic() - start, 1), flush=True)
    report = dict(roots=len(ordered), used_F=len(used), seconds=args.seconds,
                  counts=dict(counts), elapsed=time.monotonic() - start,
                  records=records)
    with gzip.open(HERE / 'sample-sup-audit41.json.gz', 'wt', encoding='utf-8') as f:
        json.dump(report, f, ensure_ascii=False, separators=(',', ':'))
    print('RESULT', {k: v for k, v in report.items() if k != 'records'}, flush=True)


if __name__ == '__main__':
    main()
