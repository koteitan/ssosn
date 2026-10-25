"""§35 purity, order, value-new, and self-consistency measurement.

timeout 600 python3 work/pure_s35.py
"""
import collections
import gzip
import json
import os
import signal
import sys
import time
from pathlib import Path

sys.path[:0] = [os.path.dirname(os.path.abspath(__file__)),
                os.path.dirname(os.path.dirname(os.path.abspath(__file__)))]

import evalord
import harness
import std
import token_tree as T
from above_p_data26 import HERE, raw
from ordinal import cmp


class CaseTimeout(BaseException):
    pass


def _alarm(_signum, _frame):
    raise CaseTimeout()


def setup():
    T.CUT_COPY_ACTION_EXPERIMENT = True
    T.CONSISTENT_COPY_SEED_EXPERIMENT = True
    T.WD_AFTER_ITERATION_EXPERIMENT = False
    T.GENERAL_COPY_EXPERIMENT = False
    T.MOVABLE_ONE_EXPERIMENT = False
    T.RELTAIL_CAP_EXPERIMENT = False
    T.TAIL_S_EXPERIMENT = True
    T.TAIL_S_DEPTH_EXPERIMENT = False
    T.TAIL_S_MARKER_EXPERIMENT = True
    T.TAIL_S_E_EXPERIMENT = True
    T._TAIL_S_MODULE = None
    T._TAIL_S_ACTIVE = False
    T.PURITY_TRACKING = True
    T.PURE_BLOCKS.clear()
    T.PURE_BODIES.clear()
    T.PURE_VALUES.clear()
    T.value_tree.cache_clear()
    T.body_tree.cache_clear()
    T.block_tree.cache_clear()
    signal.signal(signal.SIGALRM, _alarm)


def main():
    start = time.monotonic()
    setup()
    with gzip.open(HERE / 'above-p26-data.json.gz', 'rt') as f:
        data = json.load(f)
    rows = {}
    spellings = collections.Counter()
    labels = {}
    pure_roots = set()
    for row in data['rows']:
        s = raw(row['tokens'])
        rows[s] = row['standard']
        spellings[s] += 1
        word = tuple(row['tokens'])
        if s not in labels or (len(word), word) < (len(labels[s]), labels[s]):
            labels[s] = word
        if row['standard'] and all(t in ('D', 'W') for t in word):
            pure_roots.add(s)
    ordered = sorted(rows, key=lambda s: (len(labels[s]), labels[s], s))
    memo = {}
    pure_reasons = collections.Counter()
    calls = 0

    def evaluate(s):
        nonlocal calls
        s = tuple(s)
        if s in memo:
            return memo[s]
        T._TAIL_S_ACTIVE = False
        T.TAIL_S_COUNTS = {'eligible': 0, 'decided': 0, 'undecided': 0}
        T.TAIL_S_MARKER_COUNTS = {'eligible': 0, 'decided': 0, 'undecided': 0}
        T.TAIL_S_E_COUNTS = {'eligible': 0, 'decided': 0, 'undecided': 0}
        # A value that does not finish promptly is unresolved and excluded
        # from the proven-pure set; this keeps the N=9 audit bounded.
        signal.setitimer(signal.ITIMER_REAL, 0.02)
        try:
            v = T.value(s)
            err = None
        except CaseTimeout:
            v = None
            err = '20-ms per-value timeout'
        except T.Unknown as e:
            v = None
            err = str(e)
        finally:
            signal.signal(signal.SIGALRM, signal.SIG_IGN)
            signal.setitimer(signal.ITIMER_REAL, 0)
            signal.signal(signal.SIGALRM, _alarm)
        counts = (T.TAIL_S_COUNTS.copy(), T.TAIL_S_MARKER_COUNTS.copy(),
                  T.TAIL_S_E_COUNTS.copy())
        pure = v is not None and T.PURE_VALUES.get(s, False)
        if not pure:
            if err is not None:
                pure_reasons['timeout' if 'timeout' in err else 'unknown'] += 1
            if v is not None and not any(x['undecided'] for x in counts):
                pure_reasons['inherited_impure'] += 1
            for name, c in zip(('tail_F', 'sibling_marker', 'E_sup'), counts):
                if c['undecided']:
                    pure_reasons[name] += c['undecided']
        calls += 1
        result = (v, pure, counts, err)
        memo[s] = result
        if calls % 1000 == 0:
            print('evaluated', calls, 'memo', len(memo),
                  'elapsed', round(time.monotonic() - start, 1), flush=True)
        return result

    # Pure roots are anchors by definition; the ordinary evaluator still
    # supplies and checks their values below.
    root_set = pure_roots
    vals = {}
    pure = {}
    for i, s in enumerate(ordered, 1):
        v, p, _, err = evaluate(s)
        if s in root_set and v is not None:
            p = True
        vals[s] = v
        pure[s] = p
    pure_standard = sorted((s for s in rows if rows[s] and pure[s]))
    pure_nonstandard = [s for s in rows if not rows[s] and pure[s]]

    # Adjacent order audit: these are the minimal local witnesses to any
    # failure of strict order on the lexicographically sorted pure standards.
    order_bad = []
    for a, b in zip(pure_standard, pure_standard[1:]):
        rel = cmp(vals[a], vals[b])
        if rel >= 0:
            order_bad.append(dict(a=a, a_tokens=labels[a], a_value=vals[a],
                                  b=b, b_tokens=labels[b], b_value=vals[b], relation=rel))

    # Newness relative only to pure standard words, with no outside partners.
    prefix_max = []
    best = None
    for i, s in enumerate(pure_standard):
        if best is None or cmp(vals[s], vals[pure_standard[best]]) > 0:
            best = i
        prefix_max.append(best)
    suffix_min = [None] * len(pure_standard)
    best = None
    for i in range(len(pure_standard) - 1, -1, -1):
        s = pure_standard[i]
        if best is None or cmp(vals[s], vals[pure_standard[best]]) < 0:
            best = i
        suffix_min[i] = best
    import bisect
    new_counts = collections.Counter()
    new_bad = []
    for s, actual in rows.items():
        if not pure[s] or vals[s] is None:
            continue
        lo = bisect.bisect_left(pure_standard, s)
        hi = bisect.bisect_right(pure_standard, s)
        lower_ok = lo == 0 or cmp(vals[pure_standard[prefix_max[lo-1]]], vals[s]) < 0
        upper_ok = hi == len(pure_standard) or cmp(vals[s], vals[pure_standard[suffix_min[hi]]]) < 0
        is_new = lower_ok and upper_ok
        new_counts[(actual, is_new)] += spellings[s]
        if actual != is_new and len(new_bad) < 100:
            new_bad.append(dict(tokens=labels[s], standard=actual, value=vals[s],
                                value_new=is_new,
                                lower=None if lo == 0 else pure_standard[prefix_max[lo-1]],
                                upper=None if hi == len(pure_standard) else pure_standard[suffix_min[hi]]))

    # Self-consistency only on pure parents whose four sampled real terms are
    # themselves pure. The term values are memoized by raw sequence.
    self_checked = 0
    self_skipped = 0
    self_bad = []
    limits = sorted((s for s in pure_standard if s[-1] != 0),
                    key=lambda s: (len(labels[s]), labels[s], s))
    for i, s in enumerate(limits, 1):
        terms = [harness.fs(s, n) for n in range(1, 5)]
        term_rows = [evaluate(t) for t in terms]
        if not all(p and v is not None for v, p, _, _ in term_rows):
            self_skipped += 1
            continue
        self_checked += 1
        for n, (t, (v, _, _, _)) in enumerate(zip(terms, term_rows), 1):
            if cmp(v, vals[s]) >= 0:
                self_bad.append(dict(parent=s, parent_tokens=labels.get(s), parent_value=vals[s],
                    n=n, term=t, term_tokens=labels.get(t), term_value=v,
                    standard=std.is_standard(t)))
        if i % 5000 == 0:
            print('self checked parents', i, 'eligible', self_checked,
                  'skipped', self_skipped, 'elapsed', round(time.monotonic()-start, 1), flush=True)
    report = dict(max_tokens=data['max_tokens'], candidates=len(rows), spellings=sum(spellings.values()),
        pure_unique=len([s for s in rows if pure[s]]), pure_spellings=sum(spellings[s] for s in rows if pure[s]),
        pure_standard_unique=len(pure_standard), pure_nonstandard_unique=len(pure_nonstandard),
        pure_standard_spellings=sum(spellings[s] for s in pure_standard),
        pure_nonstandard_spellings=sum(spellings[s] for s in pure_nonstandard),
        pure_reason_counts=dict(pure_reasons),
        order_violations=order_bad, order_violation_count=len(order_bad),
        value_new_counts={f'{k[0]}:{k[1]}': v for k,v in new_counts.items()},
        value_new_mismatches=new_bad,
        self_consistency_checked=self_checked,self_consistency_skipped=self_skipped,
        self_consistency_violations=self_bad,
        pure_roots=len(root_set),elapsed=time.monotonic()-start)
    out = HERE / 'pure-s35.json.gz'
    with gzip.open(out, 'wt', encoding='utf-8') as f:
        json.dump(report, f, ensure_ascii=False, separators=(',', ':'))
    print('RESULT', {k:v for k,v in report.items() if k not in
          ('order_violations','value_new_mismatches','self_consistency_violations')}, flush=True)
    print('ORDER', [(x['a_tokens'], x['a_value'], x['b_tokens'], x['b_value']) for x in order_bad[:20]], flush=True)
    print('VALUE_NEW', new_bad[:20], flush=True)
    print('SELF', self_bad[:20], flush=True)


if __name__ == '__main__':
    main()
