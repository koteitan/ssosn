"""Audit §39 pure words after excluding any sampled-sup F dependency."""

import bisect
import collections
import gzip
import json
import pickle
import signal
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import harness
import std
import tail_symbolic as S
import token_tree as T
import pure_s39 as runner
from above_p_data26 import HERE, raw
from ordinal import cmp, show


class CaseTimeout(BaseException):
    pass


def _alarm(_signum, _frame):
    raise CaseTimeout()


def main():
    start = time.monotonic()
    runner.setup(0)
    S.load_cache(runner.TAIL_CACHE)
    with gzip.open(HERE / 'above-p26-data.json.gz', 'rt') as f:
        data = json.load(f)
    labels = {}
    standard = {}
    spellings = collections.Counter()
    anchors = set()
    for row in data['rows']:
        s = raw(row['tokens'])
        names = tuple(row['tokens'])
        standard[s] = row['standard']
        spellings[s] += 1
        if s not in labels or (len(names), names) < (len(labels[s]), labels[s]):
            labels[s] = names
        if row['standard'] and all(x in ('D', 'W') for x in names):
            anchors.add(s)
    T.PURE_ANCHOR_TOKENS.clear()
    T.PURE_ANCHOR_TOKENS.update(labels[s] for s in anchors)
    with gzip.open(runner.WORD_CACHE, 'rb') as f:
        old = pickle.load(f)['values']

    structural_f = {}
    sampled_roots = set()

    def f_structural(key):
        hit = structural_f.get(key)
        if hit is not None:
            return hit
        base, flag, tail, depth = key
        result = S._F_CACHE.get(key)
        if result is None or result[0] != 'value':
            raise RuntimeError('missing decided F dependency')
        if not tail:
            answer = True
        elif tail[-3:] == S.A0:
            answer = f_structural((base, flag, tail[:-3], depth))
        else:
            periodic = S._PERIODIC_CACHE.get((base, tail, depth))
            if periodic is None or periodic[0] != 'value':
                raise RuntimeError('missing periodic decomposition')
            head, block, _end, _terms = periodic[1]
            opened = S.s_block_k(block)
            if opened is None:
                sampled_roots.add(key)
                answer = False
            else:
                _level, rest = opened
                answer = (f_structural((base, flag, head, depth)) and
                          f_structural((base, flag, rest, depth)))
        structural_f[key] = answer
        return answer

    f_counts = collections.Counter()
    for key, result in S._F_CACHE.items():
        if result[0] == 'value':
            f_counts['structural' if f_structural(key) else 'sampled'] += 1

    seen = set()
    original_F = S.F

    def traced_F(t, depth=0):
        seen.add((S.BASE, S.FIXEDPOINT_SUP_EXPERIMENT, t, depth))
        return original_F(t, depth)

    S.F = traced_F
    signal.signal(signal.SIGALRM, _alarm)
    replay = {}
    disagreements = []

    def evaluate(s):
        s = tuple(s)
        if s in replay:
            return replay[s]
        seen.clear()
        T._TAIL_S_ACTIVE = False
        T.PURE_BLOCKS.clear()
        T.PURE_BODIES.clear()
        T.PURE_VALUES.clear()
        T.PURE_FOLDS.clear()
        T.value_tree.cache_clear()
        T.body_tree.cache_clear()
        T.block_tree.cache_clear()
        signal.setitimer(signal.ITIMER_REAL, 2.0)
        try:
            value = T.value(s)
            pure = T.PURE_VALUES.get(s, False) or s in anchors
            provenance = pure and all(f_structural(k) for k in seen)
            result = (value, provenance, tuple(seen), None)
        except (CaseTimeout, Exception) as e:
            result = (None, False, tuple(seen), type(e).__name__ + ': ' + str(e))
        finally:
            signal.signal(signal.SIGALRM, signal.SIG_IGN)
            signal.setitimer(signal.ITIMER_REAL, 0)
            signal.signal(signal.SIGALRM, _alarm)
        replay[s] = result
        oldrow = old.get(s)
        if oldrow and oldrow[0] is not None and result[0] is not None and cmp(oldrow[0], result[0]):
            disagreements.append(s)
        return result

    old_pure = sorted(s for s, row in old.items()
                      if s in standard and row[0] is not None and
                      (row[1] or s in anchors))
    used_f = set()
    for i, s in enumerate(old_pure, 1):
        evaluate(s)
        used_f.update(replay[s][2])
        if i % 1000 == 0:
            print('replayed', i, 'of', len(old_pure),
                  'elapsed', round(time.monotonic() - start, 1), flush=True)
    structural = sorted(s for s in old_pure if replay[s][1])
    used_f_counts = collections.Counter('structural' if f_structural(k) else 'sampled'
                                        for k in used_f)
    ss = [s for s in structural if standard[s]]
    ns = [s for s in structural if not standard[s]]
    order_bad = [(a, b) for a, b in zip(ss, ss[1:])
                 if cmp(replay[a][0], replay[b][0]) >= 0]
    limits = [s for s in ss if s[-1] != 0]
    self_checked = 0
    self_skipped = 0
    self_bad = []
    for s in limits:
        terms = [tuple(harness.fs(s, n)) for n in range(1, 5)]
        vals = [evaluate(t) for t in terms]
        if not all(row[1] for row in vals):
            self_skipped += 1
            continue
        self_checked += 1
        for n, (term, row) in enumerate(zip(terms, vals), 1):
            if cmp(row[0], replay[s][0]) >= 0:
                self_bad.append((s, n, term))

    new_counts = collections.Counter()
    new_bad = []
    for s in structural:
        i = bisect.bisect_left(ss, s)
        j = bisect.bisect_right(ss, s)
        low = i == 0 or all(cmp(replay[t][0], replay[s][0]) < 0 for t in ss[:i])
        high = j == len(ss) or all(cmp(replay[s][0], replay[t][0]) < 0 for t in ss[j:])
        is_new = low and high
        new_counts[(standard[s], is_new)] += spellings[s]
        if standard[s] != is_new:
            new_bad.append(s)
    report = {
        'old_pure': len(old_pure),
        'F_decided': dict(f_counts),
        'F_direct_sampled_roots': len(sampled_roots),
        'F_used_by_pure': dict(used_f_counts),
        'structural_unique': len(structural),
        'structural_spellings': sum(spellings[s] for s in structural),
        'structural_standard_unique': len(ss),
        'structural_standard_spellings': sum(spellings[s] for s in ss),
        'structural_nonstandard_unique': len(ns),
        'structural_nonstandard_spellings': sum(spellings[s] for s in ns),
        'sampled_dependent_pure': len(old_pure) - len(structural),
        'structural_words': [labels[s] for s in structural],
        'sampled_dependent_words': [labels[s] for s in old_pure if s not in structural],
        'sampled_dependent_examples': [labels[s] for s in sorted(
            (s for s in old_pure if s not in structural),
            key=lambda s: (len(labels[s]), labels[s], s))[:20]],
        'direct_sampled_F_examples': [dict(tail=S.tokens(k[2]), depth=k[3])
            for k in sorted(sampled_roots,
                            key=lambda k: (len(k[2]), k[2], k[3]))[:20]],
        'order_bad': [dict(a=labels.get(a), b=labels.get(b)) for a, b in order_bad],
        'self_checked': self_checked,
        'self_skipped': self_skipped,
        'self_bad': [dict(parent=labels.get(s), n=n, term=t) for s, n, t in self_bad],
        'value_new_counts': {f'{a}:{b}': n for (a, b), n in new_counts.items()},
        'value_new_bad': [labels.get(s) for s in new_bad],
        'replay_disagreements': [labels.get(s) for s in disagreements],
        'elapsed': time.monotonic() - start,
    }
    with gzip.open(HERE / 'structural-pure40.json.gz', 'wt', encoding='utf-8') as f:
        json.dump(report, f, ensure_ascii=False, separators=(',', ':'))
    with gzip.open(HERE / 'used-F40.json.gz', 'wt', encoding='utf-8') as f:
        json.dump([dict(tokens=S.tokens(k[2]), depth=k[3],
                        value=show(S._F_CACHE[k][1]),
                        source='structural' if f_structural(k) else 'sampled')
                   for k in sorted(used_f, key=lambda k: (k[3], len(k[2]), k[2]))],
                  f, ensure_ascii=False, separators=(',', ':'))
    print(report, flush=True)


if __name__ == '__main__':
    main()
