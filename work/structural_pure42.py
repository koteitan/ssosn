"""§42: structural purity of §39 pure words with the additive rule ADD.

ADD (prefix cut after A0, see notes §42): for a tail t = Z A0 X with X free of a trailing A0,
F(t) = F(Z A0) + F(X). A periodic block Q = Y A0 Y' therefore has
F(H Q^(m-1) V) = F(H Y A0) + F(Y' Y A0)·(m-2) + F(Y' V), with sup F(H Y A0) + F(Y' Y A0)·ω.
A tail H D with block W uses WD-i (H = W^j: F = w^w) or WD-ii (F = bump_last(F(H), k, F(R1 D))),
with the block shape checked for m = 1..3. The block W D W uses WD-iii (the epsilon chain).
Missing purity flags of base folds are computed on demand (token_tree.PURITY_ON_DEMAND).
An F counts as structural when it follows from A0-successor, S, ADD or WD, and the rule value
equals the decided (cached) value; a mismatch is recorded, not trusted.
"""

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
from ordinal import ONE, OMEGA, add, cmp, show
import evalord
import token_value as TV


class CaseTimeout(BaseException):
    pass


def _alarm(_signum, _frame):
    raise CaseTimeout()


def main():
    start = time.monotonic()
    runner.setup(0)
    T.PURITY_ON_DEMAND = True
    S.load_cache(runner.TAIL_CACHE)
    for k in [k for k, v in S._F_CACHE.items() if v[0] == 'timeout']:
        del S._F_CACHE[k]  # budgeted misses; ADD components are recomputed with a 2-s limit
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

    add_checks = collections.Counter()
    wd_checks = collections.Counter()
    wd_errors = []
    add_mismatch = []

    def value_of(tail, depth):
        key = (S.BASE, False, tail, depth)
        hit = S._F_CACHE.get(key)
        if hit is None or hit[0] != 'value':
            if hit is not None and hit[0] == 'timeout':
                del S._F_CACHE[key]
            signal.signal(signal.SIGALRM, _alarm)
            signal.setitimer(signal.ITIMER_REAL, 2.0)
            try:
                S.F(tail, depth)
            except CaseTimeout:
                raise RuntimeError('ADD component timeout')
            finally:
                signal.setitimer(signal.ITIMER_REAL, 0)
            hit = S._F_CACHE.get(key)
        if hit is None or hit[0] != 'value':
            raise RuntimeError('undecided ADD component')
        return hit[1]

    def check_add(key, parts, value, kind):
        decided = S._F_CACHE[key][1]
        add_checks[kind] += 1
        if cmp(value, decided):
            add_mismatch.append(dict(kind=kind, tail=S.tokens(key[2]), depth=key[3],
                                     decided=show(decided), add=show(value)))
            return False
        return all(f_structural((S.BASE, False, p, key[3])) for p in parts)

    def wrun_d(key, head, th):
        """T = H D with block W: T[m] = H W^(m-1). Rules WD-i and WD-ii (notes §42).
        The block shape of H W^m is checked for m = 1..3 only."""
        depth = key[3]
        W1 = S.seq(['W'])
        if all(x == 'W' for x in th):
            # WD-i: F(W^(j+1)) = (F(W^j)+1)·ω by rotation, so F(W^j D) = ω^ω.
            for m in range(1, 4):
                y = head + W1 * m
                h, q, v, _ = S.periodic(y, depth)
                x = ['W'] * (len(th) + m - 1)
                tq_m, th_m = S.tokens(q), S.tokens(h)
                # the same repetition split as (X A0)^n or as X (A0 X)^(n-1)
                if v or not ((th_m == tq_m == x + ['A0']) or
                             (th_m == x and tq_m == ['A0'] + x)):
                    return None
            value = TV.w(OMEGA)
            wd_checks['i'] += 1
            return check_value(key, (), value, 'wd-i')
        # WD-ii: H W^m has block A_k R1 W^(m-1); bumps at depth k absorb, so the sup
        # of the amounts (1+F(R1 W^(m-1)))·ω is F(R1 D).
        blocks = []
        for m in range(1, 4):
            h, q, v, _ = S.periodic(head + W1 * m, depth)
            b = S.s_block_k(q)
            if h != head + W1 * (m - 1) or b is None:
                return None
            blocks.append(b)
        k, r1 = blocks[0]
        if any(b != (k, r1 + W1 * i) for i, b in enumerate(blocks)):
            return None
        amount_tail = r1 + S.seq(['D'])
        value = TV.bump_last(value_of(head, depth), k, value_of(amount_tail, depth))
        wd_checks['ii'] += 1
        return check_value(key, (head, amount_tail), value, 'wd-ii')

    def eps_chain(key, head, block):
        """WD-iii: block W D W. With c_m = H Q^(m-1), the ADD/WD evaluator gives
        F(c_(m+2)) >= w^F(c_m) below the next epsilon after F(c_1) (checked for m = 1..3),
        so F(T) is that epsilon (notes §42)."""
        depth = key[3]
        S.ADD_WD_EXPERIMENT = True
        try:
            vals = [S.F(head + block * m, depth) for m in range(5)]
        finally:
            S.ADD_WD_EXPERIMENT = False
        eps = evalord.next_fp(ONE, vals[0])
        if not all(cmp(v, eps) < 0 for v in vals):
            return None
        # every second term passes w^x, so the terms are cofinal below eps
        if not all(cmp(b, TV.w(a)) >= 0 for a, b in zip(vals, vals[2:])):
            return None
        wd_checks['iii'] += 1
        return check_value(key, (), eps, 'wd-iii')

    def check_value(key, parts, value, kind):
        return check_add(key, parts, value, kind)

    def f_structural(key):
        hit = structural_f.get(key)
        if hit is not None:
            return hit
        structural_f[key] = False  # recursion guard
        base, flag, tail, depth = key
        result = S._F_CACHE.get(key)
        if result is None or result[0] != 'value':
            try:
                value_of(tail, depth)
            except Exception:
                return False
            result = S._F_CACHE.get(key)
        if not tail:
            answer = True
        elif tail[-3:] == S.A0:
            answer = f_structural((base, flag, tail[:-3], depth))
        else:
            tk = S.tokens(tail)
            inner = [i for i, x in enumerate(tk[:-1]) if x == 'A0']
            if inner:
                i = inner[-1]
                z, x = S.seq(tk[:i+1]), S.seq(tk[i+1:])
                try:
                    v = add(value_of(z, depth), value_of(x, depth))
                    answer = check_add(key, (z, x), v, 'split')
                except Exception:
                    answer = False
                structural_f[key] = answer
                return answer
            periodic = S._PERIODIC_CACHE.get((base, tail, depth))
            if periodic is None or periodic[0] != 'value':
                raise RuntimeError('missing periodic decomposition')
            head, block, end, terms = periodic[1]
            opened = S.s_block_k(block)
            tq = S.tokens(block)
            th, tv = S.tokens(head), S.tokens(end)
            consistent = (tq is not None and th is not None and tv is not None and
                          all(S.tokens(c) == th + tq * m + tv for m, c in enumerate(terms)))
            if opened is not None:
                _level, rest = opened
                answer = (f_structural((base, flag, head, depth)) and
                          f_structural((base, flag, rest, depth)))
            elif consistent and 'A0' in tq:
                j = tq.index('A0')
                y, y2 = tq[:j], tq[j+1:]
                first = S.seq(th + y + ['A0'])
                step = S.seq(y2 + y + ['A0'])
                try:
                    v = add(value_of(first, depth), S.mul_omega(value_of(step, depth)))
                    answer = check_add(key, (first, step), v, 'rotate')
                except Exception:
                    answer = False
            elif consistent and tq == ['W'] and not tv:
                try:
                    answer = wrun_d(key, head, th)
                except Exception as e:
                    wd_errors.append((S.tokens(tail), depth, type(e).__name__ + ': ' + str(e)))
                    answer = None
                if answer is None:  # the rule does not apply: a sampled root
                    sampled_roots.add(key)
                    answer = False
            elif consistent and tq == ['W', 'D', 'W'] and not tv:
                try:
                    answer = eps_chain(key, head, block)
                except Exception as e:
                    wd_errors.append((S.tokens(tail), depth, type(e).__name__ + ': ' + str(e)))
                    answer = None
                if answer is None:
                    sampled_roots.add(key)
                    answer = False
            else:
                sampled_roots.add(key)
                answer = False
        structural_f[key] = answer
        return answer

    f_counts = collections.Counter()
    for key, result in list(S._F_CACHE.items()):
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
        'direct_sampled_F_examples': [dict(tail=S.tokens(k[2]), depth=k[3], value=show(S._F_CACHE[k][1]))
            for k in sorted(sampled_roots,
                            key=lambda k: (len(k[2]), k[2], k[3]))],
        'order_bad': [dict(a=labels.get(a), b=labels.get(b)) for a, b in order_bad],
        'self_checked': self_checked,
        'self_skipped': self_skipped,
        'self_bad': [dict(parent=labels.get(s), n=n, term=t) for s, n, t in self_bad],
        'value_new_counts': {f'{a}:{b}': n for (a, b), n in new_counts.items()},
        'value_new_bad': [labels.get(s) for s in new_bad],
        'replay_disagreements': [dict(label=labels.get(s), raw=s, old=show(old[s][0]), new=show(replay[s][0])) for s in disagreements],
        'add_checks': dict(add_checks),
        'add_mismatch': add_mismatch,
        'wd_errors': wd_errors,
        'elapsed': time.monotonic() - start,
    }
    with gzip.open(HERE / 'structural-pure42.json.gz', 'wt', encoding='utf-8') as f:
        json.dump(report, f, ensure_ascii=False, separators=(',', ':'))
    with gzip.open(HERE / 'used-F42.json.gz', 'wt', encoding='utf-8') as f:
        json.dump([dict(tokens=S.tokens(k[2]), depth=k[3],
                        value=show(S._F_CACHE[k][1]),
                        source='structural' if f_structural(k) else 'sampled')
                   for k in sorted(used_f, key=lambda k: (k[3], len(k[2]), k[2]))],
                  f, ensure_ascii=False, separators=(',', ':'))
    print({k: v for k, v in report.items() if not k.endswith('_words')}, flush=True)


if __name__ == '__main__':
    main()
