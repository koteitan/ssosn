"""§43: bounded audit of P1_V_BITS_EXPERIMENT on longer standard forms above P V.

Run: timeout 900 python3 work/p1_v_ext43.py --maxlen 21
Standard forms in [P V, P1) are extended from standard prefixes only (digits 0..3),
as in p1_tokens43.py.  For every form: decided?  successor = parent+1?  for limits,
n=1..10 terms decided and below the parent, sampled sup (4 vs 10 terms) agreement,
and adjacent order inversions.  A sampled sup is evidence only.
Also records every W/D/V copy word whose bits rank was used.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE.parent)]

import std
import harness
import evalord
import token_value
import v_bits43
from ordinal import lt, show, succ
from p1_tokens43 import P

PV = P + (0, 2, 1)
P1 = P + (1,)


def digits(raw):
    return ''.join(map(str, raw))


def enumerate_forms(maxlen):
    out = [PV]
    frontier = [PV]
    while frontier:
        nxt = []
        for s in frontier:
            if len(s) >= maxlen:
                continue
            for d in range(0, 4):
                c = s + (d,)
                if c < P1 and std.is_standard(c):
                    nxt.append(c)
        out += nxt
        frontier = nxt
    return sorted(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--maxlen', type=int, default=21)
    ap.add_argument('--budget', type=float, default=700)
    ap.add_argument('--raw', action='store_true', help='old value of 00+bits as copy rank')
    args = ap.parse_args()
    t0 = time.monotonic()
    forms = enumerate_forms(args.maxlen)
    t_enum = time.monotonic() - t0
    if args.raw:
        from p1_v_fold43 import run_values
        baseline = run_values(False, forms)
    else:
        baseline = None
    used = Counter()
    if args.raw:
        import v_raw43
        orig = v_raw43.rank
    else:
        orig = v_bits43.rank

    def rank(c):
        used[''.join(c)] += 1
        return orig(c)
    if args.raw:
        v_raw43.rank = rank
    else:
        v_bits43.rank = rank
    token_value.P1_ROOT_EXPERIMENT = True
    token_value.P1_V_BITS_EXPERIMENT = not args.raw
    token_value.P1_V_RAW_EXPERIMENT = args.raw

    def cand(raw):
        try:
            return token_value.value(raw)
        except token_value.Unknown:
            return None
    vals = {s: cand(s) for s in forms}
    counts = Counter(forms=len(forms))
    issues = []
    if baseline is not None:
        for s in forms:
            old = baseline[digits(s)]
            new = vals[s]
            if old is not None:
                counts['old_decided'] += 1
                if new is None or show(new) != old:
                    counts['old_value_changed'] += 1
                    if len(issues) < 100:
                        issues.append({'kind': 'old_changed', 'raw': digits(s),
                                       'old': old, 'new': None if new is None else show(new)})
    by_len = Counter(len(s) for s in forms)
    started = time.monotonic()
    for s in forms:
        v = vals[s]
        if v is None:
            counts['unknown'] += 1
            if len(issues) < 100:
                issues.append({'kind': 'unknown', 'raw': digits(s)})
            continue
        counts['decided'] += 1
        if s[-1] == 0:
            p = vals.get(s[:-1]) or cand(s[:-1])
            if p is None:
                counts['succ_parent_unknown'] += 1
            elif v == succ(p):
                counts['succ_agree'] += 1
            else:
                counts['succ_differ'] += 1
                issues.append({'kind': 'successor', 'raw': digits(s)})
            continue
        counts['limit'] += 1
        if time.monotonic() - started > args.budget:
            counts['limit_budget_skipped'] += 1
            continue
        xs = []
        for n in range(1, 11):
            x = cand(harness.fs(s, n))
            xs.append(x)
            if x is None:
                break
        ok = len(xs) == 10 and all(x is not None for x in xs)
        counts['limit_all10' if ok else 'limit_term_unknown'] += 1
        if not ok and len(issues) < 100:
            issues.append({'kind': 'term_unknown', 'raw': digits(s), 'n': len(xs)})
        if any(x is not None and not lt(x, v) for x in xs):
            counts['limit_term_not_below'] += 1
            issues.append({'kind': 'term_not_below', 'raw': digits(s), 'value': show(v)})
        if ok:
            s4, s10 = evalord.sup(xs[:4]), evalord.sup(xs)
            if s4 is None or s10 is None or s4 != s10:
                counts['limit_sup_undecided'] += 1
                if len(issues) < 100:
                    issues.append({'kind': 'sup_undecided', 'raw': digits(s), 'value': show(v)})
            elif s10 == v:
                counts['limit_sup_agree'] += 1
            else:
                counts['limit_sup_differ'] += 1
                issues.append({'kind': 'sup_differ', 'raw': digits(s),
                               'value': show(v), 'sup10': show(s10)})
    dec = [(s, vals[s]) for s in forms if vals[s] is not None]
    for (a, x), (b, y) in zip(dec, dec[1:]):
        if not lt(x, y):
            counts['adjacent_order_bad'] += 1
            issues.append({'kind': 'order', 'left': digits(a), 'right': digits(b),
                           'lv': show(x), 'rv': show(y)})
    words = sorted(used, key=lambda w: (len(w), w))
    ranks = []
    for w in words:
        try:
            rv = show(orig(tuple(w)))
        except ValueError:
            rv = None
        ranks.append({'word': w, 'bits': digits(v_bits43.bits(tuple(w))), 'rank': rv})
    report = {'flag': 'P1_ROOT_EXPERIMENT + ' + ('P1_V_RAW_EXPERIMENT' if args.raw else 'P1_V_BITS_EXPERIMENT'), 'maxlen': args.maxlen,
              'by_len': {str(k): by_len[k] for k in sorted(by_len)},
              'enum_seconds': round(t_enum, 1), 'counts': dict(counts),
              'issues': issues[:300],
              'bits_words': ranks}
    output = f'p1-v-raw-ext43-{args.maxlen}.json' if args.raw else f'p1-v-ext43-{args.maxlen}.json'
    (HERE / output).write_text(
        json.dumps(report, ensure_ascii=False, indent=1) + '\n')
    print('by_len', report['by_len'], 'enum', round(t_enum, 1), 's')
    print('counts', dict(counts))
    print('issues', issues[:10])
    print('bits words', len(words))
    for r in report['bits_words'][:60]:
        print(' ', r['word'], r['bits'], r['rank'])


if __name__ == '__main__':
    main()
