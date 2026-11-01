"""§43: audit of the flagged internal-V copy rank (P1_V_FOLD_EXPERIMENT) on [P,P1).

Run: timeout 900 python3 work/p1_v_fold43.py [--bits|--raw]
  default: P1_V_FOLD_EXPERIMENT (Codex's next-epsilon V rank) -> p1-v-fold43.json
  --bits:  P1_V_BITS_EXPERIMENT (v_bits43 rank, fresh E1 above offset) -> p1-v-bits43.json
  --raw:   P1_V_RAW_EXPERIMENT (old value of 00+bits, where defined) -> p1-v-raw43.json
The baseline (P1_ROOT_EXPERIMENT only) and the V-fold values are computed in two
separate processes, so no cache carries over between the flags.  A finite sampled
sup is evidence only; an undecided sup is never counted as agreement.
"""
from collections import Counter
import json
import multiprocessing as mp
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE.parent)]


def digits(raw):
    return ''.join(map(str, raw))


def load_words():
    data = json.loads((HERE / 'p1-tokens43-18.json').read_text())
    return sorted((tuple(map(int, s)) for s in data['standard_raw']),
                  key=lambda raw: (len(raw), raw))


def values_worker(vfold, words, queue):
    import token_value
    from ordinal import show
    token_value.P1_ROOT_EXPERIMENT = True
    token_value.P1_V_FOLD_EXPERIMENT = vfold
    out = {}
    for raw in words:
        try:
            out[digits(raw)] = show(token_value.value(raw))
        except token_value.Unknown:
            out[digits(raw)] = None
    queue.put(out)


def run_values(vfold, words):
    ctx = mp.get_context('spawn')
    q = ctx.Queue()
    p = ctx.Process(target=values_worker, args=(vfold, words, q))
    p.start()
    out = q.get()
    p.join()
    return out


def main():
    words = load_words()
    base = run_values(False, words)
    import token_value
    import harness
    import evalord
    import conj2
    from ordinal import lt, show, succ
    token_value.P1_ROOT_EXPERIMENT = True
    BITS = '--bits' in sys.argv
    RAW = '--raw' in sys.argv
    if BITS and RAW:
        raise SystemExit('choose only one of --bits and --raw')
    token_value.P1_V_FOLD_EXPERIMENT = not (BITS or RAW)
    token_value.P1_V_BITS_EXPERIMENT = BITS
    token_value.P1_V_RAW_EXPERIMENT = RAW

    def cand(raw):
        try:
            return token_value.value(raw)
        except token_value.Unknown:
            return None

    new = {raw: cand(raw) for raw in words}
    counts = Counter()
    issues = []
    started = time.monotonic()
    for raw in words:
        b = base[digits(raw)]
        v = new[raw]
        if b is not None:
            counts['base_decided'] += 1
            if v is None or show(v) != b:
                counts['base_value_changed'] += 1
                issues.append({'kind': 'base_changed', 'raw': digits(raw), 'base': b,
                               'new': None if v is None else show(v)})
            continue
        counts['base_unknown'] += 1
        if v is None:
            counts['still_unknown'] += 1
            continue
        counts['new_decided'] += 1
        if raw[-1] == 0:
            parent = new.get(raw[:-1]) or cand(raw[:-1])
            if parent is None:
                counts['succ_parent_unknown'] += 1
            elif v == succ(parent):
                counts['succ_agree'] += 1
            else:
                counts['succ_differ'] += 1
                issues.append({'kind': 'successor', 'raw': digits(raw)})
            continue
        counts['limit'] += 1
        if time.monotonic() - started > 700:
            counts['limit_budget_skipped'] += 1
            continue
        xs = []
        for n in range(1, 11):
            x = cand(harness.fs(raw, n))
            xs.append(x)
            if x is None:
                break
        ok = len(xs) == 10 and all(x is not None for x in xs)
        counts['limit_all10' if ok else 'limit_term_unknown'] += 1
        bad = [n for n, x in enumerate(xs, 1) if x is not None and not lt(x, v)]
        if bad:
            counts['limit_term_not_below'] += 1
            issues.append({'kind': 'term_not_below', 'raw': digits(raw), 'n': bad})
        if any(x is not None and y is not None and not lt(x, y) for x, y in zip(xs, xs[1:])):
            counts['limit_terms_not_increasing'] += 1
        if ok:
            s4, s10 = evalord.sup(xs[:4]), evalord.sup(xs)
            if s4 is None or s10 is None or s4 != s10:
                counts['limit_sup_undecided'] += 1
            elif s10 == v:
                counts['limit_sup_agree'] += 1
            else:
                counts['limit_sup_differ'] += 1
                issues.append({'kind': 'sup_differ', 'raw': digits(raw),
                               'value': show(v), 'sup10': show(s10)})
    ordered = sorted((raw, v) for raw, v in new.items() if v is not None)
    counts['decided_total'] = len(ordered)
    for (a, x), (c, y) in zip(ordered, ordered[1:]):
        if not lt(x, y):
            counts['adjacent_order_bad'] += 1
            issues.append({'kind': 'order', 'left': digits(a), 'right': digits(c),
                           'lv': show(x), 'rv': show(y)})
    unknown = sorted(digits(raw) for raw, v in new.items() if v is None)
    minimal = [s for s in unknown
               if not any(s != t and s.startswith(t) for t in unknown)]

    # primitive blocks (T(u)=u) in terms n=1..4 of the five old minimal roots
    roots = ['00210202102', '0021020210121', '00210202101202',
             '00210202100210202', '002102021010210202']
    prims = {}
    for r in roots:
        S = tuple(map(int, r))
        for n in range(1, 5):
            t = harness.fs(S, n)
            for u in conj2.units(t[2:]):
                for w in [u, conj2.T(u)]:
                    for x in conj2.units(w):
                        if len(x) > 1 and conj2.T(x) == x:
                            prims[x] = None
    rows = []
    for u in sorted(prims):
        try:
            val = token_value.block_value(u)
        except token_value.Unknown:
            val = None
        rows.append((u, val))
    prim_bad = 0
    known = [(u, x) for u, x in rows if x is not None]
    for (a, x), (c, y) in zip(known, known[1:]):
        if not lt(x, y):
            prim_bad += 1
    counts['prim_blocks'] = len(rows)
    counts['prim_decided'] = len(known)
    counts['prim_order_bad'] = prim_bad
    flag = 'P1_V_RAW_EXPERIMENT' if RAW else 'P1_V_BITS_EXPERIMENT' if BITS else 'P1_V_FOLD_EXPERIMENT'
    report = {'flag': 'P1_ROOT_EXPERIMENT + ' + flag, 'counts': dict(counts),
              'issues': issues[:200], 'still_unknown_minimal': minimal,
              'still_unknown_count': len(unknown),
              'prim_blocks': [{'u': digits(u), 'value': None if x is None else show(x)}
                              for u, x in rows]}
    (HERE / ('p1-v-raw43.json' if RAW else 'p1-v-bits43.json' if BITS else 'p1-v-fold43.json')).write_text(json.dumps(report, ensure_ascii=False, indent=1) + '\n')
    print('counts', dict(counts))
    print('issues', issues[:8])
    print('still unknown', len(unknown), 'minimal', minimal[:20])
    for u, x in rows:
        print(' prim', digits(u), None if x is None else show(x))


if __name__ == '__main__':
    main()
