"""Compare EXT121 rules with real terms evaluated with EXT121 and II disabled.

The two evaluators have separate clean caches. Enumeration includes the entire
length-24 closure and all standard toksearch2 strings of at most nine tokens.
Unfinished enumeration and timed-out comparisons are explicitly unresolved.
"""
import argparse
from collections import Counter
from functools import lru_cache
import heapq
import json
from pathlib import Path
import pickle
import signal
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE.parent)]
import harness
import lift
import rule6
import std
from ordinal import show


class Timeout(Exception):
    pass


def alarm(*_):
    raise Timeout


def text(s):
    return ''.join(map(str, s))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--off-seed', type=Path, required=True)
    ap.add_argument('--on-seed', type=Path,
                    help='optional separate EXT121 seed; default: copy the off seed')
    ap.add_argument('--save-off', type=Path)
    ap.add_argument('--variant', choices=('EXT121','EXT121E'), default='EXT121')
    ap.add_argument('--include-cases', type=Path)
    ap.add_argument('--results', type=Path, required=True)
    ap.add_argument('--seconds', type=float, default=600)
    ap.add_argument('--scan-budget', type=float, default=.025)
    ap.add_argument('--case-budget', type=float, default=.2)
    args = ap.parse_args()
    if args.on_seed and args.variant != 'EXT121':
        ap.error('EXT121E requires a common off seed, not an EXT121 on seed')
    rule6.USE_LIFT = rule6.EXT = rule6.MORE = True
    rule6.MAXD = 7
    lift.unlift((2, 1))
    harness.fs = lru_cache(maxsize=40000)(harness.fs)
    rule6.is_selfref = lru_cache(maxsize=40000)(rule6.is_selfref)
    rule6.level = lru_cache(maxsize=40000)(rule6.level)
    rule6.conj2.T = lru_cache(maxsize=40000)(rule6.conj2.T)
    signal.signal(signal.SIGALRM, alarm)
    caches = {}
    for flag, path in ((False, args.off_seed), (True, args.on_seed)):
        if flag and path is None:
            caches[True] = tuple(dict(d) for d in caches[False])
            continue
        with path.open('rb') as f:
            state = pickle.load(f)
        expected = (('ext121-no-II-v1', 7, rule6.NS) if flag else
                    ('frontier-no-ii-v1', rule6.NS, True, True, rule6.MORE_DEPTH))
        if state['signature'] != expected:
            ap.error('incompatible clean seed')
        caches[flag] = (state['memo'], state['hmemo'])
    frontier = Counter()

    def missing(u):
        frontier[tuple(u)] += 1
        return None

    rule6.lower.lower = missing

    def call(flag, fun, budget):
        rule6.EXT121 = rule6.EXT121E = False
        setattr(rule6, args.variant, flag)
        rule6.memo, rule6.hmemo = caches[flag]
        rule6.st.update(depth=0, taint=0)
        frontier.clear()
        signal.setitimer(signal.ITIMER_REAL, budget)
        try:
            x = fun()
            status = 'missing' if rule6.st['taint'] else ('clean' if x is not None else 'none')
        except (Timeout, RecursionError):
            x, status = None, 'timeout'
        finally:
            signal.setitimer(signal.ITIMER_REAL, 0)
            rule6.st['depth'] = 0
        return {'status': status, 'ordinal': x if status == 'clean' else None,
                'rendered': show(x) if status == 'clean' else None}, list(frontier)

    def real(s, budget):
        # real_sup bypasses the closed rule for s itself. The entire dependency
        # evaluation uses only the off cache. Never insert its guessed sup.
        def run():
            x, _ = rule6.real_sup(s[2:])
            return x
        return call(False, run, budget)

    closure = {s for s in harness.closure([(0,0,2,1,0,2)], maxlen=24)
               if s >= tuple(map(int, '0021012021'))}
    tokens = {'A0': (0,1,2), 'A1': (0,1,2,0,2), 'A2': (0,1,2,0,2,0,2), '1': (1,)}
    seen, token_rows = set(), {}
    wave = [((), (2,1))]
    for _ in range(9):
        nxt = []
        for names, u in wave:
            for name, tk in tokens.items():
                if name == '1' and names and names[-1] == '1':
                    continue
                v = u+tk
                s = (0,0)+v
                if v in seen or s >= (0,0,2,1,0,2):
                    continue
                seen.add(v)
                if not std.is_standard(s):
                    continue
                token_rows[s] = names+(name,)
                nxt.append((names+(name,), v))
        wave = nxt
    seqs = sorted((s for s in closure | token_rows.keys() if rule6.is_selfref(s[2:])),
                  key=lambda s:(len(s), s))
    report = {'closure_selected': len(closure), 'token_standard': len(token_rows),
              'selfref_union': len(seqs), 'NS': rule6.NS, 'MAXD': 7,
              'comparison_EXT121': False, 'hypothesis_II_executed': False,
              'cases': [], 'scan_unresolved': [], 'same_rule': 0, 'no_rule': 0}
    report['seed_strategy'] = 'separate' if args.on_seed else 'same off seed, separate copies'
    report['experiment'] = args.variant
    report['comparison_EXT121E'] = False
    print('enumeration', {k:v for k,v in report.items() if isinstance(v,int)}, flush=True)

    def save():
        args.results.write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n')

    for i, s in enumerate(seqs):
        off, _ = call(False, lambda:rule6.rules(s[2:]), args.scan_budget)
        on, _ = call(True, lambda:rule6.rules(s[2:]), args.scan_budget)
        row = {'sequence': text(s), 'closure': s in closure,
               'tokens': token_rows.get(s), 'off_rule': off, 'on_rule': on}
        # Equality only counts when both computations really finished cleanly.
        if off['status'] == on['status'] == 'clean' and off['ordinal'] == on['ordinal']:
            report['same_rule'] += 1
        elif off['status'] == on['status'] == 'none':
            report['no_rule'] += 1
        elif off['status'] == 'clean' or on['status'] == 'clean':
            report['cases'].append(row)
        else:
            report['scan_unresolved'].append(row)
        # Warm the on evaluator with actual terms for non-rule E bases; never
        # share these results with the independent off evaluator.
        if on['status'] != 'clean':
            call(True, lambda:rule6.R(s), args.scan_budget)
        if i % 100 == 0:
            print('scan', i, 'cases', len(report['cases']), 'scan-unresolved',
                  len(report['scan_unresolved']), flush=True)
            save()

    # A second pass retries the scan now that shorter bases have been warmed.
    initial = report['cases'] + report['scan_unresolved']
    report['cases'], report['scan_unresolved'] = [], []
    for row in initial:
        s = tuple(map(int, row['sequence']))
        off, _ = call(False, lambda:rule6.rules(s[2:]), args.scan_budget)
        on, _ = call(True, lambda:rule6.rules(s[2:]), args.scan_budget)
        row.update(off_rule=off, on_rule=on)
        if off['status'] == on['status'] == 'clean' and off['ordinal'] == on['ordinal']:
            report['same_rule'] += 1
        elif off['status'] == on['status'] == 'none':
            report['no_rule'] += 1
        elif off['status'] == 'clean' or on['status'] == 'clean':
            report['cases'].append(row)
        else:
            report['scan_unresolved'].append(row)
    print('scan done cases', len(report['cases']), 'unclassified', len(report['scan_unresolved']), flush=True)

    if args.include_cases:
        previous = json.loads(args.include_cases.read_text())
        present = {r['sequence'] for r in report['cases']+report['scan_unresolved']}
        for old in previous['cases']+previous.get('scan_unresolved',[]):
            if old['sequence'] in present:
                continue
            s = tuple(map(int,old['sequence']))
            off,_ = call(False,lambda:rule6.rules(s[2:]),args.scan_budget)
            on,_ = call(True,lambda:rule6.rules(s[2:]),args.scan_budget)
            report['cases'].append({'sequence':old['sequence'], 'closure':old['closure'],
                                    'tokens':old['tokens'],'off_rule':off,'on_rule':on,
                                    'retained_from_previous':True})
            present.add(old['sequence'])

    for row in report['cases']:
        s = tuple(map(int, row['sequence']))
        value, _ = real(s, args.case_budget)
        row['off_real_sup'] = value

    b = tuple(map(int, '002101210120210121'))
    targets = [b+(0,1,2)+(0,2)*k for k in (1,2,3)]
    report['targets'] = [{'sequence': text(s)} for s in targets]
    pending, scheduled, attempts = [], set(), Counter()

    def enqueue(s):
        if len(s) <= 500 and caches[False][0].get(s) is None and s not in scheduled:
            heapq.heappush(pending, (attempts[s], len(s), s))
            scheduled.add(s)

    for s in targets:
        for n in rule6.NS:
            t = harness.fs(s,n)
            for j in range(3, len(t)+1):
                if t[j-1] != 0:
                    enqueue(t[:j])
    start = last_log = time.monotonic()
    deadline = start+args.seconds
    jobs = 0
    while time.monotonic() < deadline:
        for s, row in zip(targets, report['targets']):
            value, deps = real(s, min(.1, max(.001, deadline-time.monotonic())))
            row['off_real_sup'] = value
            for u in deps:
                enqueue((0,0)+u)
        if all(r['off_real_sup']['status']=='clean' for r in report['targets']):
            break
        if not pending:
            break
        # Work for <= 3 seconds before retrying target real sups.
        tick = min(deadline,time.monotonic()+3)
        retry = []
        while pending and time.monotonic() < tick:
            _, _, s = heapq.heappop(pending)
            scheduled.remove(s)
            attempts[s] += 1
            value, deps = call(False, lambda:rule6.R(s), min(.15,max(.001,tick-time.monotonic())))
            if value['status'] != 'clean':
                retry.append(s)
            for u in deps:
                enqueue((0,0)+u)
            jobs += 1
        for s in retry:
            enqueue(s)
        if time.monotonic()-last_log >= 20:
            print('B warm', round(time.monotonic()-start), 's jobs', jobs, 'pending', len(pending),
                  'R',len(caches[False][0]), 'targets',
                  [r['off_real_sup']['status'] for r in report['targets']], flush=True)
            save()
            last_log = time.monotonic()
    report['B_seconds'] = time.monotonic()-start
    report['B_jobs'] = jobs
    for row in report['cases']:
        s = tuple(map(int, row['sequence']))
        value, _ = real(s, args.case_budget)
        row['off_real_sup'] = value
        on = row['on_rule']
        row['result'] = ('unresolved' if value['status'] != 'clean' or on['status'] != 'clean'
                         else 'agree' if value['ordinal']==on['ordinal'] else 'differ')
    report['counts'] = dict(Counter(row['result'] for row in report['cases']))
    for s, row in zip(targets,report['targets']):
        value, _ = real(s,args.case_budget)
        on, _ = call(True,lambda:rule6.rules(s[2:]),args.scan_budget)
        row.update(off_real_sup=value,on_rule=on,
                   result=('unresolved' if value['status']!='clean' or on['status']!='clean' else
                           'agree' if value['ordinal']==on['ordinal'] else 'differ'))
    save()
    if args.save_off:
        with args.save_off.open('wb') as f:
            pickle.dump({'signature': ('frontier-no-ii-v1', rule6.NS, True, True, rule6.MORE_DEPTH),
                         'memo': {s:x for s,x in caches[False][0].items() if x is not None},
                         'hmemo': {s:x for s,x in caches[False][1].items() if x is not None}}, f)
    print('FINAL',report['counts'], 'scan-unresolved',len(report['scan_unresolved']), flush=True)
    print('B targets',[(r['sequence'],r['result']) for r in report['targets']],flush=True)


if __name__ == '__main__':
    main()
