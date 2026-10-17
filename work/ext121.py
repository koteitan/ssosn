"""Flag-guarded EXT121 experiment. Run from the repository root with timeout 30s.

python3 work/ext121.py validate
python3 work/ext121.py predict --state work/ext121-state.pkl
No hypothesis II is executed in predict mode. Clean still depends on conjectural
closed rules and finite-sample sup inference, including the new EXT121 rule.
"""
import argparse
from functools import lru_cache
import json
from pathlib import Path
import pickle
import signal
import sys

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE.parent)]
import harness
import lift
import rule6
from ordinal import show

ROOTS = ('002101210120210121012021', '002101210121', '002102')


class TimedOut(Exception):
    pass


def alarm(*_):
    raise TimedOut


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('mode', choices=('validate', 'predict'))
    ap.add_argument('--state', type=Path)
    ap.add_argument('--budget', type=float, default=.15)
    ap.add_argument('--results', type=Path, required=True)
    ap.add_argument('--variant', choices=('EXT121','EXT121E'), default='EXT121')
    ap.add_argument('--disable-experiment', action='store_true')
    args = ap.parse_args()
    rule6.USE_LIFT = rule6.EXT = rule6.MORE = True
    rule6.MAXD = 7
    lift.unlift((2, 1))
    harness.fs = lru_cache(maxsize=20000)(harness.fs)
    rule6.is_selfref = lru_cache(maxsize=20000)(rule6.is_selfref)
    rule6.level = lru_cache(maxsize=20000)(rule6.level)
    # lev depends on the experiment flag: deliberately do not cache it.
    rule6.conj2.T = lru_cache(maxsize=20000)(rule6.conj2.T)
    report = {'MAXD': 7, 'NS': rule6.NS, 'USE_LIFT': True, 'EXT': True, 'MORE': True}
    if args.mode == 'validate':
        ss = sorted(s for s in harness.closure([(0, 0, 2, 1, 0, 2)], maxlen=24)
                    if s >= tuple(map(int, '0021012021')))
        report.update(closure_nmax=3, closure_maxlen=24, selected=len(ss), runs=[])
        for enabled in (False, True):
            rule6.EXT121 = rule6.EXT121E = False
            setattr(rule6,args.variant,enabled)
            rule6.memo.clear()
            rule6.hmemo.clear()
            rule6.st.update(depth=0, taint=0)
            print(args.variant, enabled, 'selected', len(ss), flush=True)
            res = rule6.validate(ss)
            report['runs'].append({args.variant: enabled, **res})
            print(res, flush=True)
    else:
        rule6.EXT121 = rule6.EXT121E = False
        setattr(rule6,args.variant,not args.disable_experiment)
        report.update(EXT121=rule6.EXT121, EXT121E=rule6.EXT121E,
                      experiment=args.variant, hypothesis_II_executed=False, rows=[], sup3=[])
        active_bases = {}
        original_ext_base = rule6.ext_base

        def traced_ext_base(u):
            allowed = original_ext_base(u)
            if allowed and rule6.EXT121E and tuple(u)[-4:] == (0,1,2,1):
                key = ''.join(map(str,u))
                active_bases[key] = active_bases.get(key,0)+1
            return allowed

        rule6.ext_base = traced_ext_base
        rule6.lower.lower = lambda u: None
        signature = (('ext121-no-II-v1', rule6.MAXD, rule6.NS)
                     if args.variant=='EXT121' and not args.disable_experiment else
                     ('root-no-II-v2', args.variant, not args.disable_experiment, rule6.MAXD,rule6.NS))
        if args.state and args.state.exists():
            with args.state.open('rb') as f:
                state = pickle.load(f)
            if state['signature'] != signature:
                ap.error('incompatible state')
            rule6.memo.update(state['memo'])
            rule6.hmemo.update(state['hmemo'])
        signal.signal(signal.SIGALRM, alarm)

        def probe(s, label):
            rule6.st.update(depth=0, taint=0)
            signal.setitimer(signal.ITIMER_REAL, args.budget)
            try:
                r = rule6.R(s)
                clean = r is not None and rule6.st['taint'] == 0
                status = 'clean' if clean else 'unknown'
            except (TimedOut, RecursionError):
                r, status = None, 'timeout'
            finally:
                signal.setitimer(signal.ITIMER_REAL, 0)
                rule6.st['depth'] = 0
            row = {'label': label, 'sequence': ''.join(map(str, s)), 'status': status,
                   'rendered': show(r) if r is not None else None, 'ordinal': r}
            report['rows'].append(row)
            print(label, row['sequence'], row['rendered'], status, flush=True)
            return r if status == 'clean' else None

        def warm(s):
            for i in range(3, len(s)):
                if s[i-1] != 0 and rule6.memo.get(s[:i]) is None:
                    probe(s[:i], 'prefix')

        # Keep the known exception in the experiment's regression checks.
        exception = tuple(map(int, '0021012101202'))
        warm(exception)
        probe(exception, 'exception')
        for text in ROOTS:
            s = tuple(map(int, text))
            warm(s)
            probe(s, 'root-before')
            xs = []
            for n in range(1, 6):
                term = harness.fs(s, n)
                warm(term)
                xs.append(probe(term, f'term-{n}'))
            probe(s, 'root-after')
            candidate = rule6.sup3(xs) if all(x is not None for x in xs) else None
            report['sup3'].append({'sequence': text, 'ordinal': candidate,
                                   'rendered': show(candidate) if candidate is not None else None})
            print('sup3', text, show(candidate) if candidate is not None else None, flush=True)
        if args.state:
            state = {'signature': signature,
                     'memo': {s:r for s,r in rule6.memo.items() if r is not None},
                     'hmemo': {s:r for s,r in rule6.hmemo.items() if r is not None}}
            with args.state.open('wb') as f:
                pickle.dump(state, f)
        report['active_EXT121E_bases'] = active_bases
    args.results.write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n')


if __name__ == '__main__':
    main()
