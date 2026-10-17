"""Warm missing blocks per EXT121 candidate using only the independent off cache.

The on-rule predictions are frozen from the common-seed scan. Missing scan
predictions are retried separately, never copied into the off evaluator.
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
from ordinal import show


class Timeout(Exception):
    pass


def alarm(*_):
    raise Timeout


def tup(x):
    return tuple(tup(y) for y in x) if isinstance(x, list) else x


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--scan', type=Path, required=True)
    ap.add_argument('--off-seed', type=Path, required=True)
    ap.add_argument('--results', type=Path, required=True)
    ap.add_argument('--case-seconds', type=float, default=1)
    ap.add_argument('--direct-seconds', type=float)
    ap.add_argument('--retain-same', action='store_true')
    args = ap.parse_args()
    report = json.loads(args.scan.read_text())
    if report['seed_strategy'] != 'same off seed, separate copies':
        ap.error('requires the common-seed scan')
    with args.off_seed.open('rb') as f:
        state = pickle.load(f)
    assert state['signature'] == ('frontier-no-ii-v1', rule6.NS, True, True, rule6.MORE_DEPTH)
    rule6.USE_LIFT = rule6.EXT = rule6.MORE = True
    rule6.EXT121 = False
    rule6.EXT121E = False
    rule6.MAXD = 7
    lift.unlift((2,1))
    rule6.memo, rule6.hmemo = state['memo'], state['hmemo']
    off = (rule6.memo, rule6.hmemo)
    on = tuple(dict(d) for d in off)
    harness.fs = lru_cache(maxsize=40000)(harness.fs)
    rule6.is_selfref = lru_cache(maxsize=40000)(rule6.is_selfref)
    rule6.level = lru_cache(maxsize=40000)(rule6.level)
    rule6.conj2.T = lru_cache(maxsize=40000)(rule6.conj2.T)
    signal.signal(signal.SIGALRM, alarm)
    deps = set()

    def missing(u):
        deps.add((0,0)+tuple(u))
        return None

    rule6.lower.lower = missing

    def call(fun, budget=.05, enabled=False):
        rule6.EXT121 = rule6.EXT121E = False
        setattr(rule6,report.get('experiment','EXT121'),enabled)
        rule6.memo, rule6.hmemo = on if enabled else off
        rule6.st.update(depth=0, taint=0)
        deps.clear()
        signal.setitimer(signal.ITIMER_REAL, max(.001,budget))
        try:
            x = fun()
            status = 'missing' if rule6.st['taint'] else ('clean' if x is not None else 'none')
        except (Timeout, RecursionError):
            x, status = None, 'timeout'
        finally:
            signal.setitimer(signal.ITIMER_REAL, 0)
            rule6.st['depth'] = 0
        return {'status':status, 'ordinal':x if status=='clean' else None,
                'rendered':show(x) if status=='clean' else None}, list(deps)

    def real(s,budget=.05):
        return call(lambda:rule6.real_sup(s[2:])[0],budget)

    def warm(s,direct):
        started = time.monotonic()
        deadline = started+(args.direct_seconds if direct and args.direct_seconds else args.case_seconds)
        pending, scheduled, attempts = [], set(), Counter()
        jobs = 0

        def enqueue(t):
            if len(t)<=500 and off[0].get(t) is None and t not in scheduled:
                heapq.heappush(pending,(attempts[t],len(t),t))
                scheduled.add(t)

        for n in rule6.NS:
            t = harness.fs(s,n)
            for i in range(3,len(t)+1):
                if t[i-1] != 0:
                    enqueue(t[:i])
        while True:
            value, missing_deps = real(s, min(.05,max(.001,deadline-time.monotonic())))
            if value['status']=='clean' or time.monotonic()>=deadline:
                return value,jobs,time.monotonic()-started
            for t in missing_deps:
                enqueue(t)
            if not pending:
                return value,jobs,time.monotonic()-started
            # Retry parents after warming dependencies, within this case's cap.
            tick=min(deadline,time.monotonic()+.15)
            again=[]
            while pending and time.monotonic()<tick:
                _,_,t=heapq.heappop(pending)
                scheduled.remove(t)
                if off[0].get(t) is not None:
                    continue
                attempts[t]+=1
                r,missing_deps=call(lambda:rule6.R(t),min(.03,max(.001,tick-time.monotonic())))
                jobs+=1
                if r['status']!='clean':
                    again.append(t)
                for d in missing_deps:
                    enqueue(d)
            for t in again:
                enqueue(t)

    rows = report['cases']+report['scan_unresolved']
    report['cases'],report['scan_unresolved']=[],[]
    report['case_seconds']=args.case_seconds
    report['direct_seconds']=args.direct_seconds
    report['screened_same_after_warm']=[]
    for i,row in enumerate(rows):
        s=tuple(map(int,row['sequence']))
        u=s[2:]
        k=rule6.level(u)
        base=u[:-2*k-3] if k else ()
        direct=bool(k and base[-4:]==(0,1,2,1) and base!=(2,1,0,1,2,1))
        value,jobs,elapsed=warm(s,direct)
        row.update(off_real_sup=value,warm_jobs=jobs,warm_seconds=elapsed)
        off_rule,_=call(lambda:rule6.rules(s[2:]),.1)
        row['off_rule_after_warm']=off_rule
        prediction=row['on_rule']
        if prediction['status'] not in ('clean','none'):
            prediction,_=call(lambda:rule6.rules(s[2:]),.1,True)
            row['on_rule']=prediction
        if not args.retain_same and (off_rule['status']==prediction['status']=='none' or
            (off_rule['status']==prediction['status']=='clean' and
             tup(off_rule['ordinal'])==tup(prediction['ordinal']))):
            row['result']='same-rule-after-warm'
            report['screened_same_after_warm'].append(row)
        else:
            row['result']=('unresolved' if value['status']!='clean' or prediction['status']!='clean' else
                           'agree' if tup(value['ordinal'])==tup(prediction['ordinal']) else 'differ')
            report['cases'].append(row)
        if i%10==0:
            print('warm',i,'/',len(rows),dict(Counter(r['result'] for r in report['cases'])),flush=True)
            args.results.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    # Later cases may have supplied the final missing dependency of earlier ones.
    for row in report['cases']:
        s=tuple(map(int,row['sequence']))
        value,_=real(s,.1)
        row['off_real_sup']=value
        prediction=row['on_rule']
        row['result']=('unresolved' if value['status']!='clean' or prediction['status']!='clean' else
                       'agree' if tup(value['ordinal'])==tup(prediction['ordinal']) else 'differ')
    for row in report['targets']:
        s=tuple(map(int,row['sequence']))
        row['off_real_sup'],_=real(s,.1)
    report['counts']=dict(Counter(r['result'] for r in report['cases']))
    for row in report['cases']:
        u=tuple(map(int,row['sequence'][2:]))
        k=rule6.level(u)
        base=u[:-2*k-3] if k else ()
        row['direct_EXT121_base']=bool(k and base[-4:]==(0,1,2,1) and base!=(2,1,0,1,2,1))
    report['warm_total_jobs']=sum(r['warm_jobs'] for r in report['cases']+report['screened_same_after_warm'])
    args.results.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print('FINAL',report['counts'],'screened',len(report['screened_same_after_warm']),
          'warm jobs',report['warm_total_jobs'],flush=True)


if __name__=='__main__':
    main()
