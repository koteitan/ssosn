"""Warm the exact unresolved hook frontiers, without executing hypothesis ②.

Use an external timeout. Each invocation has its own short wall-clock budget
and checkpoints only non-None clean R/hook entries. Repeating the command
continues the queue. Results still rely on rule6's conjectural rules and sup
heuristic; clean is not a proof of the ordinal assignment.

Example: timeout 30s python3 work/warm_frontier.py 002101210120210121012021
  --state work/clean-warm.pkl --seconds 20 --terms 5
"""
import argparse
from collections import Counter
from functools import lru_cache
import heapq
import hashlib
import json
from pathlib import Path
import pickle
import signal
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE), str(HERE.parent)]
import rule6
import harness
import lift
from ordinal import show


class JobTimeout(Exception):
    pass


def alarm(*_):
    raise JobTimeout


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('seqs', nargs='+')
    ap.add_argument('--state', type=Path, required=True)
    ap.add_argument('--seconds', type=float, default=20)
    ap.add_argument('--depth', type=int, default=6)
    ap.add_argument('--terms', type=int, default=5)
    ap.add_argument('--job-seconds', type=float, default=.3)
    ap.add_argument('--max-block', type=int, default=300)
    ap.add_argument('--max-jobs', type=int, default=1000)
    ap.add_argument('--frontier-prefixes', action='store_true')
    ap.add_argument('--order', choices=('length', 'lex'), default='length')
    ap.add_argument('--probe-seconds', type=float, default=.05)
    ap.add_argument('--results', type=Path)
    args = ap.parse_args()
    if min(args.seconds, args.job_seconds, args.probe_seconds) <= 0 or args.depth < 0 or args.terms < 1:
        ap.error('positive time budgets/term count and nonnegative depth required')

    rule6.USE_LIFT = rule6.EXT = rule6.MORE = True
    rule6.MAXD = args.depth
    lift.unlift((2,1))
    # These functions are pure at the fixed settings above. Never cache rules()
    # or an unresolved hook: their answers depend on the growing clean memo.
    harness.fs = lru_cache(maxsize=20000)(harness.fs)
    rule6.is_selfref = lru_cache(maxsize=20000)(rule6.is_selfref)
    rule6.lev = lru_cache(maxsize=20000)(rule6.lev)
    rule6.level = lru_cache(maxsize=20000)(rule6.level)
    rule6.conj2.T = lru_cache(maxsize=20000)(rule6.conj2.T)
    signature = ('frontier-no-ii-v1', rule6.NS, rule6.EXT, rule6.MORE, rule6.MORE_DEPTH)
    state = {'signature': signature, 'memo': {}, 'hmemo': {}, 'pending': set(),
             'attempts': {}, 'timeouts': 0}
    if args.state.exists():
        with args.state.open('rb') as f:
            state = pickle.load(f)
        if state['signature'] != signature:
            ap.error('incompatible memo settings')
    rule6.memo.update(state['memo'])
    rule6.hmemo.update(state['hmemo'])
    pending = state['pending']
    attempts = state['attempts']
    roots = [tuple(int(c) for c in s) for s in args.seqs]
    if any(s[:2] != (0,0) or len(s) < 3 or s[-1] == 0 for s in roots):
        ap.error('roots must start 00, be nonempty limits, and use digits')
    terms = [(s, n, harness.fs(s, n)) for s in roots for n in range(1, args.terms+1)]
    tracked = set(roots) | {s[:-1] for _, _, s in terms}
    for _, _, s in terms:
        pending.update(s[:i] for i in range(3, len(s)+1) if s[i-1] != 0)
    pending.update(roots)
    frontier = Counter()

    # This is the ONLY replacement for lower.lower: it never returns a value
    # from ②. rule6 itself still increments taint before reaching this hook.
    def unresolved(u):
        frontier[tuple(u)] += 1
        return None

    rule6.lower.lower = unresolved
    signal.signal(signal.SIGALRM, alarm)
    deadline = time.monotonic()+args.seconds
    jobs = successes = 0
    clean_version = len(rule6.memo)+len(rule6.hmemo)
    visited = set()
    queue = []
    scheduled = set()

    def enqueue(s):
        pending.add(s)
        if s not in visited and s not in scheduled and rule6.memo.get(s) is None:
            key = (s, attempts.get(s, 0)) if args.order == 'lex' else (len(s), attempts.get(s, 0), s)
            heapq.heappush(queue, (key, s))
            scheduled.add(s)

    for s in list(pending):
        enqueue(s)
    while time.monotonic() < deadline and jobs < args.max_jobs:
        if not queue:
            now_version = sum(r is not None for r in rule6.memo.values()) + sum(
                r is not None for r in rule6.hmemo.values())
            if now_version <= clean_version:
                break
            clean_version = now_version
            visited.clear()
            for s in list(pending):
                enqueue(s)
            continue
        _, s = heapq.heappop(queue)
        scheduled.discard(s)
        if s in visited or rule6.memo.get(s) is not None:
            if rule6.memo.get(s) is not None:
                pending.discard(s)
            continue
        pending.discard(s)
        visited.add(s)
        attempts[s] = attempts.get(s, 0)+1
        frontier.clear()
        rule6.st.update(depth=0, taint=0)
        signal.setitimer(signal.ITIMER_REAL, min(args.job_seconds, max(.001, deadline-time.monotonic())))
        try:
            r = rule6.R(s)
            if r is not None and not rule6.st['taint']:
                successes += 1
            else:
                pending.add(s)
        except JobTimeout:
            state['timeouts'] += 1
            pending.add(s)
        finally:
            signal.setitimer(signal.ITIMER_REAL, 0)
            rule6.st['depth'] = 0
        for u in frontier:
            if len(u) <= args.max_block and rule6.hmemo.get(u) is None:
                enqueue((0,0)+u)
                if args.frontier_prefixes:
                    for i in range(1,len(u)):
                        if u[i-1] != 0:
                            enqueue((0,0)+u[:i])
        if s in tracked:
            state.setdefault('frontier_roots', {})[s] = frontier.most_common(10)
        jobs += 1
    # Materialize cheap successor terms and retry the requested roots after
    # their dependencies have been warmed. Do not infer values by interpolation.
    for s in [s for _, _, s in terms] + roots:
        rule6.st.update(depth=0, taint=0)
        signal.setitimer(signal.ITIMER_REAL, args.probe_seconds)
        try:
            rule6.R(s)
        except JobTimeout:
            pass
        finally:
            signal.setitimer(signal.ITIMER_REAL, 0)
            rule6.st['depth'] = 0
    state['memo'] = {s:r for s,r in rule6.memo.items() if r is not None}
    state['hmemo'] = {u:r for u,r in rule6.hmemo.items() if r is not None}
    pending.difference_update(state['memo'])
    args.state.parent.mkdir(parents=True, exist_ok=True)
    temp = args.state.with_suffix(args.state.suffix+'.tmp')
    with temp.open('wb') as f:
        pickle.dump(state, f)
    temp.replace(args.state)
    print(f'jobs={jobs} successful_jobs={successes} clean_R={len(state["memo"])} '
          f'clean_hook={len(state["hmemo"])} pending={len(pending)} timeouts_total={state["timeouts"]}', flush=True)
    for _, n, s in terms:
        r = state['memo'].get(s)
        print('term', n, ''.join(map(str,s)), show(r) if r is not None else 'UNKNOWN', flush=True)
    for s in roots:
        r = state['memo'].get(s)
        print('root', ''.join(map(str,s)), show(r) if r is not None else 'UNKNOWN', flush=True)
    if args.results:
        report = {'method': 'rule6 clean memo with hypothesis II disabled; rules and sup remain conjectural',
                  'depth': args.depth, 'NS': rule6.NS, 'roots': [], 'source_sha256': {}}
        for path in (HERE/'rule6.py', HERE/'lift.py', HERE.parent/'evalord.py', HERE.parent/'ordinal.py'):
            report['source_sha256'][str(path.relative_to(HERE.parent))] = hashlib.sha256(path.read_bytes()).hexdigest()
        for root in roots:
            row = {'sequence': ''.join(map(str,root)), 'direct_value': state['memo'].get(root), 'terms': []}
            clean_prefix = []
            prefix_open = True
            for _, n, term in (entry for entry in terms if entry[0] == root):
                r = state['memo'].get(term)
                row['terms'].append({'n': n, 'sequence': ''.join(map(str,term)),
                                     'clean': r is not None, 'rendered': show(r) if r is not None else None,
                                     'ordinal': r})
                if prefix_open and r is not None:
                    clean_prefix.append(r)
                else:
                    prefix_open = False
            candidate = rule6.sup3(clean_prefix) if len(clean_prefix) >= 2 else None
            row['candidate_terms_used'] = len(clean_prefix)
            row['sup3_candidate'] = show(candidate) if candidate is not None else None
            row['sup3_ordinal'] = candidate
            report['roots'].append(row)
        args.results.parent.mkdir(parents=True, exist_ok=True)
        args.results.write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n')
    unresolved_short = sorted(pending, key=lambda s:(len(s), s))[:3]
    print('short unresolved:', [''.join(map(str,s)) for s in unresolved_short], flush=True)


if __name__ == '__main__':
    main()
