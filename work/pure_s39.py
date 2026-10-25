"""§39 corrected block-depth S audit, with the fixed-point fallback off.

timeout 3600 python3 work/pure_s39.py --workers 8 --seconds 1
"""
import argparse
import collections
import gzip
import json
import multiprocessing
import os
import pickle
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
import tail_symbolic as S
from above_p_data26 import HERE, raw
from ordinal import cmp


class CaseTimeout(BaseException):
    pass


CACHE_VERSION = 's39-block-k-no-fp-v1'
CACHE_DIR = HERE / '.cache'
WORD_CACHE = CACHE_DIR / 'pure-s39-words.pkl.gz'
TAIL_CACHE = CACHE_DIR / 'tail-s39.pkl.gz'


def _alarm(_signum, _frame):
    raise CaseTimeout()


def setup(seconds=0):
    T.CUT_COPY_ACTION_EXPERIMENT = True
    T.CONSISTENT_COPY_SEED_EXPERIMENT = True
    T.WD_AFTER_ITERATION_EXPERIMENT = False
    T.GENERAL_COPY_EXPERIMENT = False
    T.MOVABLE_ONE_EXPERIMENT = False
    T.RELTAIL_CAP_EXPERIMENT = False
    T.TAIL_S_EXPERIMENT = True
    T.TAIL_S_DEPTH_EXPERIMENT = False
    T.TAIL_S_COMPLETE_EXPERIMENT = True
    T.TAIL_S_MARKER_EXPERIMENT = True
    T.TAIL_S_E_EXPERIMENT = True
    S.BASE = (0,0,2,1) + S.seq(('D',)*10+('A0',))
    S.FIXEDPOINT_SUP_EXPERIMENT = False
    S.CURRENT_BUDGET_SECONDS = seconds
    T._TAIL_S_MODULE = S
    T._TAIL_S_ACTIVE = False
    T.PURITY_TRACKING = True
    T.PURE_BLOCKS.clear()
    T.PURE_BODIES.clear()
    T.PURE_VALUES.clear()
    T.PURE_FOLDS.clear()
    T.value_tree.cache_clear()
    T.body_tree.cache_clear()
    T.block_tree.cache_clear()
    signal.signal(signal.SIGALRM, _alarm)


def evaluate_one(s, seconds):
    s=tuple(s)
    T._TAIL_S_ACTIVE=False
    T.TAIL_S_COUNTS={'eligible':0,'decided':0,'undecided':0}
    T.TAIL_S_MARKER_COUNTS={'eligible':0,'decided':0,'undecided':0}
    T.TAIL_S_E_COUNTS={'eligible':0,'decided':0,'undecided':0}
    signal.setitimer(signal.ITIMER_REAL, seconds)
    try:
        value=T.value(s);error=None
    except CaseTimeout:
        value=None;error=f'{seconds:g}-s per-value timeout'
    except Exception as e:
        value=None;error=f'{type(e).__name__}: {e}'
    finally:
        signal.signal(signal.SIGALRM, signal.SIG_IGN)
        signal.setitimer(signal.ITIMER_REAL,0)
        signal.signal(signal.SIGALRM,_alarm)
    counts=(T.TAIL_S_COUNTS.copy(),T.TAIL_S_MARKER_COUNTS.copy(),
            T.TAIL_S_E_COUNTS.copy())
    pure=value is not None and T.PURE_VALUES.get(s,False)
    return value,pure,counts,error


def _write_pickle(path, obj):
    path.parent.mkdir(parents=True,exist_ok=True)
    pending=path.with_name(path.name+'.pending')
    with gzip.open(pending,'wb',compresslevel=3) as f:
        pickle.dump(obj,f,protocol=pickle.HIGHEST_PROTOCOL)
    pending.replace(path)


def _read_pickle(path):
    with gzip.open(path,'rb') as f:return pickle.load(f)


def _worker(index, words, anchors, seconds, tag):
    setup(seconds)
    T.PURE_ANCHOR_TOKENS.update(anchors)
    S.load_cache(TAIL_CACHE)
    results={}
    for n,s in enumerate(words,1):
        results[s]=evaluate_one(s,seconds)
        if n%5000==0:print('worker',tag,index,'evaluated',n,'of',len(words),flush=True)
    _write_pickle(CACHE_DIR/f'{tag}-part-{index}.pkl.gz',results)
    S.save_cache(CACHE_DIR/f'{tag}-tail-{index}.pkl.gz')


def _parallel_values(words, memo, anchors, seconds, workers, tag):
    pending=[s for s in words if s not in memo]
    if not pending:return 0
    chunks=[pending[i::workers] for i in range(workers)]
    ctx=multiprocessing.get_context('fork')
    jobs=[]
    for index,chunk in enumerate(chunks):
        if not chunk:continue
        job=ctx.Process(target=_worker,args=(index,chunk,anchors,seconds,tag))
        job.start();jobs.append((index,job))
    for index,job in jobs:
        job.join()
        if job.exitcode:
            raise RuntimeError(f'{tag} worker {index} exited {job.exitcode}')
    for index,_ in jobs:
        memo.update(_read_pickle(CACHE_DIR/f'{tag}-part-{index}.pkl.gz'))
        S.load_cache(CACHE_DIR/f'{tag}-tail-{index}.pkl.gz')
    S.save_cache(TAIL_CACHE)
    _write_pickle(WORD_CACHE,{'version':CACHE_VERSION,'budget':seconds,
        'values':memo})
    return len(pending)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers',type=int,default=8)
    parser.add_argument('--seconds',type=float,default=1.0)
    parser.add_argument('--limit',type=int,default=0,
        help='profile only the first raw words; 0 audits all N=9 rows')
    args=parser.parse_args()
    start = time.monotonic()
    setup(args.seconds)
    S.load_cache(TAIL_CACHE)
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
    T.PURE_ANCHOR_TOKENS.clear()
    T.PURE_ANCHOR_TOKENS.update(tuple(labels[s]) for s in pure_roots)
    ordered = sorted(rows, key=lambda s: (len(labels[s]), labels[s], s))
    if args.limit:
        ordered=ordered[:args.limit]
        rows={s:rows[s] for s in ordered}
    memo = {}
    if WORD_CACHE.exists():
        cached=_read_pickle(WORD_CACHE)
        if cached.get('version')==CACHE_VERSION:
            prior_budget=cached.get('budget',0)
            memo.update({s:r for s,r in cached['values'].items()
                if r[0] is not None or prior_budget>=args.seconds})
    anchors=tuple(T.PURE_ANCHOR_TOKENS)
    processed=_parallel_values(ordered,memo,anchors,args.seconds,args.workers,'s39-roots')
    print('first pass',len(ordered),'new evaluations',processed,
          'elapsed',round(time.monotonic()-start,1),flush=True)
    pure_reasons = collections.Counter()

    def evaluate(s):
        s = tuple(s)
        if s in memo:
            return memo[s]
        memo[s]=evaluate_one(s,args.seconds)
        return memo[s]

    # Pure roots are anchors by definition; the ordinary evaluator still
    # supplies and checks their values below.
    root_set = pure_roots
    vals = {}
    pure = {}
    for i, s in enumerate(ordered, 1):
        v, p, counts, err = evaluate(s)
        if s in root_set and v is not None:
            p = True
        vals[s] = v
        pure[s] = p
        if not p:
            if err is not None:pure_reasons['timeout' if 'timeout' in err else 'unknown']+=1
            if v is not None and not any(x['undecided'] for x in counts):
                pure_reasons['inherited_impure']+=1
            for name,c in zip(('tail_F','sibling_marker','E_sup'),counts):
                if c['undecided']:pure_reasons[name]+=c['undecided']
    pure_standard = sorted((s for s in rows if rows[s] and pure[s]))
    pure_nonstandard = [s for s in rows if not rows[s] and pure[s]]
    limits = sorted((s for s in pure_standard if s[-1] != 0),
                    key=lambda s: (len(labels[s]), labels[s], s))
    terms=sorted({tuple(harness.fs(s,n)) for s in limits for n in range(1,5)})
    term_processed=_parallel_values(terms,memo,anchors,args.seconds,args.workers,'s39-terms')
    print('term pass',len(terms),'new evaluations',term_processed,
          'elapsed',round(time.monotonic()-start,1),flush=True)

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
        if actual != is_new:
            new_bad.append(dict(tokens=labels[s], standard=actual, value=vals[s],
                                value_new=is_new,
                                lower=None if lo == 0 else pure_standard[prefix_max[lo-1]],
                                upper=None if hi == len(pure_standard) else pure_standard[suffix_min[hi]]))

    # A nonstandard value can appear new when the tail is outside the common
    # reference language, or reaches its next sibling cap (§37.x).
    reference=(0,0,2,1)+T.raw_tokens(('D',)*10+('A0',))
    membership=collections.Counter()
    membership_examples=[]
    for mismatch in new_bad:
        if mismatch['standard'] or not mismatch['value_new']:continue
        ts=tuple(mismatch['tokens']);j=0
        while j<len(ts) and ts[j] in ('W','D'):j+=1
        if j==len(ts) or not ts[j].startswith('A'):
            category='outside_reference';shifted=None
        else:
            k=int(ts[j][1:]);tail=ts[j+1:]
            if any(t.startswith('A') and int(t[1:])<k for t in tail):
                category='outside_reference';shifted=None
            else:
                shifted=tuple(('A'+str(int(t[1:])-k)) if t.startswith('A') else t for t in tail)
                in_reference=std.is_standard(reference+T.raw_tokens(shifted))
                marker=('W',)+ts[:j]+('A1',)
                over_cap=T.raw_tokens(shifted)>=T.raw_tokens(marker)
                category=('outside_reference' if not in_reference else
                          'at_or_above_cap' if over_cap else 'inside_both')
        weight=spellings[raw(ts)]
        membership[category]+=weight
        if len(membership_examples)<100:
            membership_examples.append(dict(tokens=ts,shifted=shifted,
                category=category,spellings=weight))

    # Self-consistency only on pure parents whose four sampled real terms are
    # themselves pure. The term values are memoized by raw sequence.
    self_checked = 0
    self_skipped = 0
    self_bad = []
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
    descent=[]
    if order_bad:
        witness=min(order_bad,key=lambda x:(max(len(x['a_tokens']),len(x['b_tokens'])),
            len(x['a_tokens'])+len(x['b_tokens']),x['a_tokens'],x['b_tokens']))
        a=tuple(witness['a']);b=tuple(witness['b']);va=vals[a]
        for step in range(16):
            found=None
            for n in range(1,51):
                t=tuple(harness.fs(b,n))
                if t>=a:found=(n,t);break
            if found is None:
                descent.append(dict(step=step,stop='no term through n=50'));break
            n,t=found;v,p,_,err=evaluate(t)
            standard=std.is_standard(t)
            descent.append(dict(step=step,parent=b,n=n,term=t,value=v,
                pure=p,standard=standard,error=err))
            if not standard or not p or v is None or cmp(va,v)<0:break
            b=t
    report = dict(max_tokens=data['max_tokens'], candidates=len(rows), spellings=sum(spellings.values()),
        workers=args.workers,seconds_per_value=args.seconds,first_pass_new=processed,
        term_pass_new=term_processed,
        pure_unique=len([s for s in rows if pure[s]]), pure_spellings=sum(spellings[s] for s in rows if pure[s]),
        pure_standard_unique=len(pure_standard), pure_nonstandard_unique=len(pure_nonstandard),
        pure_standard_spellings=sum(spellings[s] for s in pure_standard),
        pure_nonstandard_spellings=sum(spellings[s] for s in pure_nonstandard),
        pure_reason_counts=dict(pure_reasons),
        order_violations=order_bad, order_violation_count=len(order_bad),
        value_new_counts={f'{k[0]}:{k[1]}': v for k,v in new_counts.items()},
        value_new_mismatches=new_bad,
        membership_counts=dict(membership),membership_examples=membership_examples,
        self_consistency_checked=self_checked,self_consistency_skipped=self_skipped,
        self_consistency_violations=self_bad,
        descent=descent,pure_roots=len(root_set),elapsed=time.monotonic()-start,
        tail_cache_sizes=(len(S._F_CACHE),len(S._INDUCED_CACHE),len(S._PERIODIC_CACHE)))
    out = HERE / ('pure-s39-sample.json.gz' if args.limit else 'pure-s39.json.gz')
    with gzip.open(out, 'wt', encoding='utf-8') as f:
        json.dump(report, f, ensure_ascii=False, separators=(',', ':'))
    print('RESULT', {k:v for k,v in report.items() if k not in
          ('order_violations','value_new_mismatches','self_consistency_violations',
           'membership_examples','descent')}, flush=True)
    print('ORDER', [(x['a_tokens'], x['a_value'], x['b_tokens'], x['b_value']) for x in order_bad[:20]], flush=True)
    print('VALUE_NEW', new_bad[:20], flush=True)
    print('SELF', self_bad[:20], flush=True)


if __name__ == '__main__':
    main()
