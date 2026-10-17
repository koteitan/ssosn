"""Fresh NOREGION evaluation, checkpointed missing-block warming, and order audit.

Only a state created by this script can resume evaluation. Old valuations are
loaded after the new calculation and used only as a separate comparison.
"""
import argparse
from collections import Counter
import csv
from functools import lru_cache
import gzip
import heapq
import json
from pathlib import Path
import pickle
import signal
import sys
import time

HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE),str(HERE.parent)]
import harness
import lift
import rule6
import std
import evalord as E
from ordinal import cmp,show
from order_region import pretty

PREFIX=(0,0)+rule6.NO_REGION_PREFIX
SUBJECTS=('0021012101202','00210121012020121','002101210120201210121','002101210120202')
THREE=('002101210120210121012021','002101210121','002102')


class Timeout(Exception):pass
def alarm(*_):raise Timeout
def txt(s):return ''.join(map(str,s))


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--state',type=Path,required=True)
    ap.add_argument('--results',type=Path,required=True)
    ap.add_argument('--seconds',type=float,default=30)
    ap.add_argument('--tokens',type=int,default=9)
    ap.add_argument('--depth',type=int,default=7)
    ap.add_argument('--job-seconds',type=float,default=.08)
    ap.add_argument('--max-block',type=int,default=500)
    ap.add_argument('--old-seed',type=Path)
    ap.add_argument('--roots',action='store_true')
    ap.add_argument('--ext121e',action='store_true')
    ap.add_argument('--rellift',action='store_true')
    ap.add_argument('--seed-noregion',type=Path,
                    help='seed a new RELLIFT run only with an independent NOREGION state')
    ap.add_argument('--max-jobs',type=int,default=100000)
    ap.add_argument('--focus',nargs='*',default=[])
    ap.add_argument('--order',choices=('length','lex'),default='length')
    args=ap.parse_args()
    rule6.USE_LIFT=rule6.EXT=rule6.MORE=rule6.NOREGION=True
    rule6.EXT121=False
    rule6.EXT121E=args.ext121e
    rule6.RELLIFT=args.rellift
    rule6.MAXD=args.depth
    lift.unlift((2,1))
    off_signature=('noregion-no-II-v1',args.depth,rule6.NS,rule6.MORE_DEPTH,args.ext121e)
    signature=(('rellift-no-II-v2',)+off_signature[1:]) if args.rellift else off_signature
    state={'signature':signature,'memo':{},'hmemo':{},'pending':set(),
           'attempts':{},'timeouts':0,'runs':0,'root_status':{}}
    if args.state.exists():
        with args.state.open('rb') as f:state=pickle.load(f)
        if state['signature']!=signature:ap.error('incompatible NOREGION state')
    elif args.seed_noregion:
        if not args.rellift:ap.error('--seed-noregion requires --rellift')
        with args.seed_noregion.open('rb') as f:seed=pickle.load(f)
        if seed['signature']!=off_signature:ap.error('incompatible independent NOREGION seed')
        state['memo'],state['hmemo']=seed['memo'],seed['hmemo']
        state['pending']=seed['pending']
        state['independent_seed_values']=len(seed['memo'])+len(seed['hmemo'])
    rule6.memo,rule6.hmemo=state['memo'],state['hmemo']
    new_caches=(rule6.memo,rule6.hmemo)
    # No old valuation is read before the new computation/checkpoint.
    harness.fs=lru_cache(maxsize=8000)(harness.fs)
    rule6.is_selfref=lru_cache(maxsize=16000)(rule6.is_selfref)
    rule6.level=lru_cache(maxsize=16000)(rule6.level)
    rule6.conj2.T=lru_cache(maxsize=16000)(rule6.conj2.T)
    missing=Counter()
    def lower_disabled(u):
        missing[tuple(u)]+=1
        return None
    rule6.lower.lower=lower_disabled
    signal.signal(signal.SIGALRM,alarm)

    def probe(s,budget):
        rule6.st.update(depth=0,taint=0)
        missing.clear()
        signal.setitimer(signal.ITIMER_REAL,max(.001,budget))
        try:
            value=rule6.R(s)
            status='clean' if value is not None and not rule6.st['taint'] else 'missing'
        except (Timeout,RecursionError):
            value,status=None,'timeout'
            state['timeouts']+=1
        finally:
            signal.setitimer(signal.ITIMER_REAL,0)
            rule6.st['depth']=0
        return status,list(missing)

    base=(2,1,0,1,2,1)
    tokens={'A0':(0,1,2),'A1':(0,1,2,0,2),'A2':(0,1,2,0,2,0,2),'1':(1,)}
    wave=[((),base)];seen=set();corpus={};counts=[]
    for _ in range(args.tokens):
        nxt=[];n=0
        for names,u in wave:
            for name,tk in tokens.items():
                if name=='1' and names and names[-1]=='1':continue
                v=u+tk;s=(0,0)+v
                if v in seen:continue
                seen.add(v)
                if not std.is_standard(s):continue
                nxt.append((names+(name,),v))
                if s[:len(PREFIX)]==PREFIX:
                    corpus[s]=names+(name,);n+=1
        counts.append(n);wave=nxt
    roots=sorted(corpus,key=lambda s:(len(s),s))
    for text in SUBJECTS:
        assert tuple(map(int,text)) in corpus,text
    if args.roots:roots+=list(map(lambda x:tuple(map(int,x)),THREE))
    pending=state['pending'];attempts=state['attempts']
    for s in roots:
        pending.add(s)
        for i in range(3,len(s)):
            if s[i-1]!=0:pending.add(s[:i])
    queue=[];scheduled=set();visited=set()
    workset=set()
    def enqueue(s):
        if len(s)>args.max_block or rule6.memo.get(s) is not None:return
        pending.add(s)
        workset.add(s)
        if s not in visited and s not in scheduled:
            first=s if args.order=='lex' else len(s)
            heapq.heappush(queue,(first,attempts.get(s,0),s));scheduled.add(s)
    if args.focus:
        for text in args.focus:
            s=tuple(map(int,text));enqueue(s)
            for n in range(1,6):
                term=harness.fs(s,n)
                for i in range(3,len(term)+1):
                    if term[i-1]!=0:enqueue(term[:i])
    else:
        for s in pending:enqueue(s)
    before=len(rule6.memo)+len(rule6.hmemo)
    generation=before
    started=time.monotonic();deadline=started+args.seconds
    jobs=0
    print('corpus',len(corpus),'per token',counts,'resume',state['runs'],
          'R',len(rule6.memo),'hook',len(rule6.hmemo),flush=True)
    while time.monotonic()<deadline and jobs<args.max_jobs:
        if not queue:
            version=sum(x is not None for x in rule6.memo.values())+sum(x is not None for x in rule6.hmemo.values())
            if version<=generation:break
            generation=version;visited.clear()
            for s in list(workset):enqueue(s)
            if not queue:break
        _,_,s=heapq.heappop(queue);scheduled.discard(s)
        if rule6.memo.get(s) is not None:
            pending.discard(s);continue
        visited.add(s);attempts[s]=attempts.get(s,0)+1
        status,frontier=probe(s,min(args.job_seconds,max(.001,deadline-time.monotonic())))
        if s in corpus:state['root_status'][s]=status
        if status=='clean':pending.discard(s)
        for u in frontier:
            enqueue((0,0)+u)
        jobs+=1
    # Cheap final probes benefit from dependencies warmed by later cases.
    for s in roots:
        if rule6.memo.get(s) is None:
            status,_=probe(s,.003)
            if s in corpus:state['root_status'][s]=status
    state['memo']={s:x for s,x in rule6.memo.items() if x is not None}
    state['hmemo']={s:x for s,x in rule6.hmemo.items() if x is not None}
    rule6.memo,rule6.hmemo=state['memo'],state['hmemo']
    new_caches=(rule6.memo,rule6.hmemo)
    pending.difference_update(state['memo'])
    state['runs']+=1
    state['last_seconds']=time.monotonic()-started
    state['total_seconds']=state.get('total_seconds',0)+state['last_seconds']
    state['total_jobs']=state.get('total_jobs',0)+jobs
    args.state.parent.mkdir(parents=True,exist_ok=True)
    temp=args.state.with_suffix('.tmp')
    with temp.open('wb') as f:pickle.dump(state,f)
    temp.replace(args.state)
    report={'method':'NOREGION with bounded relative lift, II disabled' if args.rellift else 'fresh NOREGION, II disabled, real-term sups in region',
            'RELLIFT':args.rellift,
            'NOREGION':True,'EXT121':False,'EXT121E':args.ext121e,'depth':args.depth,
            'NS':rule6.NS,'per_token':counts,'corpus':len(corpus),
            'runs':state['runs'],'jobs':jobs,'total_jobs':state['total_jobs'],
            'total_seconds':state['total_seconds'],'R':len(state['memo']),'hook':len(state['hmemo']),
            'pending':len(pending),'timeouts':state['timeouts'],'rows':[],'three_roots':[]}
    # Keep old values in an independent evaluator. They are never copied into
    # state.memo/hmemo, and this stage runs only after checkpointing the new state.
    old=None
    if args.old_seed:
        with args.old_seed.open('rb') as f:old=pickle.load(f)
    for s in sorted(corpus):
        x=state['memo'].get(s)
        row={'sequence':txt(s),'tokens':corpus[s],'ordinal':x,
             'rendered':show(x) if x is not None else None,
             'status':'clean' if x is not None else state['root_status'].get(s,'unvisited')}
        if old is not None and x is not None:
            rule6.NOREGION=False;rule6.EXT121E=False
            rule6.RELLIFT=False
            rule6.memo,rule6.hmemo=old['memo'],old['hmemo']
            rule6.st.update(depth=0,taint=0)
            signal.setitimer(signal.ITIMER_REAL,.025)
            try:
                y=rule6.rules(s[2:]);clean=not rule6.st['taint']
                row['old_rule']=y if clean else None
                row['old_rule_status']='clean' if clean and y is not None else 'unknown'
            except (Timeout,RecursionError):
                row['old_rule']=None;row['old_rule_status']='timeout'
            finally:
                signal.setitimer(signal.ITIMER_REAL,0);rule6.st['depth']=0
            row['old_R']=old['memo'].get(s)
            row['old_hook']=old['hmemo'].get(s[2:])
        report['rows'].append(row)
    rule6.memo,rule6.hmemo=new_caches
    rule6.NOREGION=True;rule6.EXT121E=args.ext121e
    rule6.RELLIFT=args.rellift
    clean=[r for r in report['rows'] if r['ordinal'] is not None]
    violations=[]
    for left,right in zip(clean,clean[1:]):
        if cmp(left['ordinal'],right['ordinal'])>=0:
            violations.append({'left':left['sequence'],'left_ordinal':left['ordinal'],
                               'right':right['sequence'],'right_ordinal':right['ordinal']})
    report['resolved']=len(clean);report['unresolved']=len(corpus)-len(clean)
    report['adjacent_violations']=violations
    report['subjects']=[next(r for r in report['rows'] if r['sequence']==s) for s in SUBJECTS]
    for text in THREE:
        s=tuple(map(int,text));x=state['memo'].get(s)
        report['three_roots'].append({'sequence':text,'ordinal':x,'rendered':show(x) if x is not None else None})
    args.results.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    with args.results.with_suffix('.tsv').open('w') as f:
        writer=csv.writer(f,delimiter='\t');writer.writerow(('sequence','tokens','status','value','old_rule','old_R'))
        for row in report['rows']:
            def render(x):return pretty(x) if x is not None else ''
            writer.writerow((row['sequence'],' '.join(row['tokens']),row['status'],
                             render(row['ordinal']),render(row.get('old_rule')),render(row.get('old_R'))))
    print('FINAL resolved',len(clean),'unresolved',report['unresolved'],'adjacent violations',len(violations),
          'R',len(state['memo']),'hook',len(state['hmemo']),'jobs',jobs,'pending',len(pending),flush=True)
    print('subjects',[(r['sequence'],r['rendered']) for r in report['subjects']],flush=True)


if __name__=='__main__':main()
