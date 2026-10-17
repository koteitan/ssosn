"""Audit the finite saved SSOS valuations in the 0021012101202 region.

All cached R/hook values in the seed are included. Current rule/real-sup
comparisons use the section 10 token/closure corpus. Standard membership uses
the same greedy descent as std.py, sharing its path across descending targets.
All missing values and finite-sample sup candidates remain conjectural.
"""
import argparse
from collections import Counter
import csv
import gzip
from functools import lru_cache
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
import evalord as E
from ordinal import ONE, cmp, show

PREFIX = tuple(map(int,'0021012101202'))
A = tuple(map(int,'002101210120201210121'))
B = tuple(map(int,'002101210120202'))


class Timeout(Exception):
    pass


def alarm(*_):
    raise Timeout


def txt(s):
    return ''.join(map(str,s))


def tu(x):
    return tuple(tu(y) for y in x) if isinstance(x,list) else x


def pretty(x):
    """Parenthesized Unicode notation for the small comparison tables."""
    if not x:return '0'
    groups=[]
    for t in x:
        if groups and groups[-1][0]==t:groups[-1][1]+=1
        else:groups.append([t,1])
    out=[]
    for (_,a,b),n in groups:
        if not a:term='1' if not b else 'ω' if b==ONE else 'ω^('+pretty(b)+')'
        elif a==ONE:term='e_('+pretty(b)+')'
        else:term='φ_('+pretty(a)+')('+pretty(b)+')'
        out.append(str(n) if term=='1' else term+('·'+str(n) if n>1 else ''))
    return '+'.join(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--seed', type=Path, required=True)
    ap.add_argument('--out-prefix', type=Path, default=Path('work/order-region'))
    ap.add_argument('--case-seconds', type=float, default=.05)
    ap.add_argument('--membership-from',type=Path,
                    help='reuse standard membership from a completed audit of the same definitions')
    args = ap.parse_args()
    rule6.USE_LIFT = rule6.EXT = rule6.MORE = True
    rule6.EXT121 = rule6.EXT121E = False
    rule6.MAXD = 7
    lift.unlift((2,1))
    with args.seed.open('rb') as f:
        state = pickle.load(f)
    assert state['signature']==('frontier-no-ii-v1',rule6.NS,True,True,rule6.MORE_DEPTH)
    rule6.memo,rule6.hmemo=state['memo'],state['hmemo']
    harness.fs=lru_cache(maxsize=40000)(harness.fs)
    rule6.is_selfref=lru_cache(maxsize=40000)(rule6.is_selfref)
    rule6.level=lru_cache(maxsize=40000)(rule6.level)
    rule6.conj2.T=lru_cache(maxsize=40000)(rule6.conj2.T)
    rule6.lower.lower=lambda u:None
    signal.signal(signal.SIGALRM,alarm)

    def probe(fun,budget=None):
        rule6.st.update(depth=0,taint=0)
        signal.setitimer(signal.ITIMER_REAL,budget or args.case_seconds)
        try:
            value=fun()
            status='missing' if rule6.st['taint'] else 'clean' if value is not None else 'none'
        except (Timeout,RecursionError):
            value,status=None,'timeout'
        finally:
            signal.setitimer(signal.ITIMER_REAL,0)
            rule6.st['depth']=0
        return {'status':status,'ordinal':value if status=='clean' else None,
                'rendered':show(value) if status=='clean' else None}

    rows={}

    def add(s,source,value):
        if s[:len(PREFIX)]!=PREFIX or value is None:
            return
        row=rows.setdefault(s,{})
        row[source]=value

    for s,value in list(rule6.memo.items()):
        add(s,'cache_R',value)
    for u,value in list(rule6.hmemo.items()):
        add((0,0)+u,'cache_hook',value)
    initial_cached=len(rows)

    # Keep the finite published sources separate; do not insert their values
    # into the evaluator caches or silently prefer one proposed value.
    for filename in ('ext121-independent-checked.json','ext121e-independent-checked.json'):
        report=json.loads((HERE/filename).read_text())
        for row in report['cases']:
            s=tuple(map(int,row['sequence']))
            for key in ('off_rule_after_warm','off_rule','off_real_sup'):
                value=row.get(key,{})
                if value.get('status')=='clean':
                    add(s,filename+':'+key,tu(value['ordinal']))
            if filename.startswith('ext121e') and row['on_rule']['status']=='clean':
                add(s,'published_rule_EXT121E',tu(row['on_rule']['ordinal']))
    root_report=HERE/'ext121e-roots-on.json'
    if root_report.exists():
        for row in json.loads(root_report.read_text())['rows']:
            if row['status']=='clean':
                add(tuple(map(int,row['sequence'])),'published_evaluator_EXT121E',tu(row['ordinal']))

    primary=set()
    seen=set()
    wave=[((),(2,1))]
    tokens={'A0':(0,1,2),'A1':(0,1,2,0,2),'A2':(0,1,2,0,2,0,2),'1':(1,)}
    for _ in range(9):
        nxt=[]
        for names,u in wave:
            for name,tk in tokens.items():
                if name=='1' and names and names[-1]=='1':continue
                v=u+tk;s=(0,0)+v
                if v in seen or s>=(0,0,2,1,0,2):continue
                seen.add(v)
                if not std.is_standard(s):continue
                nxt.append((names+(name,),v))
                if s[:len(PREFIX)]==PREFIX:primary.add(s)
        wave=nxt
    for s in harness.closure([(0,0,2,1,0,2)],maxlen=24):
        if s[:len(PREFIX)]==PREFIX and rule6.is_selfref(s[2:]):primary.add(s)
    primary.update((A,B))
    comparisons=[]
    for i,s in enumerate(sorted(primary)):
        row={'sequence':txt(s),'rule':probe(lambda:rule6.rules(s[2:])),
             'real_sup':probe(lambda:rule6.real_sup(s[2:])[0])}
        comparisons.append(row)
        for field in ('rule','real_sup'):
            v=row[field]
            if v['status']=='clean':add(s,field, v['ordinal'])
        if i%100==0:print('primary',i,'/',len(primary),flush=True)

    details=[]
    for s in (A,B):
        row={'sequence':txt(s),'standard':std.is_standard(s),'terms':[]}
        xs=[]
        for n in range(1,6):
            term=harness.fs(s,n)
            value=probe(lambda:rule6.R(term),.5)
            row['terms'].append({'n':n,'sequence':txt(term),'standard':std.is_standard(term),**value})
            if value['status']=='clean':add(term,'focused_term',value['ordinal'])
            xs.append(value['ordinal'])
        row['sup4']=E.sup(xs[:4]) if all(x is not None for x in xs[:4]) else None
        row['sup5']=E.sup(xs) if all(x is not None for x in xs) else None
        row['sup3']=rule6.sup3(xs) if all(x is not None for x in xs) else None
        details.append(row)

    # Greedy membership with a shared upper bound. Each target is smaller than
    # the last one, so the last known standard ceiling remains a valid top.
    top=std.TOP
    standard=set()
    steps=0
    ordered=sorted(rows,reverse=True)
    started=time.monotonic()
    known_standard=set()
    if args.membership_from:
        previous=json.loads(args.membership_from.read_text())
        with gzip.open(previous['files']['values'],'rt') as f:
            known_standard={tuple(map(int,row['sequence'])) for row in csv.DictReader(f,delimiter='\t')}
        assert len(known_standard)==previous['standard_sequences']
        standard.update(rows.keys()&known_standard)
    targets=ordered if not args.membership_from else [s for s in ordered if s not in known_standard]
    for i,s in enumerate(targets):
        for _ in range(100000):
            if top==s:
                standard.add(s)
                break
            assert top>s
            if top[-1]==0:
                nxt=top[:-1]
                if nxt<s:break
            else:
                cut=harness.Seq(top,'new').cut()
                g,block=top[:cut],top[cut:-1]+(top[-1]-1,)
                if std.above_all_terms(g,block,s):break
                lo,hi=1,len(s)//len(block)+2
                while lo<hi:
                    mid=(lo+hi)//2
                    if g+block*mid>=s:hi=mid
                    else:lo=mid+1
                nxt=g+block*lo
            top=nxt
            steps+=1
        else:
            raise RuntimeError('membership step cap reached')
        if i%5000==0:
            print('standard',i,'/',len(ordered),'accepted',len(standard),
                  'seconds',round(time.monotonic()-started),flush=True)
    # Compare the shared-path algorithm against the original implementation,
    # including endpoints, the primary corpus and evenly spaced long cases.
    # Targets without any value are outside this membership audit; they have
    # already passed the token generator's separate standard-form check.
    sample=(set(primary)&rows.keys())|{ordered[i] for i in range(0,len(ordered),max(1,len(ordered)//40))}
    for s in sample:
        assert std.is_standard(s)==(s in standard),txt(s)
    ordered=sorted(standard)

    paths={name:args.out_prefix.with_name(args.out_prefix.name+'-'+name+
                                        ('.tsv' if name in ('status','primary-adjacent','compatible','problems') else '.tsv.gz'))
           for name in ('values','adjacent','sup-witnesses','status','primary-adjacent','compatible','problems')}
    with gzip.open(paths['values'],'wt') as f:
        writer=csv.writer(f,delimiter='\t')
        writer.writerow(('sequence','source','ordinal'))
        for s in ordered:
            for source,value in rows[s].items():writer.writerow((txt(s),source,show(value)))

    adjacent_counts=Counter()
    bad_sequences=set()
    channels=('cache_R','cache_hook','rule','real_sup','combined')
    with gzip.open(paths['adjacent'],'wt') as f:
        writer=csv.writer(f,delimiter='\t')
        writer.writerow(('channel','left','left_source','left_value','right','right_source','right_value','comparison'))
        for channel in channels:
            seqs=[s for s in ordered if channel=='combined' or channel in rows[s]]
            for left,right in zip(seqs,seqs[1:]):
                lv=rows[left] if channel=='combined' else {channel:rows[left][channel]}
                rv=rows[right] if channel=='combined' else {channel:rows[right][channel]}
                ls,lx=max(lv.items(),key=lambda kv:E._Key(kv[1]))
                rs,rx=min(rv.items(),key=lambda kv:E._Key(kv[1]))
                comparison=cmp(lx,rx)
                if comparison>=0:
                    writer.writerow((channel,txt(left),ls,show(lx),txt(right),rs,show(rx),comparison))
                    adjacent_counts[channel]+=1
                    bad_sequences.update((left,right))

    primary_adjacent_counts=Counter()
    with paths['primary-adjacent'].open('w') as f:
        writer=csv.writer(f,delimiter='\t')
        writer.writerow(('channel','left','left_value','right','right_value','comparison'))
        for channel in channels:
            seqs=[s for s in ordered if s in primary and (channel=='combined' or channel in rows[s])]
            for left,right in zip(seqs,seqs[1:]):
                lv=rows[left] if channel=='combined' else {channel:rows[left][channel]}
                rv=rows[right] if channel=='combined' else {channel:rows[right][channel]}
                lx=max(lv.values(),key=E._Key)
                rx=min(rv.values(),key=E._Key)
                comparison=cmp(lx,rx)
                if comparison>=0:
                    writer.writerow((channel,txt(left),show(lx),txt(right),show(rx),comparison))
                    primary_adjacent_counts[channel]+=1

    # Prefix maxima/suffix minima test ALL larger/lower known sequences in O(N),
    # rather than limiting a sup warning to its immediate neighbour.
    premax=[]
    best=None
    for s in ordered:
        premax.append(best)
        for source,value in rows[s].items():
            if best is None or cmp(value,best[2])>0:best=(s,source,value)
    suffix=[None]*len(ordered)
    best=None
    for i in range(len(ordered)-1,-1,-1):
        suffix[i]=best
        for source,value in rows[ordered[i]].items():
            if best is None or cmp(value,best[2])<0:best=(ordered[i],source,value)
    indices={s:i for i,s in enumerate(ordered)}
    sup_warnings=[]
    with gzip.open(paths['sup-witnesses'],'wt') as f:
        writer=csv.writer(f,delimiter='\t')
        writer.writerow(('sequence','sup_source','sup_value','larger_sequence','larger_source','larger_value'))
        for s in ordered:
            witness=suffix[indices[s]]
            if witness is None:continue
            for source,value in rows[s].items():
                if 'real_sup' not in source:continue
                if cmp(value,witness[2])>=0:
                    writer.writerow((txt(s),source,show(value),txt(witness[0]),witness[1],show(witness[2])))
                    sup_warnings.append({'sequence':txt(s),'source':source,'witness':txt(witness[0])})

    statuses=[]
    with paths['status'].open('w') as f, paths['compatible'].open('w') as good, paths['problems'].open('w') as bad:
        writer=csv.writer(f,delimiter='\t')
        good_writer,bad_writer=csv.writer(good,delimiter='\t'),csv.writer(bad,delimiter='\t')
        header=('sequence','status','rule','real_sup','earlier_witness','later_witness')
        for w in (writer,good_writer,bad_writer):w.writerow(header)
        for row in comparisons:
            s=tuple(map(int,row['sequence']))
            if s not in standard:continue
            rule,real=row['rule'],row['real_sup']
            i=indices[s]
            earlier,later=premax[i],suffix[i]
            same=rule['status']==real['status']=='clean' and rule['ordinal']==real['ordinal']
            value=rule['ordinal'] if same else None
            before=earlier is not None and value is not None and cmp(earlier[2],value)>=0
            after=later is not None and value is not None and cmp(value,later[2])>=0
            local_conflict=value is not None and any(v!=value for v in rows[s].values())
            status=('consistent_and_matched' if same and not(before or after or local_conflict)
                    else 'matched_but_order_conflict' if same else
                    'rule_sup_differ' if rule['status']==real['status']=='clean' else 'unresolved')
            row['order_status']=status
            statuses.append(row)
            writer.writerow((txt(s),status,rule['rendered'],real['rendered'],
                             txt(earlier[0]) if before else '',txt(later[0]) if after else ''))
            chosen=good_writer if status=='consistent_and_matched' else bad_writer
            chosen.writerow((txt(s),status,
                             pretty(rule['ordinal']) if rule['status']=='clean' else rule['status'],
                             pretty(real['ordinal']) if real['status']=='clean' else real['status'],
                             txt(earlier[0]) if before else '',txt(later[0]) if after else ''))

    report={'prefix':txt(PREFIX),'initial_cached_sequences':initial_cached,
            'valued_sequences':len(rows),'standard_sequences':len(standard),
            'nonstandard_sequences':len(rows)-len(standard),'primary':len(primary),
            'membership_steps':steps,'membership_sample_checked':len(sample),
            'membership_reused':len(rows.keys()&known_standard),
            'adjacent_counts':dict(adjacent_counts),'sup_warning_count':len(sup_warnings),
            'primary_adjacent_counts':dict(primary_adjacent_counts),
            'sup_warnings':sup_warnings,'statuses':dict(Counter(x['order_status'] for x in statuses)),
            'comparisons':statuses,'focused':details,'hypothesis_II_executed':False,
            'EXT121':False,'EXT121E':False,
            'files':{k:str(v) for k,v in paths.items()}}
    # The complete value matrix is large. Violation lists are small enough to
    # provide readable TSV copies as well as the compressed audit artifacts.
    for name in ('adjacent','sup-witnesses'):
        plain=paths[name].with_suffix('')
        with gzip.open(paths[name],'rb') as f:
            plain.write_bytes(f.read())
        report['files'][name+'_plain']=str(plain)
    args.out_prefix.with_suffix('.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print('FINAL',{k:report[k] for k in ('standard_sequences','adjacent_counts','sup_warning_count','statuses')},flush=True)


if __name__=='__main__':
    main()
