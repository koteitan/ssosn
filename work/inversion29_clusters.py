"""Cluster the measured roots; extra comparisons are evidence, not value fixes."""
import collections
import gzip
import json
import harness
import std
import token_tree as T
import evalord as E
from ordinal import cmp
from above_p_data26 import HERE,raw
from token_targets import pretty
from self_consistency28 import configure


def main():
    configure('seed')
    data=json.load(gzip.open(HERE/'inversion29.json.gz','rt'))
    assert data['complete']
    base=json.load(gzip.open(HERE/'above-p26-data.json.gz','rt'))
    standard_raw={raw(row['tokens']) for row in base['rows'] if row['standard']}
    groups=collections.defaultdict(list)
    for row in data['rows']:
        r=row['result'];assert r['status']=='term_root'
        ts=tuple(r['parent_shape']['tokens'])
        j=max(i for i,t in enumerate(ts) if t.startswith(('A','E')))
        groups[(ts[j],tuple(ts[j+1:]))].append(row)
    primary=set();primary_rows=set()
    for i,row in enumerate(data['rows']):
        source=tuple(row['source'])
        if source not in primary:primary_rows.add(i);primary.add(source)
    row_indices={id(row):i for i,row in enumerate(data['rows'])}
    def probe(s):
        s=tuple(s)
        try:
            v=T.value(s)
            if std.is_standard(s):
                xs=[T.value(harness.fs(s,n)) for n in range(1,6)]
                inferred=E.sup(xs)
                diagnostics=dict(all5_below=all(cmp(x,v)<0 for x in xs),
                    inferred_sup=None if inferred is None else pretty(inferred),
                    inference_equal=None if inferred is None else cmp(inferred,v)==0)
            else:diagnostics={}
            return dict(raw=s,value=pretty(v),standard=std.is_standard(s),**diagnostics)
        except T.Unknown as error:return dict(raw=s,unknown=str(error))
    summaries=[]
    for number,(signature,rows) in enumerate(sorted(groups.items(),key=lambda item:-len(item[1])),1):
        representative=min(rows,key=lambda row:(len(row['result']['parent_shape']['tokens']),
            tuple(row['result']['parent_shape']['tokens']),row['result']['n']))
        result=representative['result'];s=tuple(result['b']);term=tuple(result['term'])
        ts=tuple(result['parent_shape']['tokens']);parent=T.value(s)
        examples={}
        last=ts[-1]
        if last in ('D','W'):
            prefix=raw(ts[:-1]);examples['prefix']=probe(prefix)
            examples['prefix']['vs_parent']=cmp(T.value(prefix),parent)
        if last=='W':
            end=len(ts)
            while ts[end-1]=='W':end-=1
            upper=raw(ts[:end]+('D',));examples['larger_D']=probe(upper)
            examples['larger_D']['parent_vs_upper']=cmp(parent,T.value(upper))
            terminal=tuple(result['child_shape']['terminal'])
            core=term[:-len(terminal)] if terminal else term
            examples['term_core']=probe(core)
            examples['term_core'].update(raw_less_upper=core<upper,
                vs_upper=cmp(T.value(core),T.value(upper)),vs_parent=cmp(T.value(core),parent))
            actual_upper=upper if examples['larger_D']['standard'] else std.ceil(upper)
            examples['larger_standard_bound']=probe(actual_upper)
            examples['larger_standard_bound'].update(term_core_raw_below=core<actual_upper,
                term_core_vs_bound=cmp(T.value(core),T.value(actual_upper)))
            if signature==('A0',('W','D','D','W')):
                first_a2=raw(ts[:-1]+('A2',))
                examples['first_A2']=probe(first_a2)
                examples['first_A2'].update(raw_below_bound=first_a2<actual_upper,
                    vs_bound=cmp(T.value(first_a2),T.value(actual_upper)))
        if last.startswith('A') and int(last[1:])>0:
            lower=raw(ts[:-1]+('A'+str(int(last[1:])-1),))
            examples['lowered_A']=probe(lower)
            examples['lowered_A']['vs_parent']=cmp(T.value(lower),parent)
        if last=='D' and examples['prefix'].get('vs_parent',-1)>=0:
            judgement='parent_too_small_relative_to_prefix'
        elif 'lowered_A' in examples and examples['lowered_A']['vs_parent']>=0:
            judgement='parent_too_small_relative_to_lowered_A'
        elif ('larger_standard_bound' in examples and examples['larger_standard_bound']['standard']
              and examples['larger_standard_bound']['term_core_raw_below']
              and examples['larger_standard_bound']['term_core_vs_bound']>=0):
            judgement='term_too_large_relative_to_D_bound'
        elif 'prefix' in examples and examples['prefix']['vs_parent']>=0:
            judgement='parent_too_small_relative_to_prefix'
        else:
            judgement='not_decided_by_these_comparisons'
            if signature==('A1',('W','D','D','W','W')):
                origin=T.Origin('cluster 10 stored versus active seed')
                copy=('W','D','D','W')
                stored=T.typed_copy_rank(copy,0,origin)
                active=T.typed_copy_rank(copy,1,origin)
                examples['copy_rank_comparison']=dict(copy=copy,
                    stored_depth0=pretty(T.ordinal(stored)),active_depth1=pretty(T.ordinal(active)),
                    stored_vs_active=cmp(T.ordinal(stored),T.ordinal(active)))
                judgement='term_promotion_suspected_depth0_rank_not_a_proof'
        summaries.append(dict(id=number,signature=signature,pairs=len(rows),
            spelling_routes=sum(r['weight'] for r in rows),
            primary_spellings=sum(r['weight'] for r in rows if row_indices[id(r)] in primary_rows),
            parents=len({tuple(r['result']['b']) for r in rows}),
            parent_n_roots=len({(tuple(r['result']['b']),r['result']['n']) for r in rows}),
            n_counts=dict(collections.Counter(r['result']['n'] for r in rows)),
            representative=result,comparisons=examples,judgement=judgement))
    roots={tuple(r['result']['b']) for r in data['rows']}
    report=dict(summary={k:v for k,v in data.items() if k!='rows'},clusters=summaries,
        unique_parent_roots=len(roots),unique_parent_n_roots=len({(tuple(r['result']['b']),r['result']['n']) for r in data['rows']}),
        roots_inside_N9=len(roots&standard_raw),roots_outside_N9=len(roots-standard_raw),
        max_steps=max(r['steps'] for r in data['rows']),
        max_n=max(step.get('n',0) for r in data['rows'] for step in r['path']),
        max_root_token_length=max(len(r['result']['parent_shape']['tokens']) for r in data['rows']),
        global_root_n_counts=dict(collections.Counter(r['result']['n'] for r in data['rows'])))
    (HERE/'inversion29-clusters.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    for c in summaries:
        print('CLUSTER',c['id'],c['signature'],'pairs',c['pairs'],'weighted',c['spelling_routes'],
            'primary',c['primary_spellings'],'parents',c['parents'],'n',c['n_counts'],c['judgement'],flush=True)
        r=c['representative'];print(' root',r['parent_shape'],'n',r['n'],r['parent'],'=>',r['child_shape'],r['child'],flush=True)
        for name,example in c['comparisons'].items():print(' comparison',name,example,flush=True)
    print('TOTAL',{k:v for k,v in report.items() if k not in ('summary','clusters')},flush=True)


if __name__=='__main__':main()
