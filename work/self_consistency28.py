"""Finite real-term checks; sup() results are heuristic diagnostics, not proofs.

timeout 600 python3 work/self_consistency28.py seed [--resume]
timeout 600 python3 work/self_consistency28.py iterate [--resume]
Each invocation checkpoints and exits after --budget seconds; resume until complete.
"""
import argparse
import collections
from functools import lru_cache
import gzip
import json
import time

from above_p_data26 import HERE,raw
import harness
import token_tree as T
import evalord as E
from ordinal import cmp,cmp_p,fs as ordinal_fs
from token_targets import pretty


def configure(variant):
    T.CUT_COPY_ACTION_EXPERIMENT=True
    T.CONSISTENT_COPY_SEED_EXPERIMENT=True
    T.WD_AFTER_ITERATION_EXPERIMENT=variant=='iterate'
    T.MOVABLE_ONE_EXPERIMENT=False
    T.GENERAL_COPY_EXPERIMENT=False


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('variant',choices=('seed','iterate'))
    parser.add_argument('--resume',action='store_true')
    parser.add_argument('--budget',type=float,default=520)
    parser.add_argument('--limit',type=int)
    args=parser.parse_args()
    configure(args.variant)
    with gzip.open(HERE/'above-p26-data.json.gz','rt') as source:data=json.load(source)
    labels={}
    for row in data['rows']:
        if row['standard']:
            w=tuple(row['tokens']);s=raw(w)
            if s not in labels or (len(w),w)<(len(labels[s]),labels[s]):labels[s]=w
    ordered=sorted(labels,key=lambda s:(len(labels[s]),labels[s]))
    if args.limit is not None:ordered=ordered[:args.limit]
    suffix='' if args.limit is None else f'-first{args.limit}'
    out=HERE/f'self28-{args.variant}{suffix}.json.gz'
    if args.resume:
        with gzip.open(out,'rt') as source:report=json.load(source)
        assert report['total']==len(ordered) and report['variant']==args.variant
    else:
        report=dict(variant=args.variant,total=len(ordered),processed=0,complete=False,
            counts={},failures=[],failed_words=[],unknown_examples=[],sup_differ_examples=[],
            elapsed_seconds=0,sup_method='evalord.sup of 5 samples; inferred diagnostic, not an exact supremum proof')
    counts=collections.Counter(report['counts'])
    start=time.monotonic();prior=report['elapsed_seconds'];calls=0
    @lru_cache(maxsize=32768)
    def evaluate(s):
        nonlocal calls
        calls+=1
        try:value=T.value(s)
        except T.Unknown:return None
        if calls%512==0:
            T.value_tree.cache_clear();T.body_tree.cache_clear();T.block_tree.cache_clear()
        if calls%4096==0:
            cmp.cache_clear();cmp_p.cache_clear();ordinal_fs.cache_clear()
        return value
    def save():
        report['counts']=dict(counts)
        report['elapsed_seconds']=prior+time.monotonic()-start
        pending=out.with_name(out.name+'.pending')
        with gzip.open(pending,'wt') as target:json.dump(report,target,ensure_ascii=False,separators=(',',':'))
        pending.replace(out)
    for i in range(report['processed'],len(ordered)):
        s=ordered[i];word=labels[s]
        parent=evaluate(s)
        cut=harness.Seq(s,'new').cut();g,b=s[:cut],s[cut:-1]+(s[-1]-1,)
        terms=[g+b*n for n in range(1,6)]
        xs=[evaluate(term) for term in terms]
        if parent is None or any(x is None for x in xs):
            counts['Unknown']+=1
            if len(report['unknown_examples'])<20:
                report['unknown_examples'].append(dict(tokens=word,raw=s,parent_unknown=parent is None,
                    unknown_terms=[n for n,x in enumerate(xs,1) if x is None]))
        else:
            below=all(cmp(x,parent)<0 for x in xs)
            increasing=all(cmp(a,b)<0 for a,b in zip(xs,xs[1:]))
            counts['below_all' if below else 'term_not_below_parent']+=1
            counts['terms_increasing' if increasing else 'terms_not_increasing']+=1
            if not below or not increasing:
                report['failed_words'].append(word)
                if len(report['failures'])<20:
                    report['failures'].append(dict(tokens=word,raw=s,parent=pretty(parent),
                        below_all=below,increasing=increasing,terms=[dict(n=n,raw=t,value=pretty(x),
                        vs_parent=cmp(x,parent)) for n,(t,x) in enumerate(zip(terms,xs),1)]))
            guessed=E.sup(xs)
            if guessed is None:counts['sup_inference_unresolved']+=1
            elif cmp(guessed,parent)==0:counts['sup_inference_agree']+=1
            else:
                counts['sup_inference_differ']+=1
                if len(report['sup_differ_examples'])<10:
                    report['sup_differ_examples'].append(dict(tokens=word,parent=pretty(parent),
                        inferred_sup=pretty(guessed),terms=[pretty(x) for x in xs]))
        report['processed']=i+1
        if (i+1)%1000==0:
            save();print(args.variant,i+1,dict(counts),'seconds',round(report['elapsed_seconds'],1),flush=True)
        if time.monotonic()-start>=args.budget:break
    report['complete']=report['processed']==len(ordered)
    save()
    print('FINAL',args.variant,'complete',report['complete'],'processed',report['processed'],
          'counts',dict(counts),'seconds',round(report['elapsed_seconds'],2),flush=True)


if __name__=='__main__':main()
