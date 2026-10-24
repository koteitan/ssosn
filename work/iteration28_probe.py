"""Exact copy-word tests and numeric diagnostics for W after W D^b."""
import gzip
import json
import time
import harness
import std
import evalord as E
import token_tree as T
from above_p_data26 import HERE,raw
from ordinal import cmp
from token_targets import pretty
from self_consistency28 import configure


def match(tokens,require_depth=True,single_d_run=True):
    end=len(tokens)
    while end and tokens[end-1]=='W':end-=1
    m=len(tokens)-end
    lower=end
    while lower and tokens[lower-1]=='D':lower-=1
    if not m or lower==end or not lower or tokens[lower-1]!='W':return None
    pos=lower-1
    while pos>=0 and tokens[pos] in ('W','D'):pos-=1
    if pos<0 or not tokens[pos].startswith('A'):return None
    if single_d_run and any(t!='W' for t in tokens[pos+1:lower]):return None
    k=int(tokens[pos][1:]);b=end-lower
    if require_depth and k>=b:return None
    return b,m,k


def main():
    start=time.monotonic()
    data=json.load(gzip.open(HERE/'above-p26-data.json.gz','rt'))
    sequences={raw(r['tokens']) for r in data['rows'] if r['standard']}
    counts={'parents':0,'terms':0,'differ':0};failures=[]
    for s in sorted(sequences):
        tokens=T.parse(s[4:],True)
        result=match(tokens)
        if result is None:continue
        b,m,k=result;counts['parents']+=1
        c=harness.Seq(s,'new').cut();g,repeat=s[:c],s[c:-1]+(s[-1]-1,)
        h=raw(tokens[:-1]);q=T.raw_tokens(('A'+str(b),)+('W',)*(m-1))
        for n in range(1,6):
            actual=g+repeat*n
            expected=h+q*(n-1)+T.A(0)+(0,)
            counts['terms']+=1
            if actual!=expected:
                counts['differ']+=1
                if len(failures)<20:failures.append(dict(tokens=tokens,b=b,m=m,k=k,n=n,actual=actual,expected=expected))
    print('syntactic law',counts,'first failures',failures[:2],flush=True)
    x=('D','D','D','A0')
    targets={'X_WDD':x+('W','D','D'),'X_WDDW':x+('W','D','D','W'),
        'X_WDDD':x+('W','D','D','D'),
        'X_WDD_A2':x+('W','D','D','A2'),'R':x+('W','D','D','W','A2'),
        'S0':('D','D','D','A1'),'S92':('D','W','A2','A1'),
        'B92':('D','W','A2','A0','W','D','W','A2','A0'),
        'C92':('D','W','A2','A0','W','D','W','A2','A1'),
        'Q1':('D','W','A1','W','D','W','W'),
        'Q2':('D','W','A2','W','D','W','W')}
    report=dict(law=dict(counts=counts,failures=failures,
        condition='last atom A_k followed by operators ending W D^b W^m, k<b, m>=1',
        proposed='S[n]=S without last W + (A_b W^(m-1))^(n-1) + A0 0'),variants={})
    excluded=('D','D','A0','W','D','W','W','D','W')
    excluded_raw=raw(excluded)
    actual=harness.fs(excluded_raw,2)
    expected=raw(excluded[:-1])+T.A(1)+T.A(0)+(0,)
    report['excluded_composite_counterexample']=dict(tokens=excluded,
        standard=std.is_standard(excluded_raw),n=2,
        actual=T.parse(actual[4:-1],True),expected=T.parse(expected[4:-1],True),
        equal=actual==expected,condition_matches=match(excluded) is not None)
    for variant in ('seed','iterate'):
        configure(variant);T.value_tree.cache_clear();T.body_tree.cache_clear();T.block_tree.cache_clear()
        rows={}
        for name,tokens in targets.items():
            s=raw(tokens);parent=T.value(s);terms=[];xs=[]
            for n in range(1,6):
                term=harness.fs(s,n)
                try:
                    v=T.value(term);xs.append(v)
                    t=dict(n=n,raw=term,value=pretty(v),vs_parent=cmp(v,parent),standard=std.is_standard(term))
                except T.Unknown as error:xs.append(None);t=dict(n=n,raw=term,unknown=str(error))
                try:t['tokens']=T.parse(term[4:-1 if tokens[-1]=='W' else -2],True)
                except T.Unknown:pass
                terms.append(t)
            inferred=E.sup(xs) if all(v is not None for v in xs) else None
            c=harness.Seq(s,'new').cut()
            rows[name]=dict(tokens=tokens,raw=s,standard=std.is_standard(s),parent=pretty(parent),
                terms=terms,cut=c,G=s[:c],B=s[c:-1]+(s[-1]-1,),
                inferred_sup=None if inferred is None else pretty(inferred),
                sup_inference_equal=None if inferred is None else cmp(inferred,parent)==0,
                depth_guard=match(tokens,False,False))
        report['variants'][variant]=rows
        p=T.value(raw(targets['X_WDDW']));s0=T.value(raw(targets['S0']))
        report.setdefault('parent_comparisons',{})[variant]=dict(
            X_WDDW_vs_X_WDDD=cmp(p,T.value(raw(targets['X_WDDD']))),
            X_WDDW_vs_S0=cmp(p,s0),R_vs_S0=cmp(T.value(raw(targets['R'])),s0),
            C92_vs_S92=cmp(T.value(raw(targets['C92'])),T.value(raw(targets['S92']))))
        for name,row in rows.items():print(variant,name,row['parent'],[t.get('vs_parent') for t in row['terms']],row['inferred_sup'],flush=True)
    report['seconds']=time.monotonic()-start
    (HERE/'iteration28-probe.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')


if __name__=='__main__':main()
