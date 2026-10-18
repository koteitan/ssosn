"""Token-law cut candidates and their suffix-order certificates.

The candidates come from syntax. The checking side uses freshly built suffix
ranks/parents for each individual sequence; no ordinal values are imported.
"""
import collections
import gzip
import json
from pathlib import Path
import harness
import token_laws as L
import token_movable as M
import token_base2 as B
from cut_structure import CutTree

HERE=Path(__file__).resolve().parent

def core_prediction(tokens):
    s=L.seq(tokens);length=len(s);last=tokens[-1]
    starts=[];position=5
    for t in tokens:
        starts.append(position)
        position+=len(L.W if t=='W' else L.A(int(t[1:]))+((1,) if t[0]=='E' else ()))
    if last=='A0':return 'A0',length-1,[length-1,length-2],2
    if last.startswith('E'):
        k=int(last[1:]);return 'E',length-2,[length-2,length-4 if k>1 else length-5],2
    if last=='W':
        i=len(tokens)-2
        while i>=0 and tokens[i]=='W':i-=1
        return ('leading_W',2,[length-3,1],2) if i<0 else ('W',starts[i]+3,[length-3,starts[i]],2)
    r,t,copies=L.a_context(tokens)
    i=len(r)-1
    while i>=0 and r[i]=='W':i-=1
    p3=starts[i] if i>=0 else 1
    c=length-len(L.components(tokens)[1])
    return 'A_positive',c,[length-1,starts[-1],p3],3

def certificate(s,c,predicted_parents=None,predicted_br=None):
    tree=CutTree.build(s);trace=tree.locate();rank=tree.suffix_rank;length=len(s)
    # Each ancestor stage is certified by a nearest-smaller suffix comparison.
    stages=[]
    for depth,(p,m) in enumerate(zip(trace['parents'],trace['records']),1):
        current=length if depth==1 else trace['parents'][depth-2]
        nearest=(p==1 or rank[p]<rank[current]) and not any(rank[j]<rank[current] for j in range(p+1,current))
        eligible=[j for j in range(p,length) if s[j-1]<s[-1]]
        maximum=(m in eligible and all(rank[j+1]<=rank[m+1] for j in eligible)) or (not eligible and m==length)
        witness=next((j for j in range(p+1,m+1) if s[j-1]<=s[p-1]),None)
        plateau=depth>1 and m==trace['records'][depth-2]
        stages.append(dict(depth=depth,parent=p,argmax=m,nearest_parent=nearest,maximum=maximum,
                           plateau=plateau,witness=witness))
    okay=trace['cut']==c and all(z['nearest_parent'] and z['maximum'] for z in stages)
    if predicted_parents is not None:okay &= trace['parents']==predicted_parents
    if predicted_br is not None:okay &= trace['br']==predicted_br
    # The raw copying law follows from cut=c, not from fitted term values.
    g=s[:c];b=s[c:-1]+(s[-1]-1,)
    return dict(sequence=s,cut=c,br=trace['br'],parents=trace['parents'],records=trace['records'],
                reason=trace['reason'],stages=stages,G=g,B=b,okay=bool(okay))


def boundary_raw(ts):
    return sum(((0,2) if t=='D' else L.W if t=='W' else L.A(int(t[1:]))+((1,) if t.startswith('E') else ()) for t in ts),())

def boundary_components(ts):
    def seq(tokens):return (0,0,2,1,0,2)+boundary_raw(tokens)
    last=ts[-1]
    if last=='D':return seq(ts[:-1]),L.W,(0,1)
    if last=='W':
        i=len(ts)-2
        while ts[i] in ('W','D'):i-=1
        return seq(ts[:-1]),boundary_raw(ts[i:-1]),L.A(0)+(0,)
    if last.startswith('E'):return seq(ts[:-1]+('A'+last[1:],)),(0,2),(0,)
    k=int(last[1:])
    if k==0:return seq(ts[:-1])+(0,1,1),(1,),()
    cut=0;copies=('W','D');i=0
    while i<len(ts)-1:
        atom=ts[i];start=i+1;i=start
        while i<len(ts)-1 and ts[i] in ('W','D'):i+=1
        if atom.startswith('A') and int(atom[1:])<k and i>start:cut=i;copies=ts[start:i]
    r,t=ts[:cut],ts[cut:-1];lower=('A'+str(k-1),)
    return seq(r+t+lower),boundary_raw(copies+t+lower),(0,1)

def main():
    report=dict(phases={});allcounts=collections.Counter();failure=None
    def run(name,items):
        nonlocal failure
        rows=[];counts=collections.Counter()
        for s,kind,c,parents,br,normal in items:
            row=certificate(s,c,parents,br);row['kind']=kind
            if normal is not None:
                h,q,v=normal;g,b=row['G'],row['B']
                row['all_n_word_certificate']=g+b==h+v and v+b==q+v
                row['okay'] &= row['all_n_word_certificate']
            # Oracle is only an independent final comparison, not a candidate.
            row['oracle_agree']=harness.Seq(s,'new').cut()==c
            row['okay'] &= row['oracle_agree']
            counts[kind]+=1;counts['br_'+str(row['br'])]+=1
            if not row['okay']:
                failure=row;rows.append(row);break
            counts['agree']+=1;rows.append(row)
        report['phases'][name]=dict(counts=counts,rows=rows)
        print(name,dict(counts),'failure',failure is not None,flush=True)
        return failure is None
    core=json.loads((HERE/'token-laws-check.json').read_text())
    def cores():
        for row in core['rows']:
            ts=tuple(row['tokens']);s=L.seq(ts);kind,c,parents,br=core_prediction(ts)
            yield s,kind,c,parents,br,L.components(ts)
    if not run('core17828',cores()):pass
    elif not run('movable3146',((tuple(r['sequence']),r['kind'],len(r['sequence'])-len(r['Q']),None,None,
                                  (tuple(r['H']),tuple(r['Q']),tuple(r['V'])))
                                 for r in json.loads((HERE/'token-movable-check.json').read_text())['rows'])):pass
    else:
        # Base-(2) rows have a separate historical artifact schema; enumerate
        # standard binary bits with the existing exact syntactic family.
        import itertools,std
        def base2():
            for size in range(15):
                for bits in itertools.product((0,1),repeat=size):
                    s=(0,0,2)+B.emit(bits)
                    if not std.is_standard(s):continue
                    g,b=B.components(bits)
                    yield s,'base2',len(g),None,None,(g+b,b,())
        if run('base2',base2()):
            def movable_contexts():
                source=json.loads((HERE/'token-movable-contexts.json').read_text())
                for row in source['rows']:
                    ts=M.parse(tuple(row['sequence'])[4:]);prefix=ts[:-1];last=ts[-1]
                    if not isinstance(last,M.Head) or len(last.gaps)!=2 or last.gaps[-1]==0:continue
                    a,b=last.gaps
                    if a not in (0,1):continue
                    if not all(t=='D' for t in prefix):continue
                    j=len(prefix)
                    h=(0,0,2,1)+M.raw(prefix+(M.Head((a,b-1)),))
                    q=M.raw(((M.Head((0,j)),) if a==0 else ())+ (M.Head((0,b-1)),))
                    v=(0,1);seq=tuple(row['sequence'])
                    yield seq,'pure_D_T'+str(a),len(seq)-len(q),None,None,(h,q,v)
            run('movable_pure_D_contexts',movable_contexts())
    if failure is None:
        def boundary():
            for row in json.loads((HERE/'token-boundary-check.json').read_text())['rows']:
                ts=tuple(row['tokens']);seq=tuple(map(int,row['sequence']));normal=boundary_components(ts)
                yield seq,'boundary_'+ts[-1],len(seq)-len(normal[1]),None,None,normal
        run('boundary3064',boundary())
    report['first_counterexample']=failure
    with gzip.open(HERE/'cut-law-explanations.json.gz','wt') as stream:
        json.dump(report,stream,ensure_ascii=False,separators=(',',':'))
    summary=dict(first_counterexample=failure,phases={name:dict(counts=phase['counts'],row_count=len(phase['rows']))
                                                    for name,phase in report['phases'].items()})
    (HERE/'cut-law-explanations.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
    print('FINAL failure',failure,flush=True)

if __name__=='__main__':main()
