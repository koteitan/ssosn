"""Print real movable-one expansions in leading and relative contexts."""
import collections
import itertools
import json
from pathlib import Path
import harness
import std
import token_movable as M

HERE=Path(__file__).resolve().parent

def main():
    contexts={()}
    for size in range(1,5):contexts.update(itertools.product(('D',M.W),repeat=size))
    for prefix in ((),('D',),('D','D'),('D',M.W),('D',)*3):
        for k in range(4):
            for m in range(3):contexts.add(prefix+(M.Head((k,)),)+(M.W,)*m)
    atoms=[M.Head((a,b)) for a in range(4) for b in range(4)]
    atoms += [M.Head(g) for g in itertools.product(range(3),repeat=3)]
    rows=[];counts=collections.Counter();failures=[]
    for prefix in sorted(contexts,key=lambda p:(len(M.raw(p)),M.raw(p))):
        for atom in atoms:
            for following_w in range(3):
                ts=prefix+(atom,)+(M.W,)*following_w
                s=(0,0,2,1)+M.raw(ts)
                if not std.is_standard(s):continue
                cut=harness.Seq(s,'new').cut();g=s[:cut];b=s[cut:-1]+(s[-1]-1,)
                terms=[dict(n=n,sequence=harness.fs(s,n),tokens=M.names(M.parse(harness.fs(s,n)[4:]))) for n in range(1,6)]
                row=dict(sequence=s,tokens=M.names(ts),prefix=M.names(prefix),atom=atom.name(),following_w=following_w,G=g,B=b,terms=terms)
                # Discover a contextual normal form from two real terms;
                # the raw-word identities then certify it for every n.
                v=M.HEAD+(0,) if following_w or atom==M.W else (0,) if atom.gaps[-1]==0 else (0,1)
                t1,t2=terms[0]['sequence'],terms[1]['sequence']
                h=t1[:-len(v)]
                q=t2[len(h):-len(v)]
                normal_ok=t1[-len(v):]==v and g+b==h+v and v+b==q+v
                row['discovered_normal_form']=dict(H=h,Q=q,V=v,all_n=normal_ok,
                    H_tokens=M.names(M.parse(h[4:])),Q_tokens=M.names(M.parse(q)))
                counts['discovered_all_n' if normal_ok else 'normal_form_DIFFER']+=1
                counts['standard']+=1
                counts['multiple_one' if len(atom.gaps)>2 else 'single_one']+=1
                law=M.w_components(ts)
                if law:
                    h,q,v,kind=law
                    ok=g+b==h+v and v+b==q+v
                    row.update(kind=kind,H=h,Q=q,V=v,all_n=ok)
                    counts[kind+('_agree' if ok else '_DIFFER')]+=1
                    if not ok:failures.append(row)
                elif following_w:counts['W_law_unsupported']+=1
                rows.append(row)
    report=dict(context_count=len(contexts),counts=counts,failures=failures,rows=rows)
    (HERE/'token-movable-contexts.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print(dict(counts),'failures',len(failures),flush=True)
    for f in failures[:8]:print('DIFFER',f['tokens'],f['kind'],flush=True)

if __name__=='__main__':main()
