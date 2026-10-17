"""Movable-one syntax experiments, checked against raw cut words for all n."""
import collections
import json
import argparse
from pathlib import Path
import harness
import std
import token_tree as T
import token_movable as M

HERE=Path(__file__).resolve().parent
ALPHABET=('A0','A1','A2','E1','W','D')

def oldraw(ts):
    return sum(((0,2) if t=='D' else T.W if t=='W' else T.A(int(t[1:]))+((1,) if t[0]=='E' else ()) for t in ts),())

def main():
    ap=argparse.ArgumentParser();ap.add_argument('N',type=int,nargs='?',default=8);args=ap.parse_args()
    front=[('D',)];counts=collections.Counter();failures=[];rows=[]
    for size in range(args.N-1):
        new=[]
        for pref in front:
            for a in ALPHABET:
                ts=pref+(a,);s=(0,0,2,1)+oldraw(ts)
                if T.parse(oldraw(ts),True)!=ts or not std.is_standard(s):continue
                new.append(ts);mt=M.parse(s[4:]);law=M.w_components(mt)
                row=dict(sequence=s,tokens=M.names(mt))
                if law is None:
                    assert mt[-1]!=M.W, ('unsupported final W',mt)
                    counts['non_W']+=1
                    continue
                h,q,v,k=law;cut=harness.Seq(s,'new').cut();g=s[:cut];b=s[cut:-1]+(s[-1]-1,)
                ok=g+b==h+v and v+b==q+v;counts[k+('_agree' if ok else '_DIFFER')]+=1
                row.update(kind=k,H=h,Q=q,V=v,G=g,B=b,all_n=ok)
                rows.append(row)
                if not ok:failures.append(row)
        front=new
        print(size+2,'std',len(new),'counts',dict(counts),'failures',len(failures),flush=True)
    report=dict(alphabet=ALPHABET,max_old_tokens=args.N,counts=counts,failures=failures,rows=rows)
    (HERE/'token-movable-check.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print('FINAL',dict(counts),'failures',len(failures),flush=True)
    for f in failures[:8]:print('DIFFER',f['tokens'],f['kind'],f['G'],f['B'],flush=True)

if __name__=='__main__':main()
