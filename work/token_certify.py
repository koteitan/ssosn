"""Certify each finite-source token law for every n>=1 by a word equation.

If G D = H V and V D = Q V, then G D^n = H Q^(n-1) V by induction.
The proposed H,Q,V are computed without the actual cut.
"""
import argparse,collections,json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE),str(HERE.parent)]
import harness
from token_laws import components

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--source',type=Path,default=HERE/'token-laws-check.json')
 ap.add_argument('--out',type=Path,default=HERE/'token-law-certificates.json')
 args=ap.parse_args();source=json.loads(args.source.read_text());counts=collections.Counter();bad=[]
 for row in source['rows']:
  ts=tuple(row['tokens']);s=tuple(map(int,row['sequence']));parts=components(ts)
  if parts is None:counts['A0_outside_three_laws']+=1;continue
  h,q,v=parts;cut=harness.Seq(s,'new').cut();g=s[:cut];d=s[cut:-1]+(s[-1]-1,)
  base=(g+d==h+v);rotation=(v+d==q+v)
  if base and rotation:counts[row['law']+'_all_n_certified']+=1
  else:bad.append(dict(sequence=row['sequence'],tokens=ts,base=base,rotation=rotation))
 report=dict(source_token_bound=source['N'],alphabet=source.get('alphabet'),counts=counts,failures=bad,meaning='Every n>=1 for every source in the stated finite corpus; not every unbounded token string',proof='G D=H V and V D=Q V imply G D^n=H Q^(n-1) V by induction')
 args.out.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n');print(counts,'FAIL',len(bad),flush=True)
if __name__=='__main__':main()
