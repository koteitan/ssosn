"""Check evaluator values against actual token-source real terms, without rule6."""
import argparse,collections,csv,gzip,json,sys,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE),str(HERE.parent)]
import token_value as V
import harness,evalord as E
from ordinal import cmp,show

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--source',type=Path,default=HERE/'token-laws-check.json')
 ap.add_argument('--out',type=Path,default=HERE/'token-semantic-check.json')
 args=ap.parse_args()
 source=json.loads(args.source.read_text());counts=collections.Counter();fail=[];calibration=[];additional=[];unknown=[];values={};started=time.monotonic()
 for i,row in enumerate(source['rows']):
  s=tuple(map(int,row['sequence']));nvals=[]
  try:
   parent=V.value(s);values[s]=parent
   cut=harness.Seq(s,'new').cut();g,b=s[:cut],s[cut:-1]+(s[-1]-1,)
   for n in range(1,6):
    t=g+b*n;x=V.value(t);nvals.append(x);values[t]=x
   bad=[n+1 for n,x in enumerate(nvals) if cmp(x,parent)>=0]
   nonincrease=[n+1 for n in range(4) if cmp(nvals[n],nvals[n+1])>=0]
   if bad or nonincrease:fail.append(dict(sequence=row['sequence'],parent=parent,terms=nvals,not_below=bad,not_increasing=nonincrease));counts['local_order_FAIL']+=1
   else:counts['local_order_pass']+=1
   if not E.check(parent,nvals,3):
    calibration.append(row['sequence']);counts['finite_calibration_FAIL']+=1
    t=g+b*6;x=V.value(t);values[t]=x
    passed=E.check(parent,nvals+[x],3)
    additional.append(dict(sequence=row['sequence'],n=6,passed=passed,ordinal=x))
    counts['additional_calibration_pass' if passed else 'additional_calibration_FAIL']+=1
   else:counts['finite_calibration_pass']+=1
  except V.Unknown as exc:
   counts['unresolved']+=1;unknown.append(dict(sequence=row['sequence'],reason=str(exc)))
  if (i+1)%2000==0:print(i+1,dict(counts),flush=True)
 ordered=sorted(values);order=[]
 for a,b in zip(ordered,ordered[1:]):
  if cmp(values[a],values[b])>=0:order.append(dict(left=''.join(map(str,a)),right=''.join(map(str,b)),left_value=values[a],right_value=values[b]))
 with gzip.open(args.out.with_name(args.out.stem+'-values.tsv.gz'),'wt') as f:
  wr=csv.writer(f,delimiter='\t');wr.writerow(('sequence','value'))
  for s in ordered:wr.writerow((''.join(map(str,s)),show(values[s])))
 report=dict(method='actual cuts, n=1..5, extra n=6 only on calibration failure; no rule6; finite calibration is not a proof',counts=counts,local_order_failures=fail,finite_calibration_failures=calibration,additional_calibration=additional,unresolved=unknown,valued_sequences=len(values),adjacent_violations=order,seconds=time.monotonic()-started)
 args.out.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
 print('FINAL',dict(counts),'union values',len(values),'adjacent violations',len(order),flush=True)
if __name__=='__main__':main()
