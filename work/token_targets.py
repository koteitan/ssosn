"""Evaluate named roots and their actual terms with the independent token evaluator."""
import json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE),str(HERE.parent)]
import token_value as V,harness,std,evalord as E
from ordinal import ONE,ZERO,OMEGA,P,add,nat,w,cmp

def pretty(x):
 if not x:return '0'
 groups=[]
 for t in x:
  if groups and groups[-1][0]==t:groups[-1][1]+=1
  else:groups.append([t,1])
 out=[]
 for (_,a,b),n in groups:
  t='1' if not a and not b else 'ω' if not a and b==ONE else 'ω^('+pretty(b)+')' if not a else 'e_('+pretty(b)+')' if a==ONE else 'φ_('+pretty(a)+')('+pretty(b)+')'
  out.append(str(n) if t=='1' else t+('·'+str(n) if n>1 else ''))
 return '+'.join(out)

def probe(s):
 try:x=V.value(s);return dict(status='value',ordinal=x,rendered=pretty(x))
 except V.Unknown as exc:return dict(status='unresolved',ordinal=None,reason=str(exc))

def main():
 cases=[('J','00210121012020121012020121'),('a','002101210120201210121'),('b','002101210120202'),('b A0','002101210120202012'),('region A3','00210121012020202'),('S','002101210120210121012021'),('WW','002101210121'),('WWW','0021012101210121'),('002102','002102'),('0021021','0021021'),('00211','00211'),('0022','0022'),('003','003')]
 result=[]
 for name,text in cases:
  s=tuple(map(int,text));root=probe(s);terms=[]
  for n in range(1,6):
   t=harness.fs(s,n);terms.append(dict(n=n,sequence=''.join(map(str,t)),**probe(t)))
  xs=[t['ordinal'] for t in terms]
  root.update(name=name,sequence=text,standard=std.is_standard(s),terms=terms)
  if root['ordinal'] is not None and all(x is not None for x in xs):
   root['all_terms_below']=all(cmp(x,root['ordinal'])<0 for x in xs)
   root['finite_calibration']=E.check(root['ordinal'],xs,3)
  result.append(root);print(name,root.get('rendered',root.get('reason')),flush=True)
 (HERE/'token-targets.json').write_text(json.dumps(dict(method='token laws, closed ordinal operations, no sequence recursion or old values',cases=result),ensure_ascii=False,indent=2)+'\n')
 for row in result[:3]:
  print(row['name'],'terms',[(t['n'],t.get('rendered',t.get('reason'))) for t in row['terms']],flush=True)
if __name__=='__main__':main()
