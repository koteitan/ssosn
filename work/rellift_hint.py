"""Check the peer's predictions without inserting them into any memo."""
import argparse,json,pickle,signal,sys
from pathlib import Path
from functools import lru_cache
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE),str(HERE.parent)]
import harness,rule6,lift,std
from ordinal import ONE,OMEGA,P,add,nat,w,cmp
from order_region import pretty
class Timeout(Exception):pass
def alarm(*_):raise Timeout

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--state',type=Path,required=True)
 ap.add_argument('--reference',type=Path,required=True)
 ap.add_argument('--out',type=Path,default=HERE/'rellift-hint.json')
 args=ap.parse_args()
 with args.state.open('rb') as f:s=pickle.load(f)
 with args.reference.open('rb') as f:ref=pickle.load(f)
 assert s['signature'][0]=='rellift-no-II-v2' and ref['signature'][0]=='noregion-no-II-v1'
 rule6.memo,rule6.hmemo=s['memo'],s['hmemo']
 rule6.RELLIFT=rule6.NOREGION=rule6.EXT=rule6.MORE=rule6.USE_LIFT=True
 rule6.EXT121=rule6.EXT121E=False;rule6.MAXD=10
 rule6.lower.lower=lambda u:None
 harness.fs=lru_cache(maxsize=8000)(harness.fs)
 rule6.is_selfref=lru_cache(maxsize=16000)(rule6.is_selfref)
 rule6.conj2.T=lru_cache(maxsize=16000)(rule6.conj2.T)
 lift.unlift((2,1));signal.signal(signal.SIGALRM,alarm)
 p=tuple(map(int,'00210121012020121'));A1=(0,1,2,0,2);W=(0,1,2,1)
 a=p+W;b=tuple(map(int,'002101210120202'));J=p+A1+W
 ew=P(ONE,OMEGA)
 L=P(ONE,add(ew,w(OMEGA*2)))
 bp=P(ONE,add(ew,w(w(nat(2)))))
 family=[]
 for n in range(17):
  t=p+A1*n;prediction=P(ONE,add(ew,w(add(OMEGA,nat(n)))))
  old=ref['memo'].get(t);new=s['memo'].get(t)
  family.append(dict(n=n,sequence=''.join(map(str,t)),standard=std.is_standard(t),below_J=t<J,prediction=prediction,independent=old,current=new,status='unresolved' if new is None else 'agree' if prediction==new else 'differ'))
 terms=[]
 for name,root,bound in [('a',a,L),('b',b,bp)]:
  for n in [2,3]:
   t=harness.fs(root,n);rule6.st.update(depth=0,taint=0);x=None
   signal.setitimer(signal.ITIMER_REAL,3)
   try:x=rule6.R(t);status='clean' if x is not None and not rule6.st['taint'] else 'missing'
   except (Timeout,RecursionError):status='timeout'
   finally:signal.setitimer(signal.ITIMER_REAL,0)
   terms.append(dict(root=name,n=n,sequence=''.join(map(str,t)),standard=std.is_standard(t),status=status,ordinal=x if status=='clean' else None,below_prediction=cmp(x,bound)<0 if status=='clean' else None))
 # The two W readings are compared to a frozen, independent value.
 q=tuple(map(int,'0021012101202'));tail=(0,1,2)+W+W
 measured=ref['memo'].get(q+tail)
 expected=P(ONE,add(add(ew,w(nat(3))),w(nat(2))))
 chain=[J,harness.fs(a,2),harness.fs(a,3),a,harness.fs(b,2),harness.fs(b,3),b]
 assert all(x<y for x,y in zip(chain,chain[1:]))
 assert all(std.is_standard(x) for x in chain)
 report=dict(predictions_inserted=False,RELLIFT=True,NOREGION=True,depth=10,seconds_per_term=3,
  J=dict(sequence=''.join(map(str,J)),standard=std.is_standard(J),below_a=J<a,current=s['memo'].get(J)),
  J_real_terms_shape='J[n] = pW A1^n A0 0; prefixes imply all pW A1^n are standard',
  family=family,terms=terms,predicted_a=L,predicted_b=bp,
  joint_predictions_inconsistent_if_family_holds_for_all_n=True,
  order_chain=[dict(name=name,sequence=''.join(map(str,t))) for name,t in zip(['J','a[2]','a[3]','a','b[2]','b[3]','b'],chain)],
  trailing_W=dict(lift_standard=std.is_standard((0,0,2,1)+tail),region_standard=std.is_standard(q+tail),measured=measured,plus_one_depth1_prediction=expected,agree=expected==measured),
  explanation='If family prediction holds for all n, sup family = L <= o(J) < o(a), contradicting a=L.')
 args.out.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
 print('J standard/below a',report['J']['standard'],report['J']['below_a'])
 print('family agree/differ/unresolved',*[sum(t['status']==k for t in family) for k in ['agree','differ','unresolved']])
 print('real terms',[(t['root'],t['n'],t['status'],t['below_prediction']) for t in terms])
 print('trailing W',report['trailing_W']['agree'])
if __name__=='__main__':main()
