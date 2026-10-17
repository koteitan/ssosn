"""Test revised SSOS predictions, using them only for comparison."""
import argparse,json,pickle,signal,sys,time
from functools import lru_cache
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE),str(HERE.parent)]
import harness,lift,rule6,std
from ordinal import ONE,OMEGA,P,add,nat,w,succ,cmp
from order_region import pretty
class Timeout(Exception):pass
def alarm(*_):raise Timeout

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--state',type=Path,required=True)
 ap.add_argument('--out',type=Path,default=HERE/'revised-predictions.json')
 ap.add_argument('--seconds',type=float,default=10)
 args=ap.parse_args()
 with args.state.open('rb') as f:state=pickle.load(f)
 assert state['signature'][0]=='rellift-no-II-v2'
 rule6.memo,rule6.hmemo=state['memo'],state['hmemo']
 rule6.RELLIFT=rule6.NOREGION=rule6.EXT=rule6.MORE=rule6.USE_LIFT=True
 rule6.EXT121=rule6.EXT121E=False;rule6.MAXD=10
 rule6.lower.lower=lambda u:None
 lift.unlift((2,1))
 harness.fs=lru_cache(maxsize=8000)(harness.fs)
 rule6.is_selfref=lru_cache(maxsize=16000)(rule6.is_selfref)
 rule6.level=lru_cache(maxsize=16000)(rule6.level)
 rule6.conj2.T=lru_cache(maxsize=16000)(rule6.conj2.T)
 signal.signal(signal.SIGALRM,alarm)
 p=tuple(map(int,'00210121012020121'));a=p+(0,1,2,1);b=tuple(map(int,'002101210120202'))
 A1=(0,1,2,0,2);A0=(0,1,2);W=(0,1,2,1);J=p+A1+W;ew=P(ONE,OMEGA)
 jpred=P(ONE,add(ew,w(OMEGA*2)))
 apred=P(ONE,add(ew,w(w(nat(2)))))
 bindex=add(ew,w(w(nat(3))));bpred=P(ONE,bindex)
 # The two A0 predictions are intentionally distinct; neither is memoized.
 bA0index=P(ONE,succ(bindex));bA0outer=succ(bpred)
 cases=[('J',J,jpred,None),('P A1^2',p+A1*2,P(ONE,add(ew,w(add(OMEGA,nat(2))))),None),
        ('a[2]',harness.fs(a,2),None,apred),('a[3]',harness.fs(a,3),None,apred),
        ('b[1]',harness.fs(b,1),None,bpred),('b[2]',harness.fs(b,2),None,bpred),
        ('b[3]',harness.fs(b,3),None,bpred),('b A0',b+A0,bA0index,None)]
 report=dict(predictions_inserted=False,NOREGION=True,RELLIFT=True,EXT121E=False,depth=10,
             seconds_per_case=args.seconds,predicted_J=jpred,predicted_a=apred,predicted_b=bpred,
             bA0_index_successor=bA0index,bA0_outer_successor=bA0outer,cases=[])
 for name,s,pred,bound in cases:
  rule6.st.update(depth=0,taint=0);x=None;cached=s in rule6.memo;started=time.monotonic()
  signal.setitimer(signal.ITIMER_REAL,args.seconds)
  try:
   x=rule6.R(s);status='clean' if x is not None and not rule6.st['taint'] else 'missing'
  except (Timeout,RecursionError):status='timeout'
  finally:signal.setitimer(signal.ITIMER_REAL,0)
  actual=x if status=='clean' else None
  row=dict(name=name,sequence=''.join(map(str,s)),standard=std.is_standard(s),cached_at_start=cached,
           status=status,ordinal=actual,rendered=pretty(actual) if actual is not None else None,
           prediction=pred,agree=(actual==pred) if actual is not None and pred is not None else None,
           below_parent_prediction=cmp(actual,bound)<0 if actual is not None and bound is not None else None,
           seconds=time.monotonic()-started)
  report['cases'].append(row)
  args.out.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
  print(name,status,row['rendered'],'agree',row['agree'],'below parent',row['below_parent_prediction'],flush=True)
 # A successor after the whole sequence is an immediate predecessor of b A0.
 report['A0_order']={'b_successor_sequence':''.join(map(str,b+(0,))),
                     'b_A0_sequence':''.join(map(str,b+A0)),
                     'both_standard':std.is_standard(b+(0,)) and std.is_standard(b+A0),
                     'b_successor_below_b_A0':b+(0,)<b+A0,
                     'b_A0_is_limit_sequence':(b+A0)[-1]>0}
 report['generalized_J_family']=[]
 for n in range(5):
  s=p+(A1+W)*n;actual=state['memo'].get(s)
  pred=P(ONE,add(ew,w(OMEGA*(n+1))))
  report['generalized_J_family'].append(dict(n=n,sequence=''.join(map(str,s)),standard=std.is_standard(s),prediction=pred,ordinal=actual,status='unresolved' if actual is None else 'agree' if actual==pred else 'differ'))
 args.out.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')

if __name__=='__main__':main()
