"""Record bounded root/term probes and the missing blocks, with II disabled."""
import argparse,json,pickle,signal,sys
from collections import Counter
from functools import lru_cache
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE),str(HERE.parent)]
import harness,rule6,lift
from order_region import pretty
class Timeout(Exception):pass
def alarm(*_):raise Timeout

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--state',type=Path,required=True)
 ap.add_argument('--out',type=Path,required=True)
 ap.add_argument('--seconds',type=float,default=1)
 ap.add_argument('--depth',type=int,default=12)
 args=ap.parse_args()
 with args.state.open('rb') as f:state=pickle.load(f)
 assert state['signature'][0]=='rellift-no-II-v2'
 rule6.memo,rule6.hmemo=state['memo'],state['hmemo']
 rule6.NOREGION=rule6.RELLIFT=rule6.EXT=rule6.MORE=rule6.USE_LIFT=True
 rule6.EXT121=False;rule6.EXT121E=state['signature'][-1];rule6.MAXD=args.depth
 lift.unlift((2,1))
 harness.fs=lru_cache(maxsize=8000)(harness.fs)
 rule6.is_selfref=lru_cache(maxsize=16000)(rule6.is_selfref)
 rule6.level=lru_cache(maxsize=16000)(rule6.level)
 rule6.conj2.T=lru_cache(maxsize=16000)(rule6.conj2.T)
 missing=Counter()
 def lower_disabled(u):missing[tuple(u)]+=1;return None
 rule6.lower.lower=lower_disabled
 signal.signal(signal.SIGALRM,alarm)
 targets=['002101210120201210121','002101210120202','002101210120210121012021','002101210121','002102']
 records=[]
 for text in targets:
  s=tuple(map(int,text));rows=[]
  for n,t in [(i,harness.fs(s,i)) for i in range(1,6)]+[(None,s)]:
   missing.clear();rule6.st.update(depth=0,taint=0);x=None
   signal.setitimer(signal.ITIMER_REAL,args.seconds)
   try:
    x=rule6.R(t);status='clean' if x is not None and not rule6.st['taint'] else 'missing'
   except (Timeout,RecursionError):status='timeout'
   finally:signal.setitimer(signal.ITIMER_REAL,0)
   rows.append(dict(n=n,sequence=''.join(map(str,t)),status=status,ordinal=x if status=='clean' else None,rendered=pretty(x) if status=='clean' else None,missing_blocks=[dict(sequence='00'+''.join(map(str,u)),hits=count) for u,count in missing.most_common(12)]))
  records.append(dict(sequence=text,probes=rows))
  print(text,rows[-1]['status'],rows[-1]['rendered'],flush=True)
 args.out.write_text(json.dumps(dict(depth=args.depth,seconds_per_probe=args.seconds,EXT121E=rule6.EXT121E,RELLIFT=True,NOREGION=True,targets=records),ensure_ascii=False,indent=2)+'\n')

if __name__=='__main__':main()
