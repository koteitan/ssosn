"""Compare independent token semantics with stored clean references and audit order."""
import argparse,collections,csv,gc,gzip,json,pickle,sys,time
from functools import lru_cache
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE),str(HERE.parent)]
import token_value as V
import harness,std,lift,conj
from ordinal import ONE,P,add,cmp,show
fmt=lru_cache(maxsize=100000)(show)
def tu(x):return tuple(tu(y) for y in x) if isinstance(x,list) else x
def txt(s):return ''.join(map(str,s))

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--state',action='append',default=[],help='label:path')
 ap.add_argument('--json-reference',action='append',default=[],help='label:path; only status=clean ordinal fields')
 ap.add_argument('--out',type=Path,default=HERE/'token-comparison.json')
 ap.add_argument('--superset',action='store_true',help='audit all valued auxiliary sequences without claiming all are standard')
 args=ap.parse_args();started=time.monotonic();stats={};allseq=set();values={};knownstandard=set();audit11=set();references11=set()
 old=HERE/'order-region-all-values.tsv.gz'
 if old.exists():
  with gzip.open(old,'rt') as f:
   for row in csv.DictReader(f,delimiter='\t'):
    s=tuple(map(int,row['sequence']));audit11.add(s);knownstandard.add(s)
 syntax=json.loads((HERE/'token-laws-check.json').read_text())
 knownstandard.update(tuple(map(int,r['sequence'])) for r in syntax['rows'])
 resultfile=args.out.with_suffix('.tsv.gz')
 f=gzip.open(resultfile,'wt');writer=csv.writer(f,delimiter='\t')
 writer.writerow(('source','sequence','status','token_value','reference','reason'))
 def compare(label,s,reference,hook=False):
  s=tuple(s);allseq.add(s)
  if label.startswith('audit11'):references11.add(s)
  c=stats.setdefault(label,collections.Counter());c['total']+=1
  try:
   value=V.block_value(s[2:]) if hook else V.value(s)
   result='agree' if value==reference else 'differ';values[s]=value;reason=''
  except (V.Unknown,RecursionError) as exc:
   value=None;result='unresolved';reason=str(exc)[:200]
  c[result]+=1
  writer.writerow((label,txt(s),result,fmt(value) if result=='differ' else '',fmt(reference) if result!='agree' else '',reason))
  if c['total']%50000==0:print(label,c['total'],dict(c),'seconds',round(time.monotonic()-started),flush=True)
 # Algebraic lift reference; it is never inserted into V's caches.
 lift.unlift((2,1))
 for u,y in lift._INV.items():compare('lift',(0,0)+u,P(ONE,add(V.E0,conj.v(y))))
 print('lift',dict(stats['lift']),flush=True)
 for spec in args.state:
  label,path=spec.split(':',1)
  with open(path,'rb') as fd:state=pickle.load(fd)
  for key in list(state):
   if key not in ('memo','hmemo'):del state[key]
  gc.collect()
  for s,x in state['memo'].items():
   if x is not None:compare(label+':R',s,x)
  for u,x in state['hmemo'].items():
   if x is not None:compare(label+':hook',(0,0)+u,x,True)
  del state;gc.collect();print('DONE',label,flush=True)
 for spec in args.json_reference:
  label,path=spec.split(':',1);data=json.loads(Path(path).read_text())
  def walk(node,sequence=None):
   if isinstance(node,dict):
    sequence=node.get('sequence',sequence)
    if sequence and node.get('status')=='clean' and node.get('ordinal') is not None:
     compare(label,tuple(map(int,sequence)),tu(node['ordinal']))
    for k,v in node.items():
     if k not in ('ordinal','sequence'):walk(v,sequence)
   elif isinstance(node,list):
    for v in node:walk(v,sequence)
  walk(data);print('DONE',label,dict(stats.get(label,{})),flush=True)
 f.close()
 # Greedy descending membership, reusing only earlier verified sequence identities.
 top=std.TOP;standard=set();steps=0
 if args.superset:standard.update(allseq)
 for number,s in enumerate([] if args.superset else sorted(allseq,reverse=True)):
  if s in knownstandard:standard.add(s);top=s;continue
  for _ in range(100000):
   if s==top:standard.add(s);break
   if top<s:raise AssertionError(('membership order',s,top))
   if top[-1]==0:
    new=top[:-1]
    if new<s:break
   else:
    cut=harness.Seq(top,'new').cut();g,b=top[:cut],top[cut:-1]+(top[-1]-1,)
    if std.above_all_terms(g,b,s):break
    lo,hi=1,len(s)//len(b)+2
    while lo<hi:
     mid=(lo+hi)//2
     if g+b*mid>=s:hi=mid
     else:lo=mid+1
    new=g+b*lo
   top=new;steps+=1
  else:raise RuntimeError('membership cap')
  if number%50000==0:print('membership',number,'standard',len(standard),'steps',steps,flush=True)
 standard_stats={};standard_differ=[];standard_differ_count=0
 with gzip.open(resultfile,'rt') as fd:
  for row in csv.DictReader(fd,delimiter='\t'):
   if tuple(map(int,row['sequence'])) not in (knownstandard if args.superset else standard):continue
   c=standard_stats.setdefault(row['source'],collections.Counter());c[row['status']]+=1;c['total']+=1
   if row['status']=='differ':
    standard_differ_count+=1
    if len(standard_differ)<20:standard_differ.append(row)
 ordered=sorted(s for s in standard if s in values);bad=[]
 for a,b in zip(ordered,ordered[1:]):
  if cmp(values[a],values[b])>=0:bad.append(dict(left=txt(a),right=txt(b),left_value=values[a],right_value=values[b]))
 with gzip.open(args.out.with_name(args.out.stem+'-values.tsv.gz'),'wt') as fd:
  wr=csv.writer(fd,delimiter='\t');wr.writerow(('sequence','value'))
  for s in ordered:wr.writerow((txt(s),fmt(values[s])))
 verified=allseq&knownstandard
 report=dict(independent_evaluator='token_value; no rule6/lower/sequence recursion',all_reference_counts=stats,standard_reference_counts=standard_stats,standard_differ_count=standard_differ_count,standard_differ_examples=standard_differ,all_comparisons_file=resultfile.name,
             all_sequences=len(allseq),standard_membership_filtered=not args.superset,verified_standard_sequences=len(verified),standard_sequences=None if args.superset else len(standard),nonstandard_sequences=None if args.superset else len(allseq)-len(standard),audited_valued_sequences=len(ordered),valued_standard_sequences=sum(s in values for s in verified) if args.superset else len(ordered),unresolved_standard_sequences=sum(s not in values for s in verified) if args.superset else len(standard)-len(ordered),membership_steps=steps,adjacent_violations=bad,
             audit11_sequences=len(audit11),audit11_reference_covered=len(audit11&references11),audit11_evaluator_resolved=sum(s in values for s in audit11),seconds=time.monotonic()-started)
 args.out.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
 print('FINAL',len(allseq),'audited superset' if args.superset else 'standard',len(standard),'valued',len(ordered),'order violations',len(bad),'seconds',round(report['seconds']),flush=True)
if __name__=='__main__':main()
