"""Check the finite real-term closure for shapes beyond the five-token alphabet."""
import collections,json,sys,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE),str(HERE.parent)]
import harness,conj2,token_value as V
from token_laws import TOK,HI

def main():
 started=time.monotonic();closure=harness.closure([HI],nmax=3,maxlen=24)
 low=(0,0,2,1);counts=collections.Counter();examples={};unknown=[];blocks=set()
 def scan(body):
  for u in conj2.units(body):
   if u in ((0,),(2,)):continue
   t=conj2.T(u)
   if t==u:blocks.add(u)
   else:scan(t)
 for s in sorted(closure):
  if not low<=s<HI:continue
  counts['range_sequences']+=1;scan(s[2:])
  try:
   ts=V.parse_tail(s[4:]);tag='five_token_alphabet' if all(t in TOK for t in ts) else 'higher_A'
  except V.Unknown:tag='structural_wrapper_needed'
  counts[tag]+=1;examples.setdefault(tag,''.join(map(str,s)))
  try:V.value(s);counts['evaluator_resolved']+=1
  except V.Unknown as e:unknown.append(dict(sequence=''.join(map(str,s)),reason=str(e)))
 for u in blocks:
  try:
   if u[:2]!=(2,1):raise V.Unknown('other self-reference base')
   V.parse_tail(u[2:]);counts['selfref_token_parsed']+=1
  except V.Unknown:counts['selfref_not_token_parsed']+=1
 report=dict(maxlen=24,nmax=3,closure_sequences=len(closure),counts=counts,examples=examples,unresolved=unknown,seconds=time.monotonic()-started,
             alphabet_not_complete_witnesses=['002101','0021012020202'],explanation='A0 expansions need structural omega-power wrappers; E1[4] produces A4, outside A0,A1,A2.')
 (HERE/'token-coverage.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
 print(report['closure_sequences'],dict(counts),'unknown',len(unknown),'seconds',report['seconds'],flush=True)
if __name__=='__main__':main()
