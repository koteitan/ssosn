"""Compare token expansion laws with the actual sequence cut, up to N tokens."""
import argparse,collections,json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path[:0]=[str(HERE),str(HERE.parent)]
import harness,std
from token_laws import TOK,HI,seq,expected,a_context
from token_value import parse_tail,Unknown

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('N',type=int)
 ap.add_argument('--out',type=Path,default=HERE/'token-laws-check.json')
 ap.add_argument('--max-a',type=int,default=2)
 ap.add_argument('--max-e',type=int,default=1)
 args=ap.parse_args();frontier=[()];counts=collections.Counter();bad=[];coverage=collections.Counter();examples={};rows=[]
 alphabet=tuple('A'+str(k) for k in range(args.max_a+1))+tuple('E'+str(k) for k in range(1,args.max_e+1))+('W',)
 for depth in range(args.N):
  new=[]
  for tokens in frontier:
   for atom in alphabet:
    ts=tokens+(atom,);s=seq(ts)
    if s>=HI or not std.is_standard(s):continue
    new.append(ts);tag='L_E' if atom.startswith('E') else 'L_W' if atom=='W' else 'A0' if atom=='A0' else 'L_A'
    ok=True
    cut=harness.Seq(s,'new').cut()
    good,badpart=s[:cut],s[cut:-1]+(s[-1]-1,)
    for n in [1,2,3,4,5]:
     actual=good+badpart*n;pred=expected(ts,n)
     if pred is not None and actual!=pred:
      ok=False;bad.append(dict(tokens=ts,n=n,actual=actual,expected=pred))
     # Full token alphabet needs arbitrary A_k and numeric terminal 0 / 01.
     terminal=(0,1) if tag=='L_A' else (0,)
     body=actual[4:]
     if tag=='A0':coverage['A0-expansion-other']+=1;examples.setdefault('A0-expansion-other',actual)
     elif body[-len(terminal):]==terminal:
      body=body[:-len(terminal)]
      try:
       parsed=parse_tail(body)
       outside=[t for t in parsed if t not in TOK]
       key='higher_A' if outside else 'original_tokens_with_terminal'
       coverage[key]+=1;examples.setdefault(key,actual)
      except Unknown:
       coverage['unparsed']+=1;examples.setdefault('unparsed',actual)
     else:coverage['unexpected_terminal']+=1;examples.setdefault('unexpected_terminal',actual)
    counts['A0_not_in_three_laws' if tag=='A0' else tag+('_holds' if ok else '_FAILS')]+=1
    rows.append(dict(sequence=''.join(map(str,s)),tokens=ts,law=tag))
  frontier=new
  print(depth+1,'standard',len(frontier),'cumulative',sum(counts.values()),dict(counts),flush=True)
 report=dict(N=args.N,alphabet=alphabet,NS=[1,2,3,4,5],counts=counts,failures=bad,coverage=coverage,coverage_examples=examples,rows=rows)
 args.out.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
if __name__=='__main__':main()
