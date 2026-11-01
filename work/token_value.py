"""Experimental token semantics: finite depth increments and omega iteration.

No rule6, lower, or sequence recursion is imported. W is grouped with its unit.
"""
import sys
from pathlib import Path
sys.path[:0]=[str(Path(__file__).resolve().parent),str(Path(__file__).resolve().parent.parent)]
from functools import lru_cache
from ordinal import ZERO,ONE,OMEGA,P,add,nat,w,succ,cmp
from evalord import next_fp

def A(k):return (0,1,2)+(0,2)*k
W=A(0)+(1,)
E0=P(ONE,ZERO)
BOUNDARY_EXPERIMENT=False  # rejected broad fold; diagnostic runs only, fresh caches
P1_ROOT_EXPERIMENT=False  # §43: D/W roots above P, measured separately
P1_V_FOLD_EXPERIMENT=False  # §43: internal V rank, on top of P1_ROOT
P1_V_BITS_EXPERIMENT=False  # §43: V copy rank via 0/1/2 bits (v_bits43); implies the V fold
P1_V_RAW_EXPERIMENT=False   # §43: rank from old value of 00+bits; partial diagnostic
P2_V7_EXPERIMENT=False      # §44: root-V blocks use the v7 rank and B(r); default off

class Unknown(Exception):pass

def leading_w_index(exponent):
 """Built-in induction formula, checked against real terms, not a fold output.

 For j>=1: index(W^j)=epsilon_(omega^j); continuous at exponent=omega.
 """
 return P(ONE,w(exponent))

def parse_tail(tail):
 tail=tuple(tail);out=[];i=0
 while i<len(tail):
  if tail[i:i+3]!=(0,1,2):raise Unknown(('non-token suffix',tail[i:]))
  j=i+3;k=0
  while tail[j:j+2]==(0,2):j+=2;k+=1
  if tail[j:j+1]==(1,):out.append('W' if k==0 else 'E'+str(k));j+=1
  else:out.append('A'+str(k))
  i=j
 return tuple(out)

def bump_last(index,depth,amount):
 if depth==0:return add(index,amount)
 if not index:raise Unknown('empty exponent')
 t=index[-1]
 exponent=t[2] if t[1]==ZERO else (t,)
 if not exponent:
  # A newly opened term may not yet have a tower at the requested depth.
  # Promote its finite coefficient, rather than inheriting an older term's
  # exponent. This is the fresh-term branch in the corrected L_A.
  n=0
  while n<len(index) and index[-1-n]==ONE[0]:n+=1
  seed=add(nat(n),amount)
  for _ in range(depth):seed=w(seed)
  return add(index[:-n],seed)
 changed=bump_last(exponent,depth-1,amount)
 return add(index[:-1],w(changed))

def epsilon_iteration(value,depth,m):
 """Iterate the next-epsilon operation at the active, rather than root, depth."""
 if depth:
  t=value[-1]
  exponent=t[2] if t[1]==ZERO else (t,)
  if not exponent:raise Unknown('epsilon depth exceeds active tower')
  return add(value[:-1],w(epsilon_iteration(exponent,depth-1,m)))
 t=value[-1];eps=next_fp(ONE,(t,));q=eps[0][2]
 if m:q=add(q,w(nat(m)))
 return add(value[:-1],P(ONE,q))

@lru_cache(maxsize=200000)
def index(tokens):
 tokens=tuple(tokens);j=0
 while j<len(tokens) and tokens[j]=='W':j+=1
 base=E0 if j==0 else leading_w_index(nat(j))
 value=base;fresh=True;i=j;active_depth=0
 while i<len(tokens):
  token=tokens[i]
  if token=='W':raise Unknown('unattached W')
  i+=1;m=0
  while i<len(tokens) and tokens[i]=='W':m+=1;i+=1
  amount=w(nat(m))
  k=int(token[1:])
  if token[0]=='A':
   if k==0:value=add(value,amount)
   elif fresh:
    seed=nat(j+2) if m==0 else amount
    for _ in range(k):seed=w(seed)
    value=add(base,seed)
   else:value=bump_last(value,k,amount)
   active_depth=k
  elif token=='E1':
   if fresh:value=add(base,P(ONE,ZERO if m==0 else amount))
   else:value=epsilon_iteration(value,active_depth,m)
  else:raise Unknown(('unimplemented token',token))
  fresh=False
 return value

@lru_cache(maxsize=200000)
def block_value(u):
 u=tuple(u)
 if P2_V7_EXPERIMENT and u[:5]==(2,1,0,2,1):
  try:
   import v_bits44
   copies=parse_p2_v7_copies(u[2:])
   return v_bits44.B7(copies)
  except (Unknown, v_bits44.Unknown) as error:
   # A_k/E tails need the same v7-seeded A_k fold as the general tree path.
   try:
    import token_tree
    token_tree.GENERAL_COPY_EXPERIMENT=True
    token_tree.V_ROOT_EXPERIMENT=True
    token_tree.V_BITS_EXPERIMENT=P1_V_BITS_EXPERIMENT
    token_tree.V_RAW_EXPERIMENT=P1_V_RAW_EXPERIMENT
    previous_p2_mode=token_tree.P2_V7_EXPERIMENT
    token_tree.P2_V7_EXPERIMENT=True
    try:
     return token_tree.block_value(u)
    finally:
     token_tree.P2_V7_EXPERIMENT=previous_p2_mode
   except token_tree.Unknown:
    pass
 if P1_ROOT_EXPERIMENT and u==(2,1,0,2,0,2,1):
  return p1_v_anchor()
 if P1_ROOT_EXPERIMENT and (P1_V_FOLD_EXPERIMENT or P1_V_BITS_EXPERIMENT or P1_V_RAW_EXPERIMENT) and u[:7]==(2,1,0,2,0,2,1):
  import token_tree
  token_tree.GENERAL_COPY_EXPERIMENT=True
  token_tree.V_ROOT_EXPERIMENT=True
  token_tree.V_BITS_EXPERIMENT=P1_V_BITS_EXPERIMENT
  token_tree.V_RAW_EXPERIMENT=P1_V_RAW_EXPERIMENT
  try:return token_tree.block_value(u)
  except token_tree.Unknown:pass
 import token_base2
 binary=token_base2.parse(u)
 if binary is not None:return P(ONE,token_base2.index(binary))
 boundary=(2,1,0,2)
 if BOUNDARY_EXPERIMENT and u[:len(boundary)]==boundary and u!=boundary:
  import token_boundary
  try:return token_boundary.block_value(u)
  except Unknown:pass
 if u==boundary+A(1):
  # Exact L_A copies W D A0; increments omega^omega*(n-1)+1
  # have supremum omega^(omega+1).
  alpha=block_value(boundary)[0][2]
  return P(ONE,add(alpha,w(succ(OMEGA))))
 # Relative tails: A0 W^m adds omega^m to the epsilon
 # index, by m successive omega-iterations of the A0 successor unit.
 # The preceding base must already have an independently known value.
 base=u;amounts=[]
 while True:
  # A0 W D has real terms A0 W^n (0,1): their index increments
  # omega^n are cofinal in omega^omega. This is a rank limit,
  # distinct from treating another W as addition of omega.
  if base[-9:]==A(0)+W+(0,2):
   base=base[:-9];amounts.append(w(OMEGA));continue
  rest=base;m=0
  while rest[-4:]==W:rest=rest[:-4];m+=1
  if rest[-3:]!=A(0):break
  base=rest[:-3];amounts.append(w(nat(m)))
 if amounts:
  import conj2
  if conj2.units(base)==[base] and conj2.T(base)==base:
   x=block_value(base)
   if len(x)==1 and x[0][1]==ONE:
    i=x[0][2]
    for amount in reversed(amounts):i=add(i,amount)
    return P(ONE,i)
 if u[:2]!=(2,1):raise Unknown(('unrecognized self-reference',u))
 if u==(2,1,0,2):
  # Real terms are W^j followed by (0,1); their outer omega powers
  # are cofinal in epsilon_(sup_j index(W^j)). No sequence recursion.
  return P(ONE,leading_w_index(OMEGA))
 return P(ONE,index(parse_tail(u[2:])))


@lru_cache(maxsize=10000)
def parse_p2_v7_copies(raw):
 """Unique W/D/V parse following the (2,1) prefix of a P1-root block."""
 raw=tuple(raw)
 pieces={'W':W,'D':(0,2),'V':(0,2,1)}
 @lru_cache(None)
 def go(i):
  if i==len(raw):return ((),)
  out=[]
  for token,unit in pieces.items():
   if raw[i:i+len(unit)]==unit:
    out.extend((token,)+tail for tail in go(i+len(unit)))
  return tuple(dict.fromkeys(out))
 forms=go(0)
 if len(forms)!=1:
  raise Unknown(('P2 V7 token parse is not unique',raw,forms[:5]))
 return forms[0]

@lru_cache(maxsize=200000)
def body_value(body):
 # The structural 0/1/2 block decomposition; no numeric override table.
 import conj2
 value=ZERO
 for unit in conj2.units(body):
  if unit==(0,):x=ONE
  elif unit==(2,):x=E0
  else:
   t=conj2.T(unit)
   x=block_value(unit) if t==unit else w(add(ONE,body_value(t)))
  value=add(value,x)
 return value

@lru_cache(maxsize=200000)
def value(s):
 s=tuple(s)
 if s[:2]!=(0,0) or max(s,default=0)>2:raise Unknown('outside 0/1/2 range')
 if len(s)>2 and s[-1]==0:return succ(value(s[:-1]))
 try:return add(nat(2),body_value(s[2:]))
 except Unknown:
  if not (P1_ROOT_EXPERIMENT or P2_V7_EXPERIMENT):raise
  return p1_root_candidate(s)


def p1_root_candidate(s):
 """Flagged D/W root extension; no assertion of a general value theorem.

 The D/W anchors are the earlier §34 general-copy candidates.  The V anchor
 is the stable finite-sample sup of the actual law P V[n] = P D^n 0.  The
 L1 anchor is the sup of the cut=2 block repetitions of P D 0 0.
 Other D-led strings are delegated to the same general-copy fold; failures
 remain Unknown rather than acquiring an invented value.
 """
 import token_tree
 root=(0,0,2,1,0,2)
 if s[:len(root)]!=root:raise Unknown('outside P root experiment')
 p1=root+(1,)
 p2=p1+(1,)
 if s>=p2:raise Unknown('at or above P2: outside root experiments')
 if s>=p1 and not P2_V7_EXPERIMENT:
  raise Unknown('at or above P1: outside P root experiment')
 token_tree.GENERAL_COPY_EXPERIMENT=True
 token_tree.V_ROOT_EXPERIMENT=P1_V_FOLD_EXPERIMENT or P1_V_BITS_EXPERIMENT or P1_V_RAW_EXPERIMENT
 token_tree.V_BITS_EXPERIMENT=P1_V_BITS_EXPERIMENT
 token_tree.V_RAW_EXPERIMENT=P1_V_RAW_EXPERIMENT
 previous_p2_mode=token_tree.P2_V7_EXPERIMENT
 token_tree.P2_V7_EXPERIMENT=P2_V7_EXPERIMENT
 if s==root+(0,2,1):
  token_tree.P2_V7_EXPERIMENT=previous_p2_mode
  if P2_V7_EXPERIMENT:
   import v_bits44
   return v_bits44.B7(('V',))
  return p1_v_anchor()
 if s==root+(0,2,0,1):
  token_tree.P2_V7_EXPERIMENT=previous_p2_mode
  return w(succ(value(root+(0,2))))
 if s==root+(0,2,1,0,1):
  token_tree.P2_V7_EXPERIMENT=previous_p2_mode
  return w(succ(value(root+(0,2,1))))
 try:
  return token_tree.value(s)
 except token_tree.Unknown as error:
  raise Unknown(('P root fold unknown',error.args)) from error
 finally:
  token_tree.P2_V7_EXPERIMENT=previous_p2_mode


@lru_cache(maxsize=1)
def p1_v_anchor():
 """The candidate sup of P V[n]=P D^n 0, checked at 3 and 4 terms."""
 import token_tree
 import evalord
 from ordinal import lt
 token_tree.GENERAL_COPY_EXPERIMENT=True
 xs=[token_tree.value((0,0,2,1)+(0,2)*n) for n in range(1,5)]
 limit3,limit4=evalord.sup(xs[:3]),evalord.sup(xs)
 if limit3 is None or limit3!=limit4 or not all(lt(x,limit4) for x in xs):
  raise Unknown('P V root sup undecided')
 return limit4

if __name__=='__main__':
 from ordinal import show
 for t in sys.argv[1:]:
  s=tuple(map(int,t))
  try:print(t,show(value(s)))
  except Unknown as e:print(t,'UNKNOWN',e)
