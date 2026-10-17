"""Token expansion laws, independent of harness and ordinal valuation."""

def A(k):return (0,1,2)+(0,2)*k
W=A(0)+(1,)
TOK=('A0','A1','A2','E1','W')
BASE=(0,0,2,1)
HI=(0,0,2,1,0,2)

def seq(tokens):
 out=BASE
 for token in tokens:
  if token=='W':out+=W
  elif token[0] in 'AE':out+=A(int(token[1:]))+((1,) if token[0]=='E' else ())
  else:raise ValueError(token)
 return out

def a_context(tokens):
 """R,T,C for a final A_k, k>=1.

 The rightmost unit A_d W^m with d<k and m>0 starts a fresh term at
 the bumped depth. R ends after that unit and C=W^m. If no such unit
 exists, R is the leading W^j and C=W^(j+1).
 """
 k=int(tokens[-1][1:]);j=0
 while j<len(tokens) and tokens[j]=='W':j+=1
 cut=j;copies=j+1;i=j
 while i<len(tokens)-1:
  atom=tokens[i];i+=1;m=0
  while i<len(tokens)-1 and tokens[i]=='W':m+=1;i+=1
  if atom.startswith('A') and int(atom[1:])<k and m:
   cut=i;copies=m
 return tuple(tokens[:cut]),tuple(tokens[cut:-1]),('W',)*copies

def components(tokens):
 """H,Q,V such that the proposed real term is H Q^(n-1) V."""
 tokens=tuple(tokens);last=tokens[-1]
 if last.startswith('E'):
  return seq(tokens[:-1]+('A'+last[1:],)),(0,2),(0,)
 if last=='W':
  j=0
  while j<len(tokens) and tokens[j]=='W':j+=1
  if j==len(tokens):
   roots=('W',)*(j-1)
   return seq(roots),seq(('E1',)+roots)[4:],A(0)+(0,)
  cut=len(tokens)-2
  while tokens[cut]=='W':cut-=1
  return seq(tokens[:-1]),seq(tokens[cut:-1])[4:],A(0)+(0,)
 k=int(last[1:])
 if k==0:return None
 R,T,C=a_context(tokens);a=('A'+str(k-1),)
 return seq(R+T+a),seq(C+T+a)[4:],(0,1)

def expected(tokens,n):
 parts=components(tokens)
 if parts is None:return None
 head,repeat,tail=parts
 return head+repeat*(n-1)+tail
