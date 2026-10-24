"""Value-free candidate grammar for (0021) token words below 002102.

Prefix A clauses are MidOK/BlockLe of TokenCut.lean. E is tested as the
infinite-depth limit of those clauses; the A0/W bound is structural.
No standardness test, sequence expansion, or ordinal values occur here.
"""
import token_laws as L


def raw(tokens):return L.seq(tuple(tokens))[4:]


def periodic_compare(left,right):
    """Compare left+A_infinity and right+A_infinity exactly.

    A_infinity = 012 (02)^omega. After both finite prefixes and heads,
    the two streams are periodic with period 2; two further symbols suffice.
    """
    a=tuple(left)+(0,1,2);b=tuple(right)+(0,1,2)
    def at(prefix,i):return prefix[i] if i<len(prefix) else (0,2)[(i-len(prefix))%2]
    for i in range(max(len(a),len(b))+2):
        x,y=at(a,i),at(b,i)
        if x!=y:return -1 if x<y else 1
    return 0


def context_clause(tokens,infinite=False):
    if infinite:
        k=1+max((int(t[1:]) for t in tokens[:-1] if t.startswith('A')),default=0)
        r,mid,copies=L.a_context(tokens[:-1]+('A'+str(k),))
    else:
        k=int(tokens[-1][1:]);r,mid,copies=L.a_context(tokens)
    midok=(not mid or mid[0]!='W') and all(not t.startswith('A') or (not infinite and int(t[1:])>=k) for t in mid)
    bound=raw(copies[:-1]+mid)
    bad=[]
    for i,t in enumerate(mid):
        if t not in ('W','E1'):continue
        tail=raw(mid[i+1:])
        okay=periodic_compare(tail,bound)<=0 if infinite else tail+L.A(k)<=bound+L.A(k)
        if not okay:bad.append(i)
    return dict(kind='E_infinity' if infinite else 'A',R=r,T=mid,C=copies,K=None if infinite else k,
                MidOK=midok,BlockLe=not bad,bad_blocks=bad,okay=midok and not bad)


def last_clause(tokens):
    tokens=tuple(tokens);last=tokens[-1]
    if last=='E1':return context_clause(tokens,True)
    if last.startswith('A') and last!='A0':return context_clause(tokens)
    if last=='W':
        i=len(tokens)-2
        while i>=0 and tokens[i]=='W':i-=1
        if i>=0 and tokens[i]=='A0':
            copies=L.a_context(tokens[:i]+('A1',))[2]
            m=len(tokens)-i-1
            return dict(kind='A0_W_bound',m=m,bound=len(copies),okay=m<=len(copies))
    return dict(kind='unconditional',okay=True)


def iteration_clause(tokens,bounded=False):
    i=len(tokens)-2
    while i>=0 and tokens[i]=='W':i-=1
    if i<0:return dict(kind='leading_W',okay=True)
    stem=tokens[i];prefix=tuple(tokens[:i]);m=len(tokens)-i-1
    if stem=='E1':
        trial=context_clause(prefix+('E1',),True)
        bound=len(trial['C'])-1
        return dict(kind='E_W_bound',m=m,bound=bound,okay=m<=bound)
    k=int(stem[1:])
    trial=context_clause(prefix+('A'+str(k+1),))
    bound=len(trial['C'])
    return dict(kind='W_opening_context',surrogate=trial,m=m,bound=bound,
                okay=trial['okay'] and (not bounded or m<=bound))


def explain(tokens,refined=False,lowered=False,bounded=False):
    if any(t not in ('E1','W') and not (t.startswith('A') and t[1:].isdigit()) for t in tokens):
        return dict(accepted=False,kind='unsupported_token')
    for size in range(1,len(tokens)+1):
        clause=last_clause(tuple(tokens[:size]))
        if not clause['okay']:return dict(accepted=False,prefix_size=size,**clause)
        if refined and tokens[size-1]=='W':
            clause=iteration_clause(tuple(tokens[:size]),bounded)
            if not clause['okay']:return dict(accepted=False,prefix_size=size,**clause)
        if lowered and tokens[size-1]!='W' and tokens[size-1]!='A0':
            last=tokens[size-1]
            maximum=len(raw(tokens[:size-1]))+2 if last=='E1' else int(last[1:])
            for k in range(1,maximum+1):
                trial=context_clause(tuple(tokens[:size-1])+('A'+str(k),))
                if not trial['okay']:
                    return dict(accepted=False,prefix_size=size,kind='lower_depth',target_depth=k,clause=trial)
    return dict(accepted=True)


def accept(tokens,refined=False,lowered=False,bounded=False):
    return explain(tokens,refined,lowered,bounded)['accepted']


def parse(body):
    body=tuple(body);out=[]
    while body:
        if body[:3]!=(0,1,2):raise ValueError(('not core token',body))
        pos,k=3,0
        while body[pos:pos+2]==(0,2):pos+=2;k+=1
        if body[pos:pos+1]==(1,):
            out.append('W' if k==0 else 'E'+str(k));pos+=1
        else:out.append('A'+str(k))
        body=body[pos:]
    return tuple(out)
