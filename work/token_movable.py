"""Syntax only: A_k and head tokens with movable, possibly multiple, ones."""
from dataclasses import dataclass

HEAD=(0,1,2)
D=(0,2)


@dataclass(frozen=True)
class Head:
    gaps: tuple

    def raw(self):
        result=HEAD+D*self.gaps[0]
        for gap in self.gaps[1:]:result+=(1,)+D*gap
        return result

    def name(self):
        if len(self.gaps)==1:return 'A'+str(self.gaps[0])
        return ('T' if len(self.gaps)==2 else 'U')+'('+','.join(map(str,self.gaps))+')'


W=Head((0,0))


def parse(body):
    body=tuple(body)
    result=[]
    while body:
        if body[:3]==HEAD:
            body=body[3:]
            gaps=[0]
            while body:
                if body[:2]==D:gaps[-1]+=1;body=body[2:]
                elif body[0]==1:gaps.append(0);body=body[1:]
                else:break
            result.append(Head(tuple(gaps)))
        elif body[:2]==D:result.append('D');body=body[2:]
        elif body[:1]==(1,):result.append('I');body=body[1:]
        elif body[:1]==(0,):result.append('z');body=body[1:]
        else:raise ValueError(('unparsed movable suffix',body))
    return tuple(result)


def raw(tokens):
    return sum((t.raw() if isinstance(t,Head) else D if t=='D' else (1,) if t=='I' else (0,) for t in tokens),())


def names(tokens):
    return [t.name() if isinstance(t,Head) else t for t in tokens]


def is_leading(tokens):
    return all(t=='D' or isinstance(t,Head) and len(t.gaps)==2 and t.gaps[0]==0 for t in tokens)


def w_components(tokens):
    """Candidate H Q^(n-1) V law, preserving trailing-one E tokens."""
    if not tokens or tokens[-1]!=W:return None
    if is_leading(tokens):
        r=tokens[:-1]
        return (0,0,2,1)+raw(r),raw((Head((1,0)),)+r),HEAD+(0,), 'leading'
    start=len(tokens)-2
    while start>=0 and tokens[start]==W:start-=1
    if start<0 or not isinstance(tokens[start],Head):return None
    atom=tokens[start]
    unit=tokens[start:-1]
    kind='plain-copy'
    if len(atom.gaps)==2 and atom.gaps[0]==0 and atom.gaps[-1]>0:
        # A previous internal-one token may already have opened the node
        # at depth b. Replay the unit, rather than skipping those tokens.
        leading=0
        while leading<len(tokens)-1 and is_leading(tokens[:leading+1]):leading+=1
        unit=()
        depth=0
        erased=False
        for current in tokens[leading:-1]:
            if not isinstance(current,Head):return None
            if current==W:
                unit+=(current,)
            elif len(current.gaps)==1:
                unit=(current,)
                depth=current.gaps[0]
            elif len(current.gaps)==2 and current.gaps[0]==0:
                b=current.gaps[-1]
                if depth<b:
                    unit=(Head((b,)),)
                    depth=b
                    erased=True
                else:unit+=(current,)
            elif len(current.gaps)==2:
                unit=(current,)
                depth=current.gaps[0]
            else:return None
        kind='erase-opened-unit' if erased else 'retain-built-unit'
    elif len(atom.gaps)>2:return None
    return (0,0,2,1)+raw(tokens[:-1]),raw(unit),HEAD+(0,),kind
