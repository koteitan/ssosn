"""Block view of the {0,1}-letter fragment (S over {0,1} with no "1,1").
S = (0,1^w1,0,1^w2,...) gives letters w; letters split at 0 give blocks
[b1,b2,...] (b = number of consecutive letter-1s).  Trailing letter-0s
are shown as '+k' (successor)."""
import ssos

def letters(S):
    L = []
    for v in S:
        if v == 0:
            L.append(0)
        else:
            L[-1] += 1
    return L

def blocks(S):
    L = letters(S)
    assert L[0] == 0
    body, k = L[1:], 0
    while body and body[-1] == 0:
        body.pop(); k += 1
    bl, c = [], 0
    for w in body:
        if w == 1:
            c += 1
        else:
            bl.append(c); c = 0
    bl.append(c)
    s = "[" + ",".join(map(str, bl)) + "]"
    return s + (f"+{k}" if k else "")

def from_blocks(bl):
    L = [0]
    for i, b in enumerate(bl):
        L += ([0] if i else []) + [1] * b
    return tuple(x for w in L for x in [0] + [1] * w)

def is01(S):
    return max(S) <= 1 and all(not (S[i] == 1 and S[i+1] == 1) for i in range(len(S)-1))
