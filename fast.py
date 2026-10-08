"""Ordinal of a 強2階探索数列 with shortcut rules (hypotheses, checked later).

  succ   o(S⌢0) = o(S)+1
  add    S = A⌢(x,0,0,y)⌢..., last such split with x,y > 0:
         o(S) = o(A⌢x⌢0) + (-1 + o((0,0)⌢Y))       (Y = part after the 0,0)
  mulw   S = (0,0)⌢Z⌢(0,1), Z ends with a nonzero value, no 0,0 inside Z:
         o(S) = o((0,0)⌢Z)·ω
  bw     S = (0,0)⌢X, X over {0,1}, no 0,0 inside, starts and ends with 1,
         X = 1^r1 0 1^r2 0 ... 0 1^rk :
         o(S) = ω^(-1 + o((0,0)⌢D(X))),  D(X) = 1^(r1-1) 0 ... 0 1^(rk-1)
         (the {0,1} fragment is Beklemishev's worm on the run lengths)
  else   o(S) = sup_n o(fs(S,n)), n = 1..3   (sup guessed, see evalord.sup)

With RULES off (the set is empty) this is the plain definition.
"""
import sys
import ssos
from ordinal import ZERO, ONE, succ, add, w, show, lt
from evalord import sup, exponent

sys.setrecursionlimit(1000000)

RULES = {"add", "mulw", "bw"}
NS = (1, 2, 3)
memo = {}


class Unknown(Exception):
    pass


def minus1(x):
    # -1 + x : drop one from a finite ordinal, identity on infinite ones
    if x and all(t == ONE[0] for t in x):
        return x[:-1]
    return x


def times_w(x):
    # x·ω for x > 0 : ω^(lead exponent + 1)
    return w(succ(exponent(x[0])))


def split_add(S):
    for j in range(len(S) - 3, 0, -1):
        if S[j - 1] > 0 and S[j] == 0 and S[j + 1] == 0 and S[j + 2] > 0:
            return S[:j + 1], (0, 0) + S[j + 2:]
    return None


def bw_runs(S):
    if S[:2] != (0, 0) or len(S) < 3:
        return None
    X = S[2:]
    if X[0] != 1 or X[-1] != 1 or any(v > 1 for v in X):
        return None
    if any(X[i] == 0 and X[i + 1] == 0 for i in range(len(X) - 1)):
        return None
    runs, c = [], 0
    for v in X:
        if v:
            c += 1
        else:
            runs.append(c)
            c = 0
    return runs + [c]


def o(S):
    S = tuple(S)
    if S in memo:
        return memo[S]
    if not S:
        r = ZERO
    elif S[-1] == 0:
        r = succ(o(S[:-1]))
    else:
        sp = split_add(S) if "add" in RULES else None
        if sp:
            r = add(o(sp[0]), minus1(o(sp[1])))
        elif "bw" in RULES and (runs := bw_runs(S)) and runs[0] >= 2:
            D = ()
            for i, k in enumerate(runs):
                D += ((0,) if i else ()) + (1,) * (k - 1)
            r = w(minus1(o((0, 0) + D)))
        elif ("mulw" in RULES and len(S) >= 5 and S[-2:] == (0, 1)
              and S[-3] > 0 and S[:2] == (0, 0)):
            r = times_w(o(S[:-2]))
        else:
            xs = [o(ssos.fs(S, n)) for n in NS]
            r = sup(xs)
            if r is None:
                raise Unknown((S, [show(x) for x in xs]))
    memo[S] = r
    return r


if __name__ == "__main__":
    for arg in sys.argv[1:]:
        S = tuple(int(x) for x in arg.split(","))
        print(S, show(o(S)), flush=True)
