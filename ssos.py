"""強2階探索数列 (strong second-order search sequence) expansion.

Transcription of the definition on the 巨大数研究 Wiki page, 1-based indices.
Sequence comparison is left-lexicographic (Python tuple order: a proper
prefix is smaller).

Two places look like typos, so both readings are selectable:
  MBP  "lit":    mbp(x) as written (strict < against mbp(x+1))
       "argmax": mbp(x) = the i in [x, L) with S_i < S_L whose
                 suffix (S_k)_{k=i+1}^L is largest (fallback L-1)
  CUT  "mbp(br)":    G = S_1..S_{mbp(br)}            (as written)
       "pbp(br)":    G = S_1..S_{mbp(p(br))}
       "pbp(br-1)":  G = S_1..S_{mbp(p(br-1))}
"""
import sys

MBP = "argmax"
CUT = "pbp(br)"


def suffix_ranks(S):
    """rank of each suffix S[i:] (0-based i) in left-lexicographic order,
    a proper prefix being smaller; prefix doubling, O(L log^2 L)."""
    L = len(S)
    if L == 0:
        return []
    rk = list(S)
    k = 1
    while True:
        key = [(rk[i], rk[i + k] if i + k < L else -1) for i in range(L)]
        order = sorted(range(L), key=key.__getitem__)
        new = [0] * L
        for j in range(1, L):
            new[order[j]] = new[order[j - 1]] + (key[order[j]] != key[order[j - 1]])
        rk = new
        if rk[order[-1]] == L - 1:
            return rk
        k *= 2


class Seq:
    def __init__(self, S):
        self.S = tuple(S)
        self.L = len(S)
        self._mbp = {}
        # rank[k] = position of suffix k (1-based) in lex order; rank[L+1] = -1
        # (the empty suffix is smaller than every other one)
        self.rank = [0] + suffix_ranks(self.S) + [-1]
        self._sp = {}
        self._p = [self.L]

    def s(self, k):
        return self.S[k - 1]

    def suf(self, k):
        """(S_j)_{j=k}^{L}"""
        return self.S[k - 1:]

    def sp(self, x):
        if x not in self._sp:
            rk = self.rank
            best = 1
            for i in range(x - 1, 0, -1):
                if rk[i] < rk[x]:
                    best = i
                    break
            self._sp[x] = best
        return self._sp[x]

    def p(self, i):
        while len(self._p) <= i:
            self._p.append(self.sp(self._p[-1]))
        return self._p[i]

    def mbp(self, x):
        L = self.L
        if x >= L:
            return L - 1
        if x in self._mbp:
            return self._mbp[x]
        if MBP == "lit":
            m = self.mbp(x + 1)
            cand = [i for i in range(x, L)
                    if self.s(i) < self.s(L) and self.suf(m + 1) < self.suf(i + 1)]
            r = min(cand + [L - 1])
        else:
            cand = [i for i in range(x, L) if self.s(i) < self.s(L)]
            r = max(cand, key=lambda i: self.rank[i + 1]) if cand else L - 1
        self._mbp[x] = r
        return r

    def pbp(self, i):
        return self.mbp(self.p(i))

    def PBP(self, i):
        return self.suf(self.pbp(i))

    def br(self):
        L = self.L
        rk = self.rank
        for i in range(2, L + 1):
            a, b = rk[self.pbp(i)], rk[self.pbp(i - 1)]   # PBP(i), PBP(i-1)
            if a <= b:
                return i
            if rk[self.pbp(i) + 1] <= rk[self.pbp(i - 1) + 1]:
                return i
        return None

    def cut(self):
        br = self.br()
        if br is None:
            raise ValueError(f"br undefined for {self.S}")
        if CUT == "mbp(br)":
            return self.mbp(br)
        if CUT == "pbp(br)":
            return self.pbp(br)
        return self.pbp(br - 1)


def parts(S):
    S = tuple(S)
    c = Seq(S).cut()
    return S[:c], S[c:-1] + (S[-1] - 1,)


def fs(S, n):
    """G ⌢ B^n (the expansion rule with the copy count given directly)."""
    G, B = parts(S)
    return G + B * n


def expand(S, n):
    """S[n] one step, as in the definition (f(n) = n+1)."""
    S = tuple(S)
    if S[-1] == 0:
        return S[:-1], n + 1
    return fs(S, n + 1), n + 1


if __name__ == "__main__":
    for arg in sys.argv[1:]:
        S = tuple(int(x) for x in arg.split(","))
        G, B = parts(S)
        print(S, "G=", G, "B=", B)
