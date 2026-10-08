"""強2階探索数列, definition as fixed on 2026-09-26 (rev 76008), literal.

  br     = min{ i | 1 < i <= L and ( S_{mbp(p(i))} <= S_{mbp(p(i-1))}
                    or (S_k)_{k=mbp(p(i))+1}^L <= (S_k)_{k=mbp(p(i-1))+1}^L ) }
  mbp(x) = min({ i | x <= i < L, S_i < S_L,
                     (S_k)_{k=mbp(x+1)+1}^L < (S_k)_{k=i+1}^L } ∪ {L-1})  if x < L
           L-1                                                            otherwise
  G = S_1..S_{mbp(br)},  B = S_{mbp(br)+1}..S_{L-1} ⌢ (S_L - 1)
CUT = "mbp(br)" is the literal text; "pbp(br)" uses mbp(p(br)) instead.
"""
import ssos

CUT = "mbp(br)"


class Seq(ssos.Seq):
    def mbp(self, x):
        L = self.L
        if x >= L:
            return L - 1
        if x in self._mbp:
            return self._mbp[x]
        m = self.mbp(x + 1)
        rk = self.rank
        cand = [i for i in range(x, L)
                if self.S[i - 1] < self.S[L - 1] and rk[m + 1] < rk[i + 1]]
        r = min(cand + [L - 1])
        self._mbp[x] = r
        return r

    def br(self):
        L, S, rk = self.L, self.S, self.rank
        for i in range(2, L + 1):
            a, b = self.mbp(self.p(i)), self.mbp(self.p(i - 1))
            if S[a - 1] <= S[b - 1] or rk[a + 1] <= rk[b + 1]:
                return i
        return None


def parts(S):
    S = tuple(S)
    q = Seq(S)
    br = q.br()
    c = q.mbp(br) if CUT == "mbp(br)" else q.mbp(q.p(br))
    return S[:c], S[c:-1] + (S[-1] - 1,)


def fs(S, n):
    G, B = parts(S)
    return G + B * n
