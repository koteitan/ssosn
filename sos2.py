"""再定式化版 2階探索数列 (2025, with the 2026/07/30 fix), as written.

  pbp = min{ i >= 2 | (S_k)_{k=p(i)+1}^L < (S_k)_{k=p(i-1)+1}^L } ∪ {L-1}
  cbr = { i | p(pbp) <= i < L and S_i < S_L } ∪ {1}
  br  = the i in cbr with the largest (S_k)_{k=i+1}^L
  G = S_1..S_br,  B = S_{br+1}..S_{L-1} ⌢ (S_L - 1)
"""
import ssos


def parts(S):
    S = tuple(S)
    q = ssos.Seq(S)
    L = q.L
    rk = q.rank
    pbp = L - 1
    for i in range(2, L + 1):
        if rk[q.p(i) + 1] < rk[q.p(i - 1) + 1]:
            pbp = i
            break
    lo = q.p(pbp)
    cbr = {i for i in range(lo, L) if S[i - 1] < S[-1]} | {1}
    br = max(cbr, key=lambda i: rk[i + 1])
    return S[:br], S[br:-1] + (S[-1] - 1,)


def fs(S, n):
    G, B = parts(S)
    return G + B * n
