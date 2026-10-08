"""Author's stated intent (2026-09-25, relayed):
  penetrate to the next ancestor only if the max bad part is updated AND
  the new bad part's root value is larger than the old root value.
pbp(i) = mbp(p(i)) with mbp = argmax bad part in [p(i), L), S_root < S_L.
br = first i >= 2 where NOT(bp(i) > bp(i-1) and S_pbp(i) > S_pbp(i-1)).
CUT: 'br' -> G ends at pbp(br);  'prev' -> G ends at pbp(br-1).
"""
import ssos

def parts(S, cut="br"):
    S = tuple(S); L = len(S); q = ssos.Seq(S); rk = q.rank
    ssos.MBP = "argmax"
    i = 2
    while i <= L:
        a, b = q.pbp(i), q.pbp(i - 1)
        if not (rk[a + 1] > rk[b + 1] and S[a - 1] > S[b - 1]):
            break
        i += 1
    c = q.pbp(i) if cut == "br" else q.pbp(i - 1)
    return S[:c], S[c:-1] + (S[-1] - 1,)

def fs(S, n, cut="br"):
    G, B = parts(S, cut); return G + B * n
