import sys
import os; _h = os.path.dirname(os.path.abspath(__file__)); sys.path[:0] = [_h, os.path.dirname(_h)]
import harness, std
def tok(S):
    """S = (0,0,2,1)+...: tokens A_k, W, 1, trailing 0s"""
    assert S[:4] == (0,0,2,1), S
    u = S[4:]; out = []; i = 0
    while i < len(u):
        if u[i:i+3] == (0,1,2):
            j = i + 3; k = 0
            while u[j:j+2] == (0,2): j += 2; k += 1
            if k == 0 and u[j:j+1] == (1,) : out.append('W'); i = j + 1; continue
            out.append('A%d' % k); i = j; continue
        if u[i] == 1: out.append('1'); i += 1; continue
        if u[i] == 0: out.append('0'); i += 1; continue
        out.append('?%d' % u[i]); i += 1
    return ' '.join(out)
T = {'A0': (0,1,2), 'A1': (0,1,2,0,2), 'A2': (0,1,2,0,2,0,2), 'A3': (0,1,2,0,2,0,2,0,2), '1': (1,), 'W': (0,1,2,1)}
for c in sys.argv[1:]:
    S = (0,0,2,1) + sum((T[t] for t in c.split()), ())
    print('==', c, 'std' if std.is_standard(S) else 'NONSTD')
    for n in range(1, 5):
        print('  ', n, tok(harness.fs(S, n)))
