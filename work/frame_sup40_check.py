"""§40 diagnostic: try a three-term ordinal frame and seek later overshoots.

This deliberately does not alter tail_symbolic.F.  Its candidates are not
accepted as values: later real terms can exceed them.
"""

import functools
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import evalord
import frame_sup40
import pure_s39
import std
import tail_symbolic as S
import token_value as TV
from ordinal import ONE, add, cmp, show


pure_s39.setup(0)
S.load_cache(pure_s39.TAIL_CACHE)


@functools.lru_cache(maxsize=None)
def trial_F(t, depth=0, level=0):
    if level > 64:
        raise S.Undecided('trial recursion depth limit')
    cached = S._F_CACHE.get((S.BASE, False, t, depth))
    if cached and cached[0] == 'value':
        return cached[1]
    if not t:
        return S.ZERO
    if t[-3:] == S.A0:
        return add(trial_F(t[:-3], depth, level + 1), ONE)
    h, q, _v, cs = S.periodic(t, depth)
    block = S.s_block_k(q)
    if block is not None:
        k, r = block
        step = add(ONE, trial_F(r, depth, level + 1))
        return TV.bump_last(trial_F(h, depth, level + 1), k,
                            S.mul_omega(step))
    xs = [trial_F(c, depth, level + 1) for c in cs]
    if any(cmp(a, b) >= 0 for a, b in zip(xs, xs[1:])):
        raise S.Undecided('trial terms not increasing')
    guess = frame_sup40.candidate(xs)
    if guess is not None:
        return guess[0]
    x4 = trial_F(S.induced(t, 4, depth), depth, level + 1)
    s3, s4 = evalord.sup(xs), evalord.sup(xs + [x4])
    if s3 is None or s4 is None or cmp(s3, s4):
        raise S.Undecided('trial unstable sup')
    return s3


def check(word, upto=6):
    t = S.seq(word)
    try:
        parent = trial_F(t)
    except (S.Undecided, TV.Unknown) as e:
        print(word, 'UNDECIDED', str(e), flush=True)
        return
    print(word, 'standard', std.is_standard(S.BASE + t),
          'candidate', show(parent), flush=True)
    for n in range(1, upto + 1):
        try:
            term = trial_F(S.induced(t, n))
            relation = cmp(term, parent)
            print(' ', n, show(term), 'below' if relation < 0 else
                  'EQUAL' if relation == 0 else 'EXCEEDS', flush=True)
            if relation >= 0:
                break
        except (S.Undecided, TV.Unknown) as e:
            print(' ', n, 'UNDECIDED', str(e), flush=True)
            break


if __name__ == '__main__':
    words = sys.argv[1:] or [
        'W D W W D W D',
        'W D W D W W D W D',
        'W D D',
        'W D W D W D',
        'W D D A1',
        'W D D W',
        'W D D D',
        'W D D D A1',
    ]
    for word in words:
        check(word)
