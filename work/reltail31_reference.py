"""Measure relative tails by contracted REAL expansions, never by seed rules.

The inferred sups are finite diagnostics, not proofs.  Every recursive limit
must have the same evalord.sup result for its first 3 and first 5 samples.
Budgets, escaping the unit, and unstable inferences are reported as Unknown.
"""
import time
from functools import lru_cache

import harness
import evalord
from ordinal import ZERO, ONE, add, cmp

A0 = (0, 1, 2)


class Undecided(Exception):
    pass


class Reference:
    def __init__(self, base, samples=5, seconds=2, max_nodes=10000, max_depth=120,
                 depth=0, max_memo=50000):
        if samples < 5:
            raise ValueError('at least 5 samples are required')
        self.base = tuple(base)
        self.samples = samples
        self.seconds = seconds
        self.max_nodes = max_nodes
        self.max_depth = max_depth
        self.successor_token = A0 + (0, 2) * depth
        self.max_memo = max_memo
        self.memo = {(): ZERO}
        self.calls = self.limits = 0
        self.top = None

    def induced(self, tail, n):
        """Recompute the cut; remove only the specified outer terminal wrapper."""
        source = self.base + tuple(tail)
        child = harness.fs(source, n)
        terminal = (0,) if source[-1] == 1 else (0, 1) if source[-1] == 2 else None
        if terminal is None or child[-len(terminal):] != terminal:
            raise Undecided('unexpected outer terminal')
        core = child[:-len(terminal)]
        if core[:len(self.base)] != self.base:
            raise Undecided('contracted term escapes unit: ' + str(n))
        result = core[len(self.base):]
        if result >= tuple(tail):
            raise Undecided('contracted term does not decrease lexicographically')
        return result

    def evaluate(self, tail):
        if len(self.memo) > self.max_memo:
            self.memo = {(): ZERO}
        self.deadline = time.monotonic() + self.seconds
        self.start_calls = self.calls
        self.top = tuple(tail)
        return self._value(tuple(tail), 0)

    def _value(self, tail, depth):
        if tail in self.memo:
            return self.memo[tail]
        if time.monotonic() >= self.deadline:
            raise Undecided('per-case timeout')
        if self.calls - self.start_calls >= self.max_nodes:
            raise Undecided('per-case node budget')
        if depth >= self.max_depth:
            raise Undecided('recursion depth budget')
        if len(tail) > 1500:
            raise Undecided('raw length budget')
        self.calls += 1
        # This is the prescribed successor law at the unit depth, not a seed.
        if tail[-len(self.successor_token):] == self.successor_token:
            value = add(self._value(tail[:-len(self.successor_token)], depth + 1), ONE)
        else:
            children = [self.induced(tail, n) for n in range(1, self.samples + 1)]
            xs = [self._value(child, depth + 1) for child in children]
            if any(cmp(a, b) >= 0 for a, b in zip(xs, xs[1:])):
                raise Undecided('inferred children not strictly increasing')
            three = evalord.sup(xs[:3])
            value = evalord.sup(xs)
            if value is None or three is None or cmp(three, value):
                raise Undecided('unstable/unknown 3-vs-' + str(self.samples) + '-sample sup')
            if any(cmp(x, value) >= 0 for x in xs):
                raise Undecided('sample not below inferred sup')
            self.limits += 1
        self.memo[tail] = value
        return value


def memoize_cut():
    cls = harness.Seq
    original = cls.cut
    @lru_cache(maxsize=32768)
    def cached(s, mode):
        return original(cls(s, mode))
    cls.cut = lambda self: cached(self.S, self.mode)

