"""Conjectured lift from the 0/1 fragment to self-referential blocks in [e0, e0*2)
(2026-10-16):  lift(Y) = (2,1) ⌢ emit(parse Y, 0),  value e_(e0 + v(Y)).

emit(list, d, first): walk the units of a list at depth d, skipping the two separator
zeros between blocks.  The opener of a unit is (0,2) for the first unit of a block's
T-list (it extends the opener of the block) and A_d = (0,1,2)⌢(0,2)^d otherwise.
  z    -> opener
  b w  -> opener ⌢ (emit(w, d+1, True) if w else (0,1,2,1)),
          preceded by A_d ⌢ (0,1,2,1) (a new term w at depth d) unless it is the first unit;
          a later b[] is just that A_d ⌢ (0,1,2,1)"""
import tree

def A(d): return (0, 1, 2) + (0, 2) * d

def units_nosep(t):
    """units of a forward unit list, without the separator zeros between blocks"""
    out = []
    n = len(t)
    for i, x in enumerate(t):
        if x == 'z':
            nxt = next((y for y in t[i+1:] if y != 'z'), None)
            if nxt is not None:      # a zero before a later block is a separator
                continue
        out.append(x)
    return out

def emit(t, d, first):
    out = ()
    for i, x in enumerate(units_nosep(t)):
        if x != 'z' and i > 0:
            out += A(d) + (0, 1, 2, 1)      # a later block: first a new term w at depth d
            if not x[1]:
                continue                     # the block b[] is that term w
        out += (0, 2) if (first and i == 0) else A(d)
        if x != 'z':
            w = x[1]
            out += emit(w, d + 1, True) if w else (0, 1, 2, 1)
    return out

def lift(Y):
    return (2, 1) + emit(tree.parse(''.join(map(str, Y))), 0, False)


_INV = None


def unlift(u, maxlen=16):
    """Y with lift(Y) == u (u without the leading (0,0)), or None.  Table of all
    StdShape Y with |Y| <= maxlen (exploration only)."""
    global _INV
    if _INV is None:
        import itertools, importlib.util, os
        spec = importlib.util.spec_from_file_location(
            'shape', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'shape.py'))
        sh = importlib.util.module_from_spec(spec); spec.loader.exec_module(sh)
        _INV = {}
        for L in range(0, maxlen + 1):
            for Y in itertools.product((0, 1), repeat=L):
                if sh.shape(tree.parse(''.join(map(str, Y)))):
                    _INV[lift(Y)] = Y
    return _INV.get(tuple(u))
