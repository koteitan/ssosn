"""Binary token family based at (2), derived separately from the (2,1) family.

A=(0,1,2), D=(0,2), F(0)=A, F(1)=D.
The candidate value of 00 2 F(Y) is epsilon_(conj.v(Y)).
No lower/rule6 import or general lowering rule is used.
"""
import conj

A = (0, 1, 2)
D = (0, 2)


def emit(bits):
    return sum((A if bit == 0 else D for bit in bits), ())


def parse(block):
    block = tuple(block)
    if block[:1] != (2,):
        return None
    tail = block[1:]
    bits = []
    while tail:
        if tail[:3] == A:
            bits.append(0)
            tail = tail[3:]
        elif tail[:2] == D:
            bits.append(1)
            tail = tail[2:]
        else:
            return None
    return tuple(bits)


def index(bits):
    return conj.v(tuple(bits))


def components(bits):
    """Pure predicted raw cut G,B; actual term is G B^n.

    For Y=R T 1, q=rcut_Y(Y) is the binary tree cut and R=Y[:q].
    The equivalent token law is 00 2 F(R T) (A F(T))^(n-1) 01.
    For Y=R 0 the law is 00 2 F(R) 01 1^n (epsilon successor).
    """
    bits = tuple(bits)
    if not bits:
        # 002[n] = 00 1^n: epsilon_0 is the tower boundary.
        return (0, 0), (1,)
    if bits[-1] == 0:
        return (0, 0, 2) + emit(bits[:-1]) + (0, 1), (1,)
    q = conj.rcut_Y(bits)
    prefix, repeat = bits[:q], bits[q:-1]
    return (0, 0) + ((2,) + emit(prefix))[:-1], (2,) + emit(repeat) + (0, 1)
