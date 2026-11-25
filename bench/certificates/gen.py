"""Make matrix certificates for MatCert.

usage: python3 -I gen.py inverse P N SEED OUT [--corrupt]
       python3 -I gen.py nonsingular N BOUND SEED OUT [--corrupt]

inverse:     a pseudo-random N x N matrix A with entries in [0, P) and its inverse B modulo
             the prime P (Gauss-Jordan elimination mod P), so that A * B = 1 (mod P).
nonsingular: a pseudo-random N x N integer matrix A with entries in [-BOUND, BOUND], its
             determinant d and its adjugate B (fraction-free Gauss-Jordan elimination), so
             that A * B = d * 1 over the integers, d != 0.

--corrupt adds 1 to the last entry of B after checking, to make a wrong certificate
(the checker must reject it).

The entries come from splitmix64 seeded with SEED, so the output depends only on the
arguments. A seed whose matrix is singular is rejected (pick another). Before writing,
the certificate is checked by multiplying it out.

Output (text): a header line `inverse P N` or `nonsingular N D`, then the N rows of A and
the N rows of B, one row per line, entries separated by single spaces.
"""
import sys

MASK = (1 << 64) - 1


class SplitMix64:
    def __init__(self, seed):
        self.state = seed & MASK

    def next(self):
        self.state = (self.state + 0x9E3779B97F4A7C15) & MASK
        z = self.state
        z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & MASK
        z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & MASK
        return z ^ (z >> 31)

    def below(self, n):
        """Uniform in [0, n) by rejection."""
        limit = (1 << 64) - (1 << 64) % n
        while True:
            x = self.next()
            if x < limit:
                return x % n


def inverse_mod(a, p):
    n = len(a)
    m = [row[:] + [int(i == j) for j in range(n)] for i, row in enumerate(a)]
    for k in range(n):
        piv = next((r for r in range(k, n) if m[r][k] % p), None)
        if piv is None:
            raise SystemExit("gen: the matrix is singular modulo P; use another seed")
        m[k], m[piv] = m[piv], m[k]
        inv = pow(m[k][k], -1, p)
        m[k] = [x * inv % p for x in m[k]]
        rk = m[k]
        for i in range(n):
            f = m[i][k]
            if i != k and f:
                m[i] = [(x - f * y) % p for x, y in zip(m[i], rk)]
    return [row[n:] for row in m]


def det_adjugate(a):
    """(d, B) with A * B = d * 1, by fraction-free Gauss-Jordan elimination on [A | 1]."""
    n = len(a)
    m = [row[:] + [int(i == j) for j in range(n)] for i, row in enumerate(a)]
    prev = 1
    for k in range(n):
        piv = next((r for r in range(k, n) if m[r][k]), None)
        if piv is None:
            raise SystemExit("gen: the matrix is singular; use another seed")
        m[k], m[piv] = m[piv], m[k]
        rk = m[k]
        p = rk[k]
        for i in range(n):
            if i == k:
                continue
            f = m[i][k]
            row = []
            for x, y in zip(m[i], rk):
                q, r = divmod(p * x - f * y, prev)
                assert r == 0
                row.append(q)
            m[i] = row
        prev = p
    d = m[0][0]
    assert all(m[i][i] == d for i in range(n))
    return d, [row[n:] for row in m]


def product(a, b):
    bt = list(zip(*b))
    return [[sum(x * y for x, y in zip(row, col)) for col in bt] for row in a]


def write(out, header, a, b):
    with open(out, "w") as f:
        f.write(header + "\n")
        for row in a + b:
            f.write(" ".join(map(str, row)) + "\n")


def main():
    args = sys.argv[1:]
    corrupt = args[-1:] == ["--corrupt"]
    if corrupt:
        args = args[:-1]
    if len(args) == 5 and args[0] == "inverse":
        p, n, seed, out = int(args[1]), int(args[2]), int(args[3]), args[4]
        g = SplitMix64(seed)
        a = [[g.below(p) for _ in range(n)] for _ in range(n)]
        b = inverse_mod(a, p)
        assert all((x - int(i == j)) % p == 0 for i, row in enumerate(product(a, b)) for j, x in enumerate(row))
        if corrupt:
            b[-1][-1] = (b[-1][-1] + 1) % p
        write(out, f"inverse {p} {n}", a, b)
    elif len(args) == 5 and args[0] == "nonsingular":
        n, bound, seed, out = int(args[1]), int(args[2]), int(args[3]), args[4]
        g = SplitMix64(seed)
        a = [[g.below(2 * bound + 1) - bound for _ in range(n)] for _ in range(n)]
        d, b = det_adjugate(a)
        assert d != 0
        assert product(a, b) == [[d if i == j else 0 for j in range(n)] for i in range(n)]
        if corrupt:
            b[-1][-1] += 1
        write(out, f"nonsingular {n} {d}", a, b)
    else:
        sys.exit(__doc__)


main()
