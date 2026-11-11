# For so(2n): count (a) all equivariant operators L^2(x)A -> L^(d-1)(x)A, A = Clifford algebra,
# and (b) those whose linearised equation can come from an action: Hom(Sym^2 A, L^3).
import sys
from itertools import product
from math import comb
from collections import Counter
def run(n):
    d = 2 * n; rho = tuple(range(n - 1, -1, -1))
    def dom(v):
        a = [abs(x) for x in v]
        if len(set(a)) < n: return 0, None
        order = sorted(range(n), key=lambda i: -a[i])
        inv = sum(1 for i in range(n) for j in range(i + 1, n) if order[i] > order[j])
        w = [a[i] for i in order]
        if sum(1 for x in v if x < 0) % 2 == 1 and w[-1] != 0: w[-1] = -w[-1]
        return (-1) ** inv, tuple(w)
    def wts(b):
        out = {}
        for nu in product((-1, 0, 1), repeat=n):
            j = sum(1 for x in nu if x)
            if b >= j and (b - j) % 2 == 0 and (b - j) // 2 <= n - j: out[nu] = comb(n - j, (b - j) // 2)
        return out
    def irreps(k):
        k = min(k, d - k)
        if k == n: return [tuple([1] * n), tuple([1] * (n - 1) + [-1])]
        return [tuple([1] * k + [0] * (n - k))]
    def tensor(lam, w):
        out = Counter()
        for nu, m in w.items():
            s, x = dom(tuple(lam[i] + nu[i] + rho[i] for i in range(n)))
            if s: out[tuple(x[i] - rho[i] for i in range(n))] += s * m
        return Counter({k: v for k, v in out.items() if v})
    W = {b: wts(b) for b in range(d + 1)}
    def ext(a, k):
        out = Counter()
        for lam in irreps(k): out.update(tensor(lam, W[a]))
        return out
    hom = lambda x, y: sum(m * y.get(l, 0) for l, m in x.items())
    N = sum(hom(ext(2, k), ext(1, l)) for k in range(d + 1) for l in range(d + 1))
    AA = Counter()
    for k in range(d + 1):
        for l in range(d + 1): AA.update(ext(l, k))
    WA = Counter()
    for b in range(d + 1):
        for nu, m in W[b].items(): WA[tuple(2 * x for x in nu)] += m
    psi2 = tensor(tuple([0] * n), WA)
    sym2 = {l: (AA.get(l, 0) + psi2.get(l, 0)) // 2 for l in set(AA) | set(psi2)}
    assert all((AA.get(l, 0) + psi2.get(l, 0)) % 2 == 0 for l in sym2)
    L3 = Counter(); [L3.update({ir: 1}) for ir in irreps(3)]
    N1 = sum(sym2.get(l, 0) * m for l, m in L3.items())
    inv3 = sum(1 for ir in irreps(3) if ir == tuple([0] * n))
    print('d = %2d: all operators %4d | action-compatible to first order %3d | invariant 3-forms %d' % (d, N, N1, inv3))
for n in (map(int, sys.argv[1:]) if len(sys.argv) > 1 else (2, 3, 4, 7)): run(n)
