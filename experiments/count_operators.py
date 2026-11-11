# Count the Spin(7,7)-equivariant linear maps  L^2 (x) A  ->  L^13 (x) A,  A = u(64,64).
# Over C this is so(14): A = sum_k L^k(C^14), L^13 = L^1.  Tensor products via the Brauer-Klimyk formula.
from itertools import product
from math import comb
from collections import Counter
from fractions import Fraction
n = 7; rho = tuple(range(n - 1, -1, -1))
def dom(v):
    """Reflect v into the dominant chamber of D7. Returns (sign, weight) or (0, None) if on a wall."""
    a = [abs(x) for x in v]
    if len(set(a)) < n: return 0, None
    order = sorted(range(n), key=lambda i: -a[i])
    inv = sum(1 for i in range(n) for j in range(i + 1, n) if order[i] > order[j])
    w = [a[i] for i in order]
    if sum(1 for x in v if x < 0) % 2 == 1 and w[-1] != 0: w[-1] = -w[-1]
    return (-1) ** inv, tuple(w)
def weights_ext(b):
    out = {}
    for nu in product((-1, 0, 1), repeat=n):
        j = sum(1 for x in nu if x)
        if b >= j and (b - j) % 2 == 0 and (b - j) // 2 <= n - j: out[nu] = comb(n - j, (b - j) // 2)
    return out
def irreps_ext(k):
    k = min(k, 14 - k)
    if k == 7: return [tuple([1] * 7), tuple([1] * 6 + [-1])]
    return [tuple([1] * k + [0] * (n - k))]
def tensor(lam, wts):
    out = Counter()
    for nu, m in wts.items():
        s, w = dom(tuple(lam[i] + nu[i] + rho[i] for i in range(n)))
        if s: out[tuple(w[i] - rho[i] for i in range(n))] += s * m
    return Counter({k: v for k, v in out.items() if v})
def dim(lam):
    l = [lam[i] + rho[i] for i in range(n)]; d = Fraction(1)
    for i in range(n):
        for j in range(i + 1, n):
            d *= Fraction((l[i] - l[j]) * (l[i] + l[j]), (rho[i] - rho[j]) * (rho[i] + rho[j]))
    return int(d)
W = {b: weights_ext(b) for b in range(15)}
def ext_tensor(a, k):               # L^a (x) L^k, a in {1,2}
    out = Counter()
    for lam in irreps_ext(k): out += tensor(lam, W[a])
    return out
def ext_tensor_swapped(a, k):       # same thing computed the other way round, as a check
    return tensor(irreps_ext(a)[0], W[k])
ok = True
for a in (1, 2):
    for k in range(15):
        d1 = ext_tensor(a, k); d2 = ext_tensor_swapped(a, k)
        ok &= d1 == d2 and all(v > 0 for v in d1.values()) and sum(dim(l) * m for l, m in d1.items()) == comb(14, a) * comb(14, k)
print('self-checks (two orders agree, multiplicities positive, dimensions add up):', ok)
print('L^1 (x) L^1 =', dict(ext_tensor(1, 1)))
IN = {k: ext_tensor(2, k) for k in range(15)}; OUT = {l: ext_tensor(1, l) for l in range(15)}
hom = lambda x, y: sum(m * y.get(lam, 0) for lam, m in x.items())
T = [[hom(IN[k], OUT[l]) for l in range(15)] for k in range(15)]
print('\nknobs by (input degree k of A -> output degree l of A):')
print('k\\l ' + ' '.join('%2d' % l for l in range(15)))
for k in range(15): print('%3d ' % k + ' '.join('%2s' % (T[k][l] or '.') for l in range(15)))
print('\nTOTAL knobs:', sum(map(sum, T)))
Ain = Counter(); Aout = Counter()
for k in range(15): Ain += IN[k]; Aout += OUT[k]
print('distinct irreducible pieces: input %d, output %d, shared %d' % (len(Ain), len(Aout), len(set(Ain) & set(Aout))))
# gravity sector: the Riemann tensor is Weyl (2,2,0..) + traceless Ricci (2,0..) + scalar (0..)
weyl = (2, 2, 0, 0, 0, 0, 0); ric = (2, 0, 0, 0, 0, 0, 0); sc = (0,) * 7
print('\ngravity sector: copies in the output space of  Weyl: %d   traceless Ricci: %d   scalar: %d' % (Aout.get(weyl, 0), Aout.get(ric, 0), Aout.get(sc, 0)))
print('  (Ricci found in output degrees l =', [l for l in range(15) if OUT[l].get(ric)], ', scalar in l =', [l for l in range(15) if OUT[l].get(sc)], ')')
print('dimension of the invariant space [L^i (x) A]^Spin, i=1..13:', [sum(tensor(irr, W[k]).get(sc, 0) for k in range(15) for irr in irreps_ext(i)) for i in range(1, 14)])
