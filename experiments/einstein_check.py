"""
Does eq. (9.3) of the GU draft reproduce the Einstein tensor when the undefined forms
are filled in with the tautological Clifford-valued forms from the literature?

  Phi_1 = sum_a e^a (x) gamma_a          Phi_2 = sum_{a,b} e^a ^ e^b (x) gamma_a gamma_b

Input xi = spin curvature of a metric: xi_{ef} = 1/4 R_{efcd} gamma^c gamma^d.
In components (Hodge duals taken, Euclidean signature, d dimensions):

  P_f = sum_a  B1(gamma_a, xi_{af})            "Ricci like"        [Phi_1 ^ *xi]
  S   = sum_ab B2(gamma_a gamma_b, xi_{ab})    "Ricci scalar like" *[Phi_2 ^ *xi]
  Q_f = B3(gamma_f, S)                         "g_mu_nu like"

Each B is either the commutator or the anticommutator. Eq. (9.3) is P - (1/2) Q up to the
normalisation of the Phi's, which the draft does not fix.
"""
import itertools, sys
import numpy as np

rng = np.random.default_rng(0)

def gammas(d):
    X = np.array([[0, 1], [1, 0]], complex); Y = np.array([[0, -1j], [1j, 0]]); Z = np.diag([1, -1]).astype(complex)
    I = np.eye(2, dtype=complex)
    g = []
    for k in range(d // 2):
        for M in (X, Y):
            mats = [Z] * k + [M] + [I] * (d // 2 - k - 1)
            out = np.array([[1]], complex)
            for m in mats: out = np.kron(out, m)
            g.append(out)
    return g

def random_riemann(d):
    """Random tensor with all algebraic symmetries of a Riemann tensor."""
    A = rng.normal(size=(d, d, d, d))
    A = A - A.transpose(1, 0, 2, 3); A = A - A.transpose(0, 1, 3, 2); A = A + A.transpose(2, 3, 0, 1)
    cyc = (A + A.transpose(0, 2, 3, 1) + A.transpose(0, 3, 1, 2)) / 3     # first Bianchi
    return A - cyc

def weyl_part(R, d):
    Ric = np.einsum('abad->bd', R); s = np.trace(Ric); g = np.eye(d)
    W = R.copy()
    for a, b, c, e in itertools.product(range(d), repeat=4):
        W[a, b, c, e] -= (g[a, c] * Ric[b, e] - g[a, e] * Ric[b, c] - g[b, c] * Ric[a, e] + g[b, e] * Ric[a, c]) / (d - 2)
        W[a, b, c, e] += s * (g[a, c] * g[b, e] - g[a, e] * g[b, c]) / ((d - 1) * (d - 2))
    return W

comm = lambda a, b: a @ b - b @ a
anti = lambda a, b: a @ b + b @ a
NAMES = {comm: 'comm', anti: 'anti'}

def pieces(R, g, B1, B2, B3):
    d = len(g)
    xi = [[sum(R[e, f, c, k] * g[c] @ g[k] for c in range(d) for k in range(d)) / 4 for f in range(d)] for e in range(d)]
    P = [sum(B1(g[a], xi[a][f]) for a in range(d)) for f in range(d)]
    S = sum(B2(g[a] @ g[b], xi[a][b]) for a in range(d) for b in range(d))
    Q = [B3(g[f], S) for f in range(d)]
    return P, S, Q

def coeff_on_gamma(M, g):
    """Return v with M = sum_d v_d gamma_d, and the residual norm."""
    n = g[0].shape[0]
    v = np.array([np.trace(M @ gd).real / n for gd in g])
    return v, np.linalg.norm(M - sum(vd * gd for vd, gd in zip(v, g)))

def run(d):
    g = gammas(d); R = random_riemann(d); W = weyl_part(R, d)
    Ric = np.einsum('abad->bd', R); s = np.trace(Ric)
    print(f"\n=== d = {d} ===")
    for B1, B2, B3 in itertools.product((comm, anti), repeat=3):
        P, S, Q = pieces(R, g, B1, B2, B3)
        Pw, Sw, Qw = pieces(W, g, B1, B2, B3)
        weyl_killed = max(np.linalg.norm(x) for x in Pw + Qw) < 1e-9
        Pv = np.array([coeff_on_gamma(P[f], g)[0] for f in range(d)]); Pres = max(coeff_on_gamma(P[f], g)[1] for f in range(d))
        Qv = np.array([coeff_on_gamma(Q[f], g)[0] for f in range(d)]); Qres = max(coeff_on_gamma(Q[f], g)[1] for f in range(d))
        p = (Pv * Ric).sum() / (Ric * Ric).sum() if Pres < 1e-9 else None
        ricci_like = Pres < 1e-9 and np.allclose(Pv, p * Ric)
        q = np.trace(Qv) / (d * s) if Qres < 1e-9 else None
        scalar_like = Qres < 1e-9 and q is not None and np.allclose(Qv, q * s * np.eye(d)) and abs(q) > 1e-12
        line = f"[{NAMES[B1]}, {NAMES[B2]}, {NAMES[B3]}]  kills Weyl: {str(weyl_killed):5}  P = {p:+.3f} Ric" if ricci_like else \
               f"[{NAMES[B1]}, {NAMES[B2]}, {NAMES[B3]}]  kills Weyl: {str(weyl_killed):5}  P not Ricci"
        if ricci_like:
            line += f"   Q = {q:+.3f} R g" if scalar_like else ("   Q = 0" if max(np.linalg.norm(x) for x in Q) < 1e-9 else "   Q not scalar")
            if scalar_like:
                line += f"   Einstein needs P - c Q with c = {p / (2 * q):+.4f}"
        print(line)

for d in (4, 6):
    run(d)

# The draft's own symmetric product on u(n) is {a, b} = i(ab + ba) (appendix, eq. 12.27).
# Redo the one Einstein-compatible choice with that product, and with Phi_2 summed over
# all ordered pairs (a, b) or over a < b only.
itw = lambda a, b: 1j * (a @ b + b @ a)
print("\n=== [comm, i-anti, i-anti]: magnitude of the coefficient Einstein needs ===")
for d in (4, 6):
    g = gammas(d); R = random_riemann(d); Ric = np.einsum('abad->bd', R); s = np.trace(Ric)
    P, S, Q = pieces(R, g, comm, itw, itw)
    Pv = np.array([coeff_on_gamma(P[f], g)[0] for f in range(d)])
    Qv = np.array([coeff_on_gamma(Q[f], g)[0] for f in range(d)])
    p = (Pv * Ric).sum() / (Ric * Ric).sum(); q = np.trace(Qv) / (d * s)
    print(f"d = {d}:  P = {p:+.3f} Ric,  Q = {q:+.3f} R g   |c| = {abs(p / (2 * q)):.4f} (all ordered pairs),  {abs(p / q):.4f} (a < b)")
