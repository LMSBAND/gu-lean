# Brute-force check in d = 4 (Euclidean): build every equivariant pairing K: (L^2 (x) A) x (L^1 (x) A) -> R
# numerically, then impose the two conditions needed for "shiab(F_A) + k*T = 0" to come from an action.
import numpy as np, itertools
d = 4
s1 = np.array([[0, 1], [1, 0]], complex); s2 = np.array([[0, -1j], [1j, 0]]); s3 = np.diag([1, -1]).astype(complex); I2 = np.eye(2, dtype=complex)
g = [np.kron(s1, I2), np.kron(s2, I2), np.kron(s3, s1), np.kron(s3, s2)]
for a in range(4):
    for b in range(4): assert np.allclose(g[a] @ g[b] + g[b] @ g[a], 2 * (a == b) * np.eye(4))
basis = []
for r in range(5):
    for I in itertools.combinations(range(4), r):
        m = np.eye(4, dtype=complex)
        for i in I: m = m @ g[i]
        basis.append(m)
dual = [np.linalg.inv(m) for m in basis]
def ad(z):   # matrix of X -> [z, X] in the Clifford basis
    return np.array([[np.trace(dual[i] @ (z @ basis[j] - basis[j] @ z)) / 4 for j in range(16)] for i in range(16)])
pairs = list(itertools.combinations(range(4), 2))
E = np.zeros((16, 6))                     # L^2 -> V (x) V
for p, (a, b) in enumerate(pairs): E[a * 4 + b, p] = 1; E[b * 4 + a, p] = -1
gens = []
for (i, j) in pairs:
    Mv = np.zeros((4, 4)); Mv[i, j] = 1; Mv[j, i] = -1
    Mvv = np.kron(Mv, np.eye(4)) + np.kron(np.eye(4), Mv)
    M2 = np.linalg.lstsq(E, Mvv @ E, rcond=None)[0]
    Ma = ad(0.5 * g[i] @ g[j]); assert np.allclose(Ma.imag, 0); Ma = Ma.real
    k = np.kron
    L = k(k(k(M2, np.eye(4)), np.eye(16)), np.eye(16)) + k(k(k(np.eye(6), Mv), np.eye(16)), np.eye(16)) \
        + k(k(k(np.eye(6), np.eye(4)), Ma), np.eye(16)) + k(k(k(np.eye(6), np.eye(4)), np.eye(16)), Ma)
    gens.append(L.astype(np.float32))
C = sum(L.T @ L for L in gens).astype(np.float64)
w, v = np.linalg.eigh(C)
B = v[:, w < 1e-6]; print('all equivariant operators (brute force):', B.shape[1])
# embed in V(x)V(x)V(x)A(x)A and impose the conditions
full = np.kron(np.kron(E, np.eye(4)), np.eye(256)) @ B            # (4,4,4,16,16) flattened
T = full.reshape(4, 4, 4, 16, 16, -1)
c1 = (T + T.transpose(0, 2, 1, 4, 3, 5)).reshape(-1, B.shape[1])   # K^{abc}(X,Y) + K^{acb}(Y,X) = 0
u, s, vt = np.linalg.svd(c1, full_matrices=False); ns = vt[s < 1e-6 * s.max()].T if (s < 1e-6 * s.max()).any() else np.zeros((B.shape[1], 0))
print('  compatible with an action to first order (C1):', ns.shape[1])
T1 = (T @ ns)
rows = []
for z in basis:                                                    # C2: invariance under every Z in the algebra
    Z = ad(z)
    rows.append((np.einsum('abcxyn,xp->abcpyn', T1, Z) + np.einsum('abcxyn,yp->abcxpn', T1, Z)).reshape(-1, ns.shape[1]))
c2 = np.concatenate(rows); s = np.linalg.svd(np.concatenate([c2.real, c2.imag]), compute_uv=False)
print('  ... and to second order as well (C1 + C2):', int((s < 1e-6 * max(s.max(), 1e-12)).sum()), ' (singular values from %.3g to %.3g)' % (s.min(), s.max()))
