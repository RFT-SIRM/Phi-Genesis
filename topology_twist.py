"""
topology_twist.py  —  U(1) magnetic Laplacian & reverse spectral sweep on SG.

Replaces the discrete Z2 Möbius twist with a continuous U(1) gauge field.
The flux theta through every lacuna is scanned to find the topological
correction that closes the 4.49 % gap between A_theory and A_fit.
"""

import numpy as np
from scipy.sparse import lil_matrix, csr_matrix
from scipy.sparse.linalg import eigs

from mobius import _sierpinski_full, _hole_boundary_edges


def _solve_edge_phases(V, E, H, theta, twist_levels=None):
    E = [tuple(e) for e in E]
    eidx = {e: i for i, e in enumerate(E)}
    bnd = [_hole_boundary_edges(V, E, h) for h in H]

    A = np.zeros((len(H), len(E)))
    for h, edges in enumerate(bnd):
        for e in edges:
            A[h, eidx[tuple(sorted(e))]] = 1

    if twist_levels is None:
        twist_levels = set(h[3] for h in H)
    b = np.array([theta if h[3] in twist_levels else 0.0 for h in H])

    phi, *_ = np.linalg.lstsq(A, b, rcond=None)
    return phi


def magnetic_laplacian_spectrum(m, theta, twist_levels=None, k=20, tol=1e-10):
    V, E, _corners, H = _sierpinski_full(m)
    n = len(V)

    phi = _solve_edge_phases(V, E, H, theta, twist_levels)

    L = lil_matrix((n, n), dtype=complex)
    deg = np.zeros(n)

    for i, (a, b) in enumerate(E):
        w = np.exp(1j * phi[i])
        L[a, b] = -w
        L[b, a] = -np.conj(w)
        deg[a] += 1
        deg[b] += 1

    for v in range(n):
        L[v, v] = deg[v]

    vals = eigs(csr_matrix(L), k=k, which='SM', return_eigenvectors=False, tol=tol)
    return np.sort(np.real(vals))


def _get_lmin(m, theta):
    spec = magnetic_laplacian_spectrum(m, theta)
    nz = spec[spec > 1e-8]
    return nz[0] if len(nz) > 0 else spec[1]


def reverse_spectral_sweep(m=5, target_ratio=1.0449, n_theta=200):
    lambda_0 = _get_lmin(m, 0.0)
    target_lambda = lambda_0 * target_ratio

    thetas = np.linspace(0.0, 2 * np.pi, n_theta)
    best_grid = {'theta': 0.0, 'err': float('inf')}
    sweep = []

    for theta in thetas:
        lmin = _get_lmin(m, theta)
        ratio = lmin / lambda_0
        err = abs(lmin - target_lambda)
        sweep.append({
            'theta': float(theta),
            'theta_deg': float(np.degrees(theta)),
            'lambda_min': float(lmin),
            'ratio': float(ratio),
            'error': float(err),
        })
        if err < best_grid['err']:
            best_grid = {'theta': theta, 'err': err}

    lo = max(0.0, best_grid['theta'] - np.pi / n_theta)
    hi = min(2 * np.pi, best_grid['theta'] + np.pi / n_theta)

    for _ in range(30):
        mid = (lo + hi) / 2
        ratio_mid = _get_lmin(m, mid) / lambda_0
        if ratio_mid < target_ratio:
            lo = mid
        else:
            hi = mid

    theta_opt = (lo + hi) / 2
    lambda_opt = _get_lmin(m, theta_opt)
    actual_ratio = lambda_opt / lambda_0

    return {
        'theta_opt': float(theta_opt),
        'theta_deg': float(np.degrees(theta_opt)),
        'lambda_0': float(lambda_0),
        'lambda_opt': float(lambda_opt),
        'target_ratio': float(target_ratio),
        'actual_ratio': float(actual_ratio),
        'ratio_error': float(abs(actual_ratio - target_ratio)),
        'lambda_error': float(abs(lambda_opt - target_lambda)),
        'sweep': sweep,
    }


def topological_scale_correction(m=5, target_ratio=1.0449):
    result = reverse_spectral_sweep(m, target_ratio)
    return result['actual_ratio']


if __name__ == "__main__":
    import json as _json
    print("[RUNNING] Reverse spectral sweep on SG level 5 ...")
    res = reverse_spectral_sweep(m=5, target_ratio=1.0449, n_theta=200)
    print(_json.dumps({k: v for k, v in res.items() if k != 'sweep'}, indent=2))
