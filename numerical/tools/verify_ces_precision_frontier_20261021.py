"""Exact helper functions used by the frontier checks."""
from fractions import Fraction as F

def dot(x, y):
    return sum(a*b for a, b in zip(x, y))

def mv(a, x):
    return [dot(row, x) for row in a]

def ge(c, p, q, D, b, sigma=F(1), positive=True):
    a = [[(pi+ci)/2, (pi-ci)/2] for pi, ci in zip(p, c)]
    if positive:
        assert all(x > 0 for row in a for x in row)
    R = dot(p, q)
    Q = sum(qi*ci*ci/pi for pi, qi, ci in zip(p, q, c))
    T = sigma*(R-Q)
    H = dot(c, mv(D, c))
    K = T+H
    m = dot(c, mv(D, b))
    nu = dot(b, mv(D, b))
    assert K > 0
    z = -m/K
    dq = [-x for x in mv(D, [bi+ci*z for bi, ci in zip(b, c)])]
    ell = nu-m*m/K
    assert ell == -dot(b, dq)
    dq0 = -dot(p, dq)
    totals = [sum(q[i]*a[i][j] for i in range(len(c))) for j in (0, 1)]
    for j in (0, 1):
        sign = 1 if j == 0 else -1
        da = [sigma*a[i][j]*(c[i]/p[i]-sign)*z for i in range(len(c))]
        clearing = sum(a[i][j]*dq[i]+q[i]*da[i] for i in range(len(c)))+dq0/2
        assert clearing == 0
    return dict(m=m, T=T, H=H, K=K, nu=nu, ell=ell, normalized=ell/nu,
                Q=Q, totals=totals, minimum_input=min(x for row in a for x in row))

def null_direction(rows, active):
    M = [[row[j] for j in active] for row in rows]
    pivots = []
    rank = 0
    for j in range(len(active)):
        pivot = next((i for i in range(rank, len(M)) if M[i][j]), None)
        if pivot is None:
            continue
        M[rank], M[pivot] = M[pivot], M[rank]
        z = M[rank][j]
        M[rank] = [x/z for x in M[rank]]
        for i in range(len(M)):
            if i != rank:
                z = M[i][j]
                M[i] = [x-z*y for x, y in zip(M[i], M[rank])]
        pivots.append(j)
        rank += 1
        if rank == len(M):
            break
    free = next((j for j in range(len(active)) if j not in pivots), None)
    if free is None:
        return None
    d = [F(0)]*len(active)
    d[free] = 1
    for i, j in enumerate(pivots):
        d[j] = -M[i][free]
    return d

def extreme_same_reports(c0, labels, v):
    n = len(c0)
    groups = sorted(set(labels))
    rows = [[F(labels[i] == g) for i in range(n)] for g in groups]+[v]
    c = c0[:]
    while True:
        active = [i for i in range(n) if abs(c[i]) < 1]
        dr = null_direction(rows, active)
        if dr is None:
            break
        d = [F(0)]*n
        for i, x in zip(active, dr):
            d[i] = x
        lo, hi = [], []
        for ci, di in zip(c, d):
            if di:
                x, y = sorted(((-1-ci)/di, (1-ci)/di))
                lo.append(x)
                hi.append(y)
        steps = [max(lo), min(hi)]
        ends = [[ci+t*di for ci, di in zip(c, d)] for t in steps]
        c = max(ends, key=lambda x: dot(x, x))
    assert all(dot(row, c) == dot(row, c0) for row in rows)
    assert sum(abs(x) < 1 for x in c) <= len(groups)+1
    assert dot(c, c)/n >= 1-F(len(groups)+1, n)
    return c
