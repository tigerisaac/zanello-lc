#!/usr/bin/env python3
"""
Independent numerical probe of Lemma 1 and Lemma 8 of candidate_proof.md.

Setup: R = k[x1,x2,x3], A = R/Ann(W) with W = <F1,F2> a 2-dim space of
degree-e dual forms (divided powers, contraction action -> characteristic-safe).
Every artinian level type-2 quotient of R arises this way (Macaulay duality),
and M := reindexed Matlis dual of A is the contraction module R∘W, graded by
M_d = R_d ∘ W (sitting in dual degree e-d).

Checks per example:
 [L1a] A is level of type 2: Soc(A)_t = 0 for t < e, dim Soc(A)_e = 2.
       (Via Koszul, Tor_3(A,k)_j = Soc(A)_{j-3}, so this IS the statement
        G_3 = R(-e-3)^2, i.e. both last shifts equal s = e+3.)
 [L1b] M is generated in degree 0 by exactly 2 elements:
       dim M_t - dim(R_1·M_{t-1}) = 0 for t >= 1, and = 2 at t = 0.
 [L1c] Hilbert function of M is the reverse of h(A) (the g_d = h_{e-d} dictionary).
 [L8 ] wherever the minimal relations of degree < d span a rank-one line over
       K = Frac(R): verify an equal-degree primitive v in R^2 exists, i.e.
       v = w/gcd(w1,w2) for the lowest relation w, gcd(v1,v2)=1, components of
       equal degree, and EVERY minimal relation of degree < d is an R-multiple
       of v (exact polynomial division).
 [LC ] the h-vector is log-concave (end-to-end sanity check of the Theorem).
"""
import random, sys, itertools
from fractions import Fraction

# ---------- monomial bookkeeping ----------
def mons(d):
    if d < 0: return []
    return [(i, j, d - i - j) for i in range(d + 1) for j in range(d - i + 1)]

MONS = {}
MIDX = {}
def mons_c(d):
    if d not in MONS:
        MONS[d] = mons(d)
        MIDX[d] = {m: i for i, m in enumerate(MONS[d])}
    return MONS[d]

def Nd(d):
    return (d + 1) * (d + 2) // 2 if d >= 0 else 0

# ---------- field arithmetic ----------
class Field:
    def __init__(self, p):  # p = 0 -> Q (Fraction), else F_p
        self.p = p
    def rand(self):
        if self.p: return random.randrange(self.p)
        return Fraction(random.randrange(-5, 6))
    def rand_nz(self):
        while True:
            a = self.rand()
            if a != 0: return a
    def zero(self): return Fraction(0) if self.p == 0 else 0
    def one(self):  return Fraction(1) if self.p == 0 else 1
    def add(self, a, b): return (a + b) % self.p if self.p else a + b
    def sub(self, a, b): return (a - b) % self.p if self.p else a - b
    def mul(self, a, b): return (a * b) % self.p if self.p else a * b
    def inv(self, a):    return pow(a, self.p - 2, self.p) if self.p else 1 / a

def rref(F, rows):
    """Row-reduce list of dicts/lists (dense lists) in place; return rank & basis."""
    if not rows: return 0, []
    ncol = len(rows[0])
    rows = [r[:] for r in rows]
    rank, piv = 0, []
    for c in range(ncol):
        pr = None
        for r in range(rank, len(rows)):
            if rows[r][c] != 0: pr = r; break
        if pr is None: continue
        rows[rank], rows[pr] = rows[pr], rows[rank]
        iv = F.inv(rows[rank][c])
        rows[rank] = [F.mul(iv, x) for x in rows[rank]]
        for r in range(len(rows)):
            if r != rank and rows[r][c] != 0:
                f = rows[r][c]
                rows[r] = [F.sub(rows[r][k], F.mul(f, rows[rank][k])) for k in range(ncol)]
        piv.append(c); rank += 1
        if rank == len(rows): break
    return rank, [rows[i] for i in range(rank)]

def nullspace(F, rows, ncol):
    """Nullspace basis of the matrix with given rows (each length ncol)."""
    rank, red = rref(F, rows) if rows else (0, [])
    piv = []
    for r in red:
        for c, x in enumerate(r):
            if x != 0: piv.append(c); break
    pivset = set(piv)
    basis = []
    for c in range(ncol):
        if c in pivset: continue
        v = [F.zero()] * ncol
        v[c] = F.one()
        for i, r in enumerate(red):
            if r[c] != 0:
                v[piv[i]] = F.sub(F.zero(), r[c])
        basis.append(v)
    return basis

# ---------- dual forms & contraction ----------
def contract(F, alpha, vec, e):
    """x^alpha ∘ (dual vec of degree e) -> dual vec of degree e-|alpha|."""
    t = sum(alpha); out_d = e - t
    out = [F.zero()] * Nd(out_d)
    if out_d < 0: return out
    mons_c(e)
    idx_e = MIDX[e]
    for k, beta in enumerate(mons_c(out_d)):
        gamma = (beta[0] + alpha[0], beta[1] + alpha[1], beta[2] + alpha[2])
        out[k] = vec[idx_e[gamma]]
    return out

def poly_contract(F, coeffs, t, vec, e):
    """(sum_a coeffs[a] x^a, deg t) ∘ vec."""
    out_d = e - t
    out = [F.zero()] * Nd(out_d)
    if out_d < 0: return out
    for a, ca in zip(mons_c(t), coeffs):
        if ca == 0: continue
        cv = contract(F, a, vec, e)
        out = [F.add(o, F.mul(ca, x)) for o, x in zip(out, cv)]
    return out

# ---------- polynomial helpers (dense in degree) ----------
def poly_mul_mono(F, coeffs, t, xi):
    """multiply degree-t poly (coeff list on mons(t)) by variable xi -> degree t+1."""
    out = [F.zero()] * Nd(t + 1)
    idx = MIDX[t + 1] if (t + 1) in MIDX else {m: i for i, m in enumerate(mons_c(t + 1))}
    for a, ca in zip(mons_c(t), coeffs):
        if ca == 0: continue
        b = list(a); b[xi] += 1
        out[idx[tuple(b)]] = F.add(out[idx[tuple(b)]], ca)
    return out

# ---------- main example analysis ----------
def analyze(F, e, W, label, verbose=True, sympy_check=True):
    """W = [F1coeffs, F2coeffs], degree-e dual vectors. Returns dict of results."""
    res = {'label': label, 'e': e, 'p': F.p, 'ok': True, 'msgs': []}
    def fail(msg):
        res['ok'] = False; res['msgs'].append('FAIL: ' + msg)

    # validity: W must be honestly 2-dimensional (else A is Gorenstein type 1,
    # outside the theorem's hypotheses)
    rW, _ = rref(F, [W[0][:], W[1][:]])
    if rW < 2:
        res['msgs'].append('SKIP: dim W < 2 (type-1 Gorenstein, not a test case)')
        res['ok'] = None
        return res

    # embedding dimension check: no linear form annihilates both F1,F2
    rows = []
    for i in range(3):
        alpha = tuple(1 if k == i else 0 for k in range(3))
        row = []
        for Fi in W:
            row += contract(F, alpha, Fi, e)
        rows.append(row)
    r, _ = rref(F, rows)
    if r < 3:
        res['msgs'].append('SKIP: embedding dim < 3')
        res['ok'] = None
        return res

    # g_d = dim R_d ∘ W ; also store bases of M_d (as vectors in D_{e-d})
    g = []
    Mbasis = []
    for d in range(e + 1):
        rows = []
        for Fi in W:
            for alpha in mons_c(d):
                rows.append(contract(F, alpha, Fi, e))
        rk, red = rref(F, rows)
        g.append(rk); Mbasis.append(red)
    h = g[::-1]
    res['h'] = h

    # [L1c] dictionary g_d = h_{e-d} is by construction; record h.
    # [L1b] generators of M: dim M_t - dim R_1*M_{t-1}
    gens = [g[0]]
    for t in range(1, e + 1):
        rows = []
        for i in range(3):
            alpha = tuple(1 if k == i else 0 for k in range(3))
            for b in Mbasis[t - 1]:
                rows.append(contract(F, alpha, b, e - (t - 1)))
        rk, _ = rref(F, rows)
        if rk > g[t]: fail(f'R_1 M_{t-1} bigger than M_{t}??')
        gens.append(g[t] - rk)
    if gens[0] != 2 or any(x != 0 for x in gens[1:]):
        fail(f'M generator degrees wrong: {gens}')
    res['Mgens'] = gens

    # [L1a] socle of A: Soc(A)_t = {r in R_t : r∘(x_i∘F_j)=0 all i,j}/I_t
    soc = []
    for t in range(e + 1):
        # I_t = {r : r∘F_j = 0}
        rowsI, rowsS = [], []
        for a in mons_c(t):
            rowI, rowS = [], []
            for Fj in W:
                rowI += contract(F, a, Fj, e)
                for i in range(3):
                    xi = tuple(1 if k == i else 0 for k in range(3))
                    dF = contract(F, xi, Fj, e)
                    rowS += contract(F, a, dF, e - 1)
            rowsI.append(rowI); rowsS.append(rowS)
        rkI, _ = rref(F, [r[:] for r in rowsI])
        rkS, _ = rref(F, rowsS)
        dimI = Nd(t) - rkI
        dimS = Nd(t) - rkS
        soc.append(dimS - dimI)
    if any(soc[t] != 0 for t in range(e)) or soc[e] != 2:
        fail(f'socle profile wrong (not level type 2): {soc}')
    res['soc'] = soc

    # [LC] log-concavity of h
    for i in range(1, e):
        if h[i - 1] * h[i + 1] > h[i] * h[i]:
            fail(f'LOG-CONCAVITY FAILS at i={i}: h={h}')
    # ---------- relations of M = ker(R^2 -> M) ----------
    # Z_t = ker( R_t^2 -> D_{e-t} ), (c1,c2) -> c1∘F1 + c2∘F2
    Z = {}
    for t in range(0, e + 1):
        nc = Nd(t)
        rows = []
        # build matrix with rows = images of basis vectors? we need nullspace of map,
        # so build matrix rows = coordinates of map applied to each basis vector, then
        # nullspace of TRANSPOSE... easier: matrix Mt with entry [basisvec][target] and
        # nullspace over rows-as-vectors: we need {v : v^T * Mt = 0}. Use nullspace on
        # columns: construct rows = for each basis element of R_t^2 its image vector,
        # then nullspace of the transpose. Implement via rref on transpose.
        imgs = []
        for j2 in range(2):
            for a in mons_c(t):
                mons_c(t)
                coeffs = [F.zero()] * nc
                coeffs[MIDX[t][a]] = F.one()
                imgs.append(poly_contract(F, coeffs, t, W[j2], e))
        # solve x^T * imgs = 0  <=>  imgs^T x = 0 : rows of system = columns of imgs
        ncolsys = len(imgs)
        target_dim = Nd(e - t)
        sysrows = []
        for kk in range(target_dim):
            sysrows.append([imgs[m][kk] for m in range(ncolsys)])
        Z[t] = nullspace(F, sysrows, ncolsys)
    # minimal relations per degree: Z_t / R_1 Z_{t-1}
    minrel = {}
    for t in range(1, e + 1):
        prev = []
        for z in Z.get(t - 1, []):
            c1, c2 = z[:Nd(t - 1)], z[Nd(t - 1):]
            for i in range(3):
                m1 = poly_mul_mono(F, c1, t - 1, i)
                m2 = poly_mul_mono(F, c2, t - 1, i)
                prev.append(m1 + m2)
        rkprev, redprev = rref(F, prev) if prev else (0, [])
        # minimal relations = complement of span(prev) inside span(Z_t)
        allrows = [r[:] for r in redprev] + [z[:] for z in Z[t]]
        rkall, redall = rref(F, allrows)
        p_t = rkall - rkprev
        if p_t > 0:
            # extract representatives: greedily take z in Z_t enlarging span
            reps = []
            cur = [r[:] for r in redprev]
            rk = rkprev
            for z in Z[t]:
                rk2, red2 = rref(F, cur + [z[:]])
                if rk2 > rk:
                    reps.append(z); cur = red2; rk = rk2
            minrel[t] = reps
    res['minrel_degs'] = {t: len(v) for t, v in minrel.items()}

    # ---------- [L8] rank-one line check ----------
    # for each d: relations of degree < d; if K-rank == 1, verify primitive
    import sympy
    x1, x2, x3 = sympy.symbols('x1 x2 x3')
    dom = sympy.GF(F.p) if F.p else sympy.QQ
    def to_poly(coeffs, t):
        expr = 0
        for a, ca in zip(mons_c(t), coeffs):
            if ca == 0: continue
            c = int(ca) if F.p else sympy.Rational(ca)
            expr += c * x1**a[0] * x2**a[1] * x3**a[2]
        return sympy.Poly(expr, x1, x2, x3, domain=dom) if expr != 0 else sympy.Poly(0, x1, x2, x3, domain=dom)
    checked_rank1 = 0
    rank1_profiles = []
    for d in range(2, e + 1):
        cols = []
        for t in sorted(minrel):
            if t < d:
                for z in minrel[t]:
                    cols.append((t, to_poly(z[:Nd(t)], t), to_poly(z[Nd(t):], t)))
        if not cols: continue
        # K-rank 1 test: all cross products vanish
        rank1 = True
        for (t1, f1, g1), (t2, f2, g2) in itertools.combinations(cols, 2):
            if (f1 * g2 - f2 * g1).total_degree() >= 0 and not (f1 * g2 - f2 * g1).is_zero:
                rank1 = False; break
        if not rank1 or len(cols) == 0: continue
        if sympy_check:
            checked_rank1 += 1
            rank1_profiles.append((d, len(cols)))
            t0, f0, g0 = cols[0]
            c = sympy.gcd(f0, g0) if (not f0.is_zero and not g0.is_zero) else (f0 if g0.is_zero else g0)
            if c.is_zero: fail('zero relation column?'); continue
            v1 = sympy.div(f0, c, x1, x2, x3)[0] if not f0.is_zero else sympy.Poly(0, x1, x2, x3, domain=dom)
            v2 = sympy.div(g0, c, x1, x2, x3)[0] if not g0.is_zero else sympy.Poly(0, x1, x2, x3, domain=dom)
            # primitive?
            gcd_v = sympy.gcd(v1, v2)
            if gcd_v.total_degree() != 0:
                fail(f'v not primitive at d={d}')
            # equal degrees (nonzero components)
            degs = [q.total_degree() for q in (v1, v2) if not q.is_zero]
            if len(set(degs)) > 1:
                fail(f'v components unequal degrees at d={d}: {degs}')
            # homogeneous?
            for q in (v1, v2):
                if not q.is_zero and not q.is_homogeneous:
                    fail(f'v component inhomogeneous at d={d}')
            # every column an R-multiple of v
            for (t, fc, gc) in cols:
                ref = v1 if not v1.is_zero else v2
                tgt = fc if not v1.is_zero else gc
                mu, rem = sympy.div(tgt, ref, x1, x2, x3)
                if not rem.is_zero or not (mu * v1 - fc).is_zero or not (mu * v2 - gc).is_zero:
                    fail(f'column of degree {t} not an R-multiple of v at d={d}')
    res['rank1_checked'] = checked_rank1
    res['rank1_profiles'] = rank1_profiles
    if verbose:
        status = 'OK ' if res['ok'] else ('SKIP' if res['ok'] is None else 'FAIL')
        print(f"[{status}] {label}: p={F.p} e={e} h={res.get('h')} gens={res.get('Mgens')} "
              f"soc={res.get('soc')} minrel={res.get('minrel_degs')} rank1(d,ncols)={rank1_profiles}")
        for m in res['msgs']: print('       ', m)
    return res

# ---------- example generators ----------
def random_dual(F, e, sparse=None):
    n = Nd(e)
    v = [F.zero()] * n
    if sparse:
        for i in random.sample(range(n), min(sparse, n)):
            v[i] = F.rand_nz()
    else:
        v = [F.rand() for _ in range(n)]
    return v

def engineered_rank1(F, e, a=1):
    """Try to build W with early relations forced onto the line spanned by
    v=(x1,x2): choose G in D_{e-a} with small annihilator gens, then solve
    x1∘F1 + x2∘F2 = G with F1,F2 random solutions of that linear system."""
    # random G, then solve linear system for (F1,F2)
    G = random_dual(F, e - 1)
    # unknowns: coefficients of F1,F2 (2*Nd(e)); equations: Nd(e-1)
    n = Nd(e)
    # x1∘F1: coefficient at beta (deg e-1) = F1[beta+e1]
    rowsys = []
    rhs = []
    idx_e = MIDX[e] if e in MIDX else {m: i for i, m in enumerate(mons_c(e))}
    for k, beta in enumerate(mons_c(e - 1)):
        row = [F.zero()] * (2 * n)
        b1 = (beta[0] + 1, beta[1], beta[2])
        b2 = (beta[0], beta[1] + 1, beta[2])
        row[idx_e[b1]] = F.one()
        row[n + idx_e[b2]] = F.one()
        rowsys.append(row); rhs.append(G[k])
    # particular solution: greedy — F1[beta+e1] = G[beta], F2 = 0 works!
    F1 = [F.zero()] * n; F2 = [F.zero()] * n
    for k, beta in enumerate(mons_c(e - 1)):
        b1 = (beta[0] + 1, beta[1], beta[2])
        F1[idx_e[b1]] = G[k]
    # add random homogeneous solution of x1∘H1 + x2∘H2 = 0 to keep genericity;
    # retry until W is honestly 2-dimensional
    hom = nullspace(F, rowsys, 2 * n)
    for _attempt in range(20):
        G1, G2 = F1[:], F2[:]
        for _ in range(8):
            if hom:
                z = random.choice(hom); c = F.rand()
                G1 = [F.add(G1[i], F.mul(c, z[i])) for i in range(n)]
                G2 = [F.add(G2[i], F.mul(c, z[n + i])) for i in range(n)]
        rk, _ = rref(F, [G1[:], G2[:]])
        if rk == 2:
            return [G1, G2]
    return [G1, G2]

def engineered_pure(F, e, a=1):
    """W solving x1^a∘F1 + x2^a∘F2 = Z^[e-a]. Then Ann(G)=(x1,x2,x3^{e-a+1}),
    so the relation line through v=(x1^a,x2^a) carries the two collinear
    minimal relations x1*v, x2*v of degree a+1 (non-principal J)."""
    n = Nd(e)
    exp1, exp2 = (a, 0, 0), (0, a, 0)
    mons_c(e)
    idx_e = MIDX[e]
    rowsys = []
    for beta in mons_c(e - a):
        row = [F.zero()] * (2 * n)
        b1 = (beta[0] + a, beta[1], beta[2])
        b2 = (beta[0], beta[1] + a, beta[2])
        row[idx_e[b1]] = F.one()
        row[n + idx_e[b2]] = F.one()
        rowsys.append(row)
    F1 = [F.zero()] * n; F2 = [F.zero()] * n
    F1[idx_e[(a, 0, e - a)]] = F.one()   # particular solution for G = Z^[e-a]
    hom = nullspace(F, rowsys, 2 * n)
    for _attempt in range(20):
        G1, G2 = F1[:], F2[:]
        for _ in range(8):
            if hom:
                z = random.choice(hom); c = F.rand()
                G1 = [F.add(G1[i], F.mul(c, z[i])) for i in range(n)]
                G2 = [F.add(G2[i], F.mul(c, z[n + i])) for i in range(n)]
        rk, _ = rref(F, [G1[:], G2[:]])
        if rk == 2:
            return [G1, G2]
    return [G1, G2]

def main():
    random.seed(20260711)
    results = []
    chars = [2, 3, 5, 0]
    for p in chars:
        F = Field(p)
        for e in range(3, 8):
            for trial in range(4):
                W = [random_dual(F, e), random_dual(F, e)]
                results.append(analyze(F, e, W, f'random p={p} e={e} #{trial}'))
            for trial in range(3):
                W = [random_dual(F, e, sparse=3), random_dual(F, e, sparse=3)]
                results.append(analyze(F, e, W, f'sparse p={p} e={e} #{trial}'))
            for trial in range(3):
                W = engineered_rank1(F, e)
                results.append(analyze(F, e, W, f'engineered p={p} e={e} #{trial}'))
            if e >= 5:
                for a in (1, 2):
                    for trial in range(2):
                        W = engineered_pure(F, e, a)
                        results.append(analyze(F, e, W, f'pure a={a} p={p} e={e} #{trial}'))
    nfail = sum(1 for r in results if r['ok'] is False)
    nskip = sum(1 for r in results if r['ok'] is None)
    nok = sum(1 for r in results if r['ok'] is True)
    nrank1 = sum(r.get('rank1_checked', 0) for r in results)
    print(f'\nTOTAL: {nok} ok, {nfail} fail, {nskip} skipped; '
          f'rank-one Lemma-8 configurations exercised: {nrank1}')
    if nfail: sys.exit(1)

if __name__ == '__main__':
    main()
