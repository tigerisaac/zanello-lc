#!/usr/bin/env python3
"""
Direct stress test of Lemma 1 (Stanley/Zanello) of the PDF:
h-vector of every Artinian Gorenstein quotient of k[x1,x2,x3] is symmetric,
nondecreasing through floor(E/2), and (full SI) the first difference of its
first half is an O-sequence -- over F_2, F_3, F_5.

B = R/Ann(F) for a random dual form F of degree E (divided powers, contraction),
which by Macaulay duality is exactly the general Artinian Gorenstein quotient
of embedding dimension <= 3. h_t(B) = dim_k R_{E-t} o F.
"""
import random, sys
sys.path.insert(0, '.')
from verify_dual_lemmas import Field, rref, contract, mons_c, Nd, random_dual

def binom(n, k):
    if k < 0 or n < 0 or k > n: return 0
    r = 1
    for i in range(k): r = r * (n - i) // (i + 1)
    return r

def macaulay_bound(n, i):
    """n^{<i>}: max value in degree i+1 given value n in degree i (i>=1)."""
    if n == 0: return 0
    # i-binomial expansion of n
    rem, d, total = n, i, 0
    parts = []
    while rem > 0 and d >= 1:
        # largest a with C(a, d) <= rem
        a = d
        while binom(a + 1, d) <= rem: a += 1
        parts.append((a, d)); rem -= binom(a, d); d -= 1
    return sum(binom(a + 1, dd + 1) for a, dd in parts)

def hvec_gorenstein(F, E, Fdual):
    h = []
    for t in range(E + 1):
        rows = [contract(F, alpha, Fdual, E) for alpha in mons_c(E - t)]
        rk, _ = rref(F, rows)
        h.append(rk)
    return h

def main():
    random.seed(20260712)
    bad = 0; total = 0
    for p in (2, 3, 5):
        F = Field(p)
        for E in range(2, 11):
            for trial in range(30):
                sparse = None if trial % 3 == 0 else random.randint(2, 5)
                Fd = random_dual(F, E, sparse=sparse)
                if all(c == 0 for c in Fd): continue
                h = hvec_gorenstein(F, E, Fd)
                total += 1
                ok = True
                # symmetry
                if any(h[t] != h[E - t] for t in range(E + 1)):
                    ok = False; print(f'SYMMETRY FAIL p={p} E={E} h={h}')
                # nondecreasing through floor(E/2)
                half = E // 2
                if any(h[t] < h[t - 1] for t in range(1, half + 1)):
                    ok = False; print(f'NONDECREASE FAIL p={p} E={E} h={h}')
                # full SI: first difference of first half is an O-sequence
                d = [h[0]] + [h[t] - h[t - 1] for t in range(1, half + 1)]
                if any(x < 0 for x in d):
                    ok = False; print(f'DIFF-NEG FAIL p={p} E={E} h={h}')
                else:
                    for t in range(1, len(d) - 1):
                        if d[t + 1] > macaulay_bound(d[t], t):
                            ok = False
                            print(f'SI FAIL p={p} E={E} h={h} diff={d} at {t}')
                if not ok: bad += 1
    print(f'checked {total} Gorenstein h-vectors over F2/F3/F5: {bad} failures')
    sys.exit(1 if bad else 0)

if __name__ == '__main__':
    main()
