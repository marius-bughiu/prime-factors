import unittest
from math import comb, isqrt

from experiments.geometric_precision_readout import interpolate, search, single_row_precision


def evaluate(poly, x):
    value = 0
    for coefficient in reversed(poly):
        value = value*x + coefficient
    return value


def local_polynomial(roots, modulus):
    poly = [1]
    for root in roots:
        poly = [((poly[i-1] if i else 0) - root*(poly[i] if i < len(poly) else 0)) % modulus
                for i in range(len(poly)+1)]
    return poly


def local_hits(p, n, base, lower, indices):
    return [i for i in indices if pow(base, i, p) == pow(base, n+1-lower, p)]


class GeometricPrecisionTests(unittest.TestCase):
    def test_crt_reconstructs_the_local_index_polynomials(self):
        cases = [(37, 43, 6, 2, False), (727, 1091, 79, 2, True),
                 (127, 241, 8, 3, False), (229, 457, 18, 4, False),
                 (241, 337, 8, 5, False)]
        for p, q, base, r, wheel in cases:
            n = p*q
            lower, last = isqrt(4*n-1)+1, isqrt(9*n//2)
            indices = list(range(last-lower+1))
            if wheel:
                # Rebuild the sum mask by multiplying pairs of residues modulo 32.
                allowed = {(a+b) % 32 for a in range(32) for b in range(32) if a*b % 32 == n % 32}
                indices = [i for i in indices if (lower+i) % 32 in allowed]
            hp, hq = (local_hits(prime, n, base, lower, indices) for prime in (p, q))
            self.assertEqual((len(hp), len(hq)), (r, r))
            if wheel:
                truth = p+q-lower
                self.assertNotEqual(hp.index(truth), hq.index(truth))
            for precision in (1, 2):
                with self.subTest(n=n, precision=precision):
                    run = search(n, base, r, precision, 512, 1, wheel=wheel)
                    u, v = p**precision, q**precision
                    left, right = local_polynomial(hp, u), local_polynomial(hq, v)
                    crt = [a+u*((b-a)*pow(u, -1, v) % v) for a, b in zip(left, right)]
                    self.assertEqual(list(map(int, run['polynomial'])), crt)
                    self.assertEqual(run['work']['scalars'], r+1)
                    self.assertEqual(run['work']['terms'], len(indices))
                    cert = run['lattice']
                    if cert is None:
                        self.assertEqual(run['outcome'], 'lattice_budget')
                        self.assertIsNone(run['factor'])
                        continue
                    roots = [i for i in range(last-lower+1) if evaluate(crt, i) % (u*v) == 0]
                    self.assertEqual(run['roots'], roots)
                    self.assertEqual(run['factor'], p)
                    self.check_row(crt, u*v, cert, roots)

    def check_row(self, poly, modulus, cert, roots):
        center, radius, power = cert['center'], cert['radius'], cert['power']
        row = list(map(int, cert['coefficients']))
        weights = list(map(int, cert['weights']))
        bound = modulus**power
        self.assertEqual(int(cert['bound']), bound)
        self.assertEqual(sum(abs(c)*radius**i for i, c in enumerate(row)), int(cert['norm']))
        self.assertLess(int(cert['norm']), bound)
        self.assertTrue(any(row))
        self.assertTrue(all(evaluate(row, root-center) == 0 for root in roots))
        # On enough distinct integers, verify membership in the lattice of the
        # centered polynomial reduced coefficientwise modulo the scalar modulus.
        shifted = [sum(c*comb(k,i)*center**(k-i) for k,c in enumerate(poly) if k>=i) % modulus
                   for i in range(len(poly))]
        degree = len(poly)-1
        self.assertEqual(len(weights), power*degree+1)
        for t in range(len(weights)):
            f = evaluate(shifted, t)
            basis = [modulus**(power-ell)*t**j*f**ell for ell in range(power) for j in range(degree)]
            basis.append(f**power)
            self.assertEqual(sum(w*b for w,b in zip(weights,basis)), evaluate(row,t))

    def test_precision_changes_the_outcome_at_fixed_lattice_power(self):
        low, high = (search(30607, 8, 3, s, 22, 1) for s in (1, 2))
        self.assertEqual((low['outcome'], low['factor']), ('lattice_budget', None))
        self.assertEqual((high['outcome'], high['factor'], high['roots']), ('polynomial_root', 127, [18]))
        self.assertEqual(high['lattice']['dimension'], 4)
        self.assertEqual(low['work']['lll_calls'], high['work']['lll_calls'])
        self.assertEqual(low['work']['scalars'], high['work']['scalars'])

    def test_auto_probe_and_exact_public_precision(self):
        for n in (9, 15, 35, 77, 143, 30607):
            for last in range(19):
                radius = max(1, last-last//2)
                for r in range(1, 7):
                    dimension = r+1
                    det_weight = radius**(r*dimension//2)
                    least = next(k for k in range(1, 128) if
                                 dimension**(2*dimension)*2**(r*dimension)*det_weight**4 < n**(4*k))
                    self.assertEqual(single_row_precision(n,last,r), least)
        run = search(30607, 8, 5, 'single_row', 22, 1, auto_multiplicity=True)
        self.assertEqual((run['multiplicity'], run['precision'], run['factor']), (3, 2, 127))
        self.assertEqual(run['probe']['terms'], 22)
        self.assertEqual(search(30607, 8, 2, None, 22, 1, auto_multiplicity=True)['outcome'],
                         'multiplicity_cap')
        mixed = search(33127, 13, 5, None, 22, 1, auto_multiplicity=True)
        self.assertEqual((mixed['outcome'], mixed['factor']), ('probe_gcd', 157))
        self.assertEqual(mixed['work']['scalars'], 0)

    def test_interpolation_over_prime_power_and_composite_rings(self):
        for modulus in (11**2, 35**2, 143**2):
            for coefficients in ((-3, 1), (2, -15, 0), (-8, 1, 3, -10, 7)):
                values = [evaluate(coefficients, z) % modulus for z in range(len(coefficients))]
                self.assertEqual(interpolate(values, modulus), [c % modulus for c in coefficients])

    def test_caps_and_incorrect_multiplicity(self):
        n = (1 << 2047) + 1
        capped = search(n, 2, 3, 2, 50, 1, wheel=True)
        self.assertEqual(capped['outcome'], 'term_limit')
        self.assertEqual(capped['work']['unvisited'], int(capped['retained']))
        self.assertEqual((capped['work']['setup_powers'], capped['work']['scalars']), (0, 0))
        for trial, reason in [(2, 'vanishing_leading'), (4, 'multiplicity_too_high')]:
            run = search(30607, 8, trial, 2, 22, 1)
            self.assertEqual((run['outcome'], run['factor']), (reason, None))
            self.assertEqual(run['work']['lll_calls'], 0)
