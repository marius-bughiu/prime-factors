import unittest
from math import gcd, isqrt, log2

from experiments.gap_coverage import primes_through
from experiments.multiplier_polynomials import matched_prefixes, search, select
from experiments.polynomial_relations import local_roots_table, polynomials, sieve
from experiments.rational_squares import prime_parity


class MultiplierPolynomialsTests(unittest.TestCase):
    def test_score_against_residue_enumeration(self):
        for n in (101*103, 277*281, 139*157):
            scores = {}
            for k in range(1, 64, 2):
                if any(k % (d*d) == 0 for d in range(2, isqrt(k)+1)):
                    continue
                value = round(-500_000*log2(k))
                value += {1: 2_000_000, 3: 500_000, 5: 1_000_000, 7: 500_000}[k*n % 8]
                for p in primes_through(97)[1:]:
                    roots = sum(x*x % p == k*n % p for x in range(p))
                    weight = 1/p if roots == 1 else roots/(p-1)
                    value += round(1_000_000*weight*log2(p))
                scores[k] = value
            checked = select(n)
            self.assertEqual(checked['k'], max(scores, key=scores.get))
            self.assertEqual(checked['score'], scores[checked['k']])
            self.assertEqual(checked['work']['odd_score_terms'], len(scores)*24)
        self.assertEqual(search(7*101)['factor'], 7)

    def test_ramified_prime_and_signed_norms(self):
        # 19 is above the bound for coefficient selection. It divides the
        # multiplier only, so it cannot give a factor or a unit Hensel root.
        n, k, radius = 277*281, 19, 15
        work = dict(coefficient_prime_tests=0)
        ps = list(polynomials(n*k, 'square', 17, radius, 2, [], work, original=n))
        self.assertEqual(len(ps), 2)
        self.assertTrue(all(gcd(a, k) == 1 for a, _, _, _ in ps))
        primes = [p for p in primes_through(41) if p == k or local_roots_table(p)[k*n % p]]
        base = [(1 << (i+1), p, (0,) if p == k else local_roots_table(p)[k*n % p])
                for i, p in enumerate(primes)]
        for a, b, s, _ in ps:
            work = dict(sieve_progressions=0, sieve_marks=0, prime_divisions=0)
            actual = sieve(k*n, a, b, radius, base, work)
            expected = []
            for x in range(-radius, radius+1):
                y = ((a*x+b)**2-k*n)//a
                self.assertEqual((pow((a*x+b)*pow(s,-1,n),2,n)-y) % n, 0)
                left = abs(y)
                for p in primes:
                    while left % p == 0:
                        left //= p
                if left == 1:
                    expected.append((x, y, prime_parity(y, primes)))
            self.assertEqual(actual, expected)

    def test_shared_budget_control(self):
        n = 1009*1031
        common = dict(bound=31, radius=8, blocks=4)
        baseline = search(n, 'one', **common)
        matched = search(n, 'matched_one', **common)
        self.assertIsNone(baseline.pop('selection'))
        self.assertGreater(matched.pop('selection')['work']['candidate_scores'], 0)
        self.assertEqual(baseline, matched)
        self.assertEqual(search(n, 'extra_one', **common)['positions'], 5*17)
        self.assertEqual(search(3*101, 'three', **common)['outcome'], 'multiplier_gcd')

    def test_cost_sensitivity_keeps_first_crossing_or_reports_cap(self):
        n = 1009*1031
        common = dict(bound=31, radius=8)
        runs = {b: search(n, 'one', blocks=b, **common) for b in range(1, 9)}
        target = dict(runs[4], sieve_marks=runs[3]['sieve_marks'],
                      prime_divisions=runs[7]['prime_divisions']-1)
        for cap in (6, 8):
            matches, _ = matched_prefixes(n, target, runs[4], runs[5], max_blocks=cap, **common)
            for name, metrics in [('marks', ['sieve_marks']),
                                  ('marks_and_divisions', ['sieve_marks', 'prime_divisions'])]:
                expected = next((b for b in range(1, cap+1)
                                 if all(runs[b][m] >= target[m] for m in metrics)), None)
                self.assertEqual(matches[name]['reached_cost'], expected is not None)
                self.assertEqual(matches[name]['blocks'], expected or cap)
