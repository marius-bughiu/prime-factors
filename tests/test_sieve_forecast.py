from collections import Counter
from math import gcd, prod
import unittest

from experiments.short_basis_sieve import shortest_lattice_vector
from experiments.sieve_forecast import coefficients, forecast, primes_through, strict_tails


class SieveForecastTests(unittest.TestCase):
    def test_period_counts_against_residues(self):
        for last in (5, 7, 11):
            start = 5
            r = forecast(40, last, start)
            selected = [p for p in primes_through(last) if p >= start]
            forbidden = {}
            for p in selected:
                squares = {x*x % p for x in range(p)}
                forbidden[p] = {a for a in range(p) if a not in squares and (a-1)%p in squares-{0}}
            counts = Counter(sum(x%p in forbidden[p] for p in selected) for x in range(r["period"]))
            for row in r["schedule"]:
                self.assertEqual(row["retained"], sum(n for j, n in counts.items() if j <= row["h"]))

    def test_elementary_symmetric_tail_against_divisors(self):
        primes, selected = [2, 3, 5, 7], {5, 7}
        m = prod(primes)
        got = strict_tails(coefficients(primes, selected,
                lambda p: ((1 if p == 2 else 2)*p*p, p-1)))
        expected = []
        for h in range(len(selected)+1):
            weighted = 0
            for d in range(1, m+1):
                if m%d or sum(d%p == 0 for p in selected) <= h:
                    continue
                phi = sum(gcd(j, d) == 1 for j in range(d))
                root_bound = 2**sum(p != 2 and (m//d)%p == 0 for p in primes)
                weighted += phi*root_bound*(m//d)**2
            expected.append(weighted)
        self.assertEqual(got, expected)

    def test_row_bounds_against_complete_lattice_enumeration(self):
        for endpoint in (5, 7, 11):
            r = forecast(40, endpoint, 3)
            m = r["m"]
            selected = [p for p in primes_through(endpoint) if p >= 3]
            for n in (10403, 150235091):
                if gcd(n, m) != 1:
                    continue
                histogram = Counter()
                for sigma in range(m):
                    if gcd(sigma, m) == 1:
                        a, b = shortest_lattice_vector(m, n*pow(sigma, -2, m)%m,
                                                       lambda pair: pair, Counter())
                        self.assertLessEqual(max(abs(a), abs(b)), r["shortest_height"])
                        histogram[sum(a%p == 0 for p in selected)] += 1
                for row in r["schedule"]:
                    actual = sum(n for j, n in histogram.items() if j > row["h"])
                    self.assertLessEqual(actual, row["row_bound"])

    def test_2048_thresholds_by_integer_comparison(self):
        result = forecast()
        m, width, rows = result["m"], result["width"], result["schedule"]
        self.assertEqual((result["prime_count"], result["selected_count"]), (62, 55))
        self.assertEqual((result["h_for_dcrit"], result["max_failures_from_height"]), (22, 31))
        self.assertEqual(rows[33]["excluded"],
                         35382592634817347590298253904362386777366977065691910019074415004208981662626909260824329463377812861640672)
        first = next(r for r in rows if r["row_bound"]*width <= m*m and r["row_bound"] <= m)
        self.assertEqual((first["h"], first["bound_source"]), (15, 83))
        self.assertGreater(rows[14]["row_bound"]*width, m*m)
