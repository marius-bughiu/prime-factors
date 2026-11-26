from math import gcd, prod
import unittest

from experiments.separating_period import basic_moduli, least_period, search


def literal_period(n, wheel, limit, reflect):
    for m in range(wheel, limit+1, wheel):
        common = gcd(n, m)
        if 1 < common < n:
            return None, common
        if common != 1:
            continue
        squares = {x*x % m for x in range(m)}
        if n % m not in squares and (not reflect or -n % m not in squares):
            return m, None
    return None, None


class SeparatingPeriodTests(unittest.TestCase):
    def test_prime_powers_and_composite_minimum(self):
        self.assertEqual(list(basic_moduli(2**5 * 3**4 * 5)), [8, 3, 5])
        for n in range(7, 80, 2):
            for wheel in (2, 3, 4, 6, 8, 9, 15, 21):
                for reflected in (False, True):
                    counts = dict(period_gcds=0, square_tests=0)
                    self.assertEqual(least_period(n, wheel, 160, reflected, counts),
                                     literal_period(n, wheel, 160, reflected))

    def test_mask_for_the_declared_interval(self):
        for n in (17*19, 101*109, 101*113, 223*251):
            for reflected in (True, False):
                result = search(n, wheel=21, reflect=reflected)
                m = result['period']
                offsets = []
                for r in range(1, m):
                    if gcd(r, m) != 1:
                        continue
                    y = n*pow(r, -1, m) % m
                    sides = (min(r, m-r), min(y, m-y)) if reflected else (r, y)
                    self.assertNotEqual(*sides)
                    if (sides[0]<sides[1]) == result['canonical']:
                        offsets.append(r)
                if reflected:
                    self.assertEqual(set(offsets), {-r % m for r in offsets})
                entries = [x for x in range(int(result['lower']),int(result['upper'])+1)
                           if x % m in offsets]
                self.assertEqual(result['product'], str(prod(entries)%n))
                self.assertEqual(result['factor'], gcd(prod(entries),n))

    def test_short_budget_and_failed_period(self):
        rejected = search(19*31, wheel=4, period_limit=4, reflect=True)
        self.assertEqual(rejected['outcome'], 'period_limit')
        self.assertEqual(rejected['visited'], '0')
        capped = search(10007*12301, max_work=0, reflect=True)
        self.assertEqual(capped['outcome'], 'work_limit')
        self.assertEqual(capped['visited'], '0')
        self.assertFalse(capped['work'])
