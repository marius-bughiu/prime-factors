from itertools import combinations, product
from math import isqrt
import unittest

from experiments.farey_allocation import (
    fast, lattice_start, meeting, min_top, optimal_with_skips, slopes, verify,
)


class FareyAllocationTests(unittest.TestCase):
    def test_coverage_including_empty_cells(self):
        primes = (5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43)
        for p, q in combinations(primes, 2):
            if q > 2*p:
                continue
            for k, m in ((1, 2), (3, 1), (6, 2), (11, 3)):
                for plan in (fast(p*q, k, m), optimal_with_skips(p*q, k, m, gap=3)):
                    verify(p*q, m, plan)
                    fractions, windows, cuts, lengths = plan
                    found = False
                    for (a, b), (start, step), lo, hi, length in zip(fractions, windows, cuts, cuts[1:], lengths):
                        if lo[0]*p <= q*lo[1] and q*hi[1] <= hi[0]*p:
                            value = a*p+b*q
                            self.assertEqual((value-start) % step, 0)
                            self.assertTrue(start <= value < start+step*length)
                            found = True
                    self.assertTrue(found)

    def test_rejects_corrupt_certificates(self):
        n = 6091663632054090929
        plan = fast(n, 38, 1406)
        fractions, windows, cuts, lengths = plan
        with self.assertRaisesRegex(ValueError, 'omitted label'):
            verify(n, 1406, (fractions, windows, cuts, [0]*len(lengths)))
        with self.assertRaisesRegex(ValueError, 'interval'):
            verify(n, 1406, (fractions, windows, cuts[:-1]+[(1, 1)], lengths))
        with self.assertRaisesRegex(ValueError, 'public weighted-sum residue'):
            verify(n, 1406, (fractions, [(windows[0][0]+1, windows[0][1])]+windows[1:], cuts, lengths))

    def test_large_requests_stop_before_enumeration(self):
        with self.assertRaisesRegex(ValueError, 'center budget'):
            fast(2**2047+1, 2**200, 128)
        with self.assertRaisesRegex(ValueError, 'state budget'):
            optimal_with_skips(2**2047+1, 4, 1, max_states=32)

    def test_overlap_threshold(self):
        for n, k in ((65, 4), (77, 5), (221, 3)):
            fractions = list(slopes(k))
            for left, right in combinations(fractions, 2):
                c, d = right
                for U in range(1+isqrt(4*c*d*n), 16+isqrt(4*c*d*n)):
                    T = min_top(n, left, right, U)
                    self.assertIsNotNone(meeting(n, left, right, T, U))
                    self.assertIsNone(meeting(n, left, right, T-1, U))

    def test_optimum_against_exhaustive_chains(self):
        # Price every permitted choice independently, including the choice to omit centers.
        n, k, m = 609166363, 2, 20
        fractions = list(slopes(k))
        starts = [lattice_start(n, a, b, 24) for a, b in fractions]
        for gap in (1, 2):
            plan = optimal_with_skips(n, k, m, gap = gap)
            work = verify(n, m, plan)
            best = (work['giants'], work['retained_slopes'])
            for size in range(len(fractions)-1):
                for mids in combinations(range(1, len(fractions)-1), size):
                    ids = (0,)+mids+(len(fractions)-1,)
                    if any(j-i > gap for i, j in zip(ids, ids[1:])):
                        continue
                    for blocks in product(range(best[0]+1), repeat=len(ids)):
                        score = (sum(blocks), len(ids))
                        if score >= best:
                            continue
                        hi = [starts[i][0]+starts[i][1]*m*g for i, g in zip(ids, blocks)]
                        possible = all(meeting(n, fractions[i], fractions[j], T, U) is not None
                                       for i, j, T, U in zip(ids, ids[1:], hi, hi[1:]))
                        self.assertFalse(possible)


if __name__ == '__main__':
    unittest.main()
