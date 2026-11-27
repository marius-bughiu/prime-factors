import unittest
from itertools import combinations
from math import gcd, isqrt

from experiments.square_anchor_slopes import family, retrospective, search, weighted_first
from scripts.factor import primes_through


class SquareAnchorSlopeTests(unittest.TestCase):
    def test_public_clipping_keeps_all_small_hits(self):
        # This independent scan has no sum bounds, parity screen or published factor inputs.
        for bits in (5, 6, 7, 8, 9):
            ps = [p for p in primes_through((1 << bits)-1) if p >= 1 << (bits-1)]
            for p, q in combinations(ps, 2):
                n = p*q
                r = isqrt(n-1)+1
                brute = []
                for b in range(1, 9):
                    for a in range(2*b, 5*b):
                        if gcd(a, b) != 1 or r % (a*b):
                            continue
                        g = r*a//b
                        self.assertEqual(r*r % g, 0)
                        total = n+1-r*r+g
                        delta = total*total-4*n
                        if total > 0 and delta >= 0 and isqrt(delta)**2 == delta:
                            x = (total-isqrt(delta))//2
                            if x > 1 and x*(total-x) == n:
                                brute.append((a, b))
                result = search(n, bits)
                self.assertEqual(bool(result["pair"]), bool(brute))
                if brute:
                    self.assertEqual(tuple(result["witness"][k] for k in ("a", "b")), brute[0])
                    self.assertEqual(result["pair"], [str(p), str(q)])

    def test_any_square_ceiling_covers_both_signs(self):
        for p, q in combinations([17, 19, 23, 29, 31], 2):
            f = (p-1)*(q-1)
            direct = [s for s in range(1, isqrt(2*f)+1)
                      if s*s > f and s*s % (s*s-f) == 0]
            self.assertEqual(retrospective(p, q)[0], direct)
        self.assertEqual(retrospective(257, 307)[0], [280, 288])

    def test_first_constructed_family_case(self):
        u, p, q = family()
        self.assertEqual(u, 1_000_022)
        self.assertEqual(16*p-9*q, 43)
        row = search(p*q, p.bit_length())
        self.assertEqual(int(row["r"]), 24*u)
        self.assertEqual(int(row["witness"]["g"]), 3*24*u)
        self.assertEqual(weighted_first(p*q)["pair"], row["pair"])


if __name__ == "__main__":
    unittest.main()
