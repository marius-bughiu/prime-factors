from collections import Counter
from itertools import combinations
from math import ceil, gcd, isqrt, prod
import unittest

from experiments.rational_square_count import bounded_groups, certificate, counted_pairs, matching_lower, overlap_lower
from experiments.rational_squares import MODES, prime_parity, reconstruct, search
from experiments.smooth_sample_bound import certified_bound, prime_bins


class RationalSquareTests(unittest.TestCase):
    def test_signed_reconstruction_matches_every_box_fraction(self):
        for n in range(3, 140, 2):
            h = isqrt((n-1)//2)
            known = {}
            for a in range(1, h+1):
                if gcd(a, n) != 1:
                    continue
                for b in range(-h, h+1):
                    if gcd(b, a) != 1 or gcd(b, n) != 1:
                        continue
                    r = b*pow(a, -1, n) % n
                    self.assertNotIn(r, known)
                    known[r] = (b,a)
            for r in range(1,n):
                if gcd(r,n) != 1:
                    continue
                b,a,_ = reconstruct(n,r,h)
                if a<=h and gcd(a,n)==1:
                    self.assertEqual(known[r], (b,a))
                else:
                    self.assertNotIn(r,known)

    def test_quarter_bit_bounds_dominate_each_prime_in_its_bin(self):
        nbits = 12
        bins = prime_bins(nbits)
        primes = [p for p in range(2, 2**nbits+1) if all(p%d for d in range(2,isqrt(p)+1))]
        groups = bounded_groups(bins, nbits, 4)
        self.assertEqual(sum(groups.values()),len(primes))
        reported = sorted(w for w,m in groups.items() for _ in range(m))
        for w,p in zip(reported,primes):
            self.assertLessEqual(p**4,2**w)

    def test_lower_bounds_against_enumerated_pairs(self):
        # Two publicly specified bins with enough members to form small disjoint tuples.
        primes = [2,3,5,7,11,13,17,19,23,29,31,37,41,43]
        weights = [2]*7 + [3]*7
        cap = 6
        items = []
        for k in range(cap//min(weights)+1):
            for idx in combinations(range(len(primes)),k):
                if sum(weights[i] for i in idx)<=cap:
                    items.append((frozenset(idx),prod(primes[i] for i in idx),
                                  (sum(i<7 for i in idx),sum(i>=7 for i in idx))))
        groups = Counter(weights)
        pairs = [(a,b) for a in items for b in items if not (a[0] & b[0])]
        typed = [(a,b) for a,b in pairs if a[2]==b[2] and max(a[2])<=1]
        self.assertEqual(counted_pairs(groups,cap,5),len(typed))
        def colour(a):
            return (pow(a[1],50,101),pow(a[1],51,103))
        self.assertLessEqual(matching_lower(len(typed),5),sum(colour(a)==colour(b) for a,b in typed))
        self.assertLessEqual(overlap_lower(groups,cap),4*sum(colour(a)==colour(b) for a,b in pairs))

    def test_full_size_comparison_at_smallest_cutoff(self):
        bins = prime_bins(16)
        narrow = ceil(certified_bound(bins, 1024)[0])
        wide = ceil(certified_bound(bins, 2047)[0])
        roots = max(certificate(16))
        primes = sum(size for _, size in bins)
        centered_or_gcd = 8*2**wide + 2**1025
        self.assertEqual((primes,narrow,wide), (6542,596,1030))
        self.assertGreaterEqual(roots, 2**1093)
        self.assertGreater(roots, 2**46 * (primes+3) * centered_or_gcd)
        self.assertLessEqual(2**48 * 8 * 2**(2*narrow) * 2**803, 2**2046)

    def test_online_basis_checks_sign_and_stops_at_first_factor(self):
        self.assertEqual(prime_parity(-2*3*3,(2,3)),3)
        for mode in MODES:
            for n in (227*233, 277*281, 101*997):
                for cap in (0, 12, 128, 256):
                    batch = search(n,mode,cap,43)
                    online = search(n,mode,cap,43,online=True)
                    self.assertEqual(bool(batch['factor']), bool(online['factor']))
                    if online['factor']:
                        self.assertEqual(n % online['factor'], 0)
                        self.assertLess(1, online['factor'])
                        self.assertLess(online['factor'], n)
                    self.assertLessEqual(online['draws'], cap)
