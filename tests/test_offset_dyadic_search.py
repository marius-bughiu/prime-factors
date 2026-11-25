from math import gcd, isqrt
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch
import unittest

from experiments.offset_dyadic_search import compare_holdout, forward_count, search, verify_split


class DyadicOffsetTests(unittest.TestCase):
    def test_published_counts_and_normalized_square_gate(self):
        # Odd k permits dividing a true discriminant by four before working
        # modulo 2**e. At e>=2 its square class uses no extra slope digit.
        for exponent in range(2, 9):
            m = 2**exponent
            square_values = {x*x % m for x in range(m)}
            for n in range(1, m, 2):
                residues = {(x+n*pow(x, -1, m)) % m for x in range(1, m, 2)}
                expected = {2*z for z in range(m//2) if (z*z-n) % m in square_values}
                self.assertEqual(residues, expected)
                self.assertEqual(len(residues), forward_count(n, exponent))

    def test_chart_split_covers_every_proper_position(self):
        for n, total, odd_only in [(117449, 120, 168), (134683853, 1584, 2184)]:
            t = isqrt(n)
            h = n-t*t
            brute = set()
            for j in range(1, isqrt(4*h//3)+1):
                for k in range(1, t*j//h+2):
                    if gcd(j,k) > 1:
                        continue
                    delta = (j+2*t*k)**2 - 4*n*k*k
                    if delta < 0 or isqrt(delta)**2 != delta:
                        continue
                    f = gcd(n, (j+2*t*k-isqrt(delta))//2)
                    if 1 < f < n:
                        brute.add((j,k,f))
            run = search(n, total)
            hits = {(hit['j'], hit['k'], hit['factor'])
                    for chart in run['charts'].values() for hit in chart['hits']}
            self.assertEqual(hits, brute)
            self.assertEqual((run['total_tuples'], run['odd_only_tuples']), (total, odd_only))
            self.assertEqual((run['visited_tuples'], run['unchecked_tuples']), (total, 0))
            self.assertEqual(run['proper_hits'], len(hits))
            self.assertEqual(run['factor']*run['remaining'], n)

    def test_frozen_holdout_exact_work(self):
        result = compare_holdout()
        self.assertEqual(result['samples'], 8)
        for name, tuples, tests in [('odd', 84948, 7660), ('dyadic', 58258, 3815)]:
            counts = result['totals'][name]
            self.assertEqual((counts['total_tuples'], counts['visited_tuples']), (tuples, tuples))
            self.assertEqual((counts['square_tests'], counts['proper_hits'], counts['unchecked_tuples']),
                             (tests, 9, 0))

    def test_certification_accounts_for_each_split_component(self):
        with TemporaryDirectory() as temp, patch('experiments.offset_dyadic_search.verify_file') as kernel:
            directory = Path(temp)
            self.assertFalse(verify_split(13, None, 13, directory)['product_kernel_checked'])
            kernel.assert_not_called()
            for n, a, b, verified, remaining in [(4, 2, 2, ['2','2'], []), (16, 4, 4, [], ['4','4']),
                                                  (30, 2, 15, ['2'], ['15'])]:
                result = verify_split(n, a, b, directory)
                self.assertEqual(result['verified_prime_factors'], verified)
                self.assertEqual(result['uncertified_cofactors'], remaining)
                self.assertEqual(result['primes_kernel_checked'], not remaining)
                self.assertTrue(result['product_kernel_checked'])
                theorem = 'partialSplit' if remaining else 'factorization'
                self.assertEqual(kernel.call_args.kwargs['theorem_name'], 'PrimeFactors.Generated.' + theorem)
        with self.assertRaises(ValueError):
            verify_split(35, 4, 9, Path('.'))

    def test_both_charts_spend_their_own_budget(self):
        for limit in (0, 1, 5):
            result = search(117449, limit)
            self.assertEqual([c['visited_tuples'] for c in result['charts'].values()], [limit, limit])
            self.assertEqual(result['unchecked_tuples'] + 2*limit, result['total_tuples'])
        self.assertEqual(search(41**2, 0)['status'], 'square')
        self.assertEqual(search(41*2, 0)['factor'], 2)
        self.assertEqual(search(31*61, 0)['factor'], 31)
        for args in [(117449,-1,3), (117449,1,0), (117449,1,21)]:
            with self.assertRaises(ValueError):
                search(args[0], args[1], max_exponent=args[2])


if __name__ == '__main__':
    unittest.main()
