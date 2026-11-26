import unittest
from unittest.mock import patch

from experiments.translated_hasse import delannoy_values, first_singular_denominator, search


def literal_middle_coefficient(n, c):
    m = (n-1)//2
    cubic = [c**3-c, 3*c*c-1, 3*c, 1]
    coefficients = [1]
    for _ in range(m):
        following = [0] * min(2*m+1, len(coefficients)+3)
        for j, value in enumerate(coefficients):
            for k, term in enumerate(cubic):
                if j+k < len(following):
                    following[j+k] = (following[j+k] + value*term) % n
        coefficients = following
    return coefficients[2*m]


class TranslatedHasseTests(unittest.TestCase):

    def test_direct_polynomial_multiplication(self):
        for n in range(3, 46, 2):
            shifts = (-2, 0, 1, 2, 3)
            _, work = search(n, shifts)
            expected = [literal_middle_coefficient(n, c) for c in shifts]
            self.assertEqual([v['residue'] for v in work['readings']], expected)
            self.assertEqual(work['terms'] * len(shifts), work['horner_updates'])
            self.assertEqual(2 * (work['terms']-1), work['exact_divisions'])

    def test_distinguishing_translation(self):
        self.assertEqual(search(187, (1,))[0], None)
        factor, work = search(187)
        self.assertEqual(factor, 11)
        self.assertEqual([r['gcd'] for r in work['readings']], [187, 11, 11])
        self.assertEqual([r['residue'] for r in work['readings']], [0, 143, 33])
        self.assertEqual(work['terms'], 47)
        self.assertEqual(work['largest_binomial_bits'], 252)

    def test_denominator_is_separate_from_coefficient(self):
        factor, work = search(77)
        self.assertIsNone(factor)
        self.assertEqual(work['outcome'], 'no_split')
        self.assertEqual([r['gcd'] for r in work['readings']], [77]*3)
        self.assertEqual(first_singular_denominator(77, 38), (7, 7))
        self.assertIsNone(first_singular_denominator(77, 6))

    def test_delannoy_exact_recurrence(self):
        values = delannoy_values(range(45))
        self.assertEqual([values[j] for j in range(6)], [1, 3, 13, 63, 321, 1683])
        for m in range(1, 45):
            n = 2*m+1
            self.assertEqual(search(n, (1,))[1]['readings'][0]['residue'], values[m] % n)

    def test_cap_precedes_construction(self):
        n = 2**2048-1
        with patch('experiments.translated_hasse.comb', side_effect=AssertionError):
            factor, work = search(n, max_index=8192)
        self.assertIsNone(factor)
        self.assertEqual(int(work['required_terms']), (n-1)//4+1)
        self.assertEqual(work['initial_binomials'], 0)
        self.assertEqual(work['terms'], 0)
        self.assertEqual(work['coefficient_gcds'], 0)
        self.assertEqual(work['readings'], [])
        self.assertEqual(work['outcome'], 'index_limit')

    def test_exact_cap_boundary_and_invalid_domain(self):
        self.assertEqual(search(187, (2,), 93)[0], 11)
        self.assertEqual(search(187, (2,), 92)[1]['outcome'], 'index_limit')
        for params in [(2, (1,), 10), (65, (), 10), (65, (1,), -1)]:
            with self.assertRaises(ValueError):
                search(*params)
