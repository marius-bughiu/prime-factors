import json
import unittest

from experiments.circular_coefficient_filter import check_four_samples, check_neighbours
from experiments.projective_word_moments import FIXTURE, check_case


class ModularCoefficientSamplesTests(unittest.TestCase):
    def test_earlier_term_survives_the_four_sample_average(self):
        without_term = check_four_samples(target=77, cutoff=2, degree=64)
        with_term = check_four_samples(target=77, cutoff=2, degree=65)
        self.assertEqual(with_term - without_term, 73_728)
        self.assertEqual(check_neighbours(), 24_920)

    def test_first_discrepancy_from_the_product(self):
        cases = json.loads(FIXTURE.read_text())
        results = {int(case['n']): check_case(case) for case in cases}
        example = results[77]
        self.assertEqual((example['degree'], example['predicted'], example['observed']), (6, 20, 42))
        self.assertEqual(example['boundary_divisor'], 11)
