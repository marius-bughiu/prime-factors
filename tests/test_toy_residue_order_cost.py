import unittest

from experiments.toy_residue_order_cost import census


class ToyResidueOrderCostTests(unittest.TestCase):
    def test_work_and_reversal_on_complete_prime_populations(self):
        rows = {row['bits']: row['groups'] for row in census()}
        self.assertEqual(rows[12]['square'], {
            'earlier': 5694,
            'tied': 4074,
            'later': 6361,
            'ascending_tests': 77334,
            'prioritized_tests': 72162,
            'priority_classifications': 199891,
        })
        self.assertEqual(rows[10]['one']['ascending_tests'], 242)
        self.assertEqual(rows[10]['one']['prioritized_tests'], 259)
