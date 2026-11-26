import unittest

from experiments.shared_multiplier_selection import MENU, catalogue, run


class SelectionTests(unittest.TestCase):
    def test_geometry_and_budgets(self):
        tables = catalogue()
        for n in (1051*2011,131*251,499*463):
            for policy,labels,setup,directions in (('initial',16,23,625),('marginal',32,24,626)):
                row = run(n,tables,policy)
                self.assertIn(row['k'],MENU)
                self.assertGreaterEqual(row['positions'],row['ordinary_positions'])
                self.assertEqual(row['setup_roots'],setup)
                self.assertEqual(row['locations_priced'],directions)
                self.assertEqual(row['selected']['tests'],labels)
                for method in ('ordinary_equal','round_robin_equal','prefixed_equal'):
                    self.assertEqual(row[method]['roots'],setup+labels)
                for d in row['selected']['factors']:
                    self.assertEqual(n%d,0)


if __name__ == '__main__':
    unittest.main()
