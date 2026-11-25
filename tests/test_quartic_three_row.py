import unittest

from experiments.quartic_three_row import search


class QuarticThreeRowTests(unittest.TestCase):
    def test_exactly_three_short_rows_in_a_single_public_window(self):
        report = search(22663,schedule='midpoint',blocks=1)
        self.assertEqual((report['first_center'],report['radius']),(139,5))
        self.assertTrue(report['schedule_exhausted'])
        self.assertEqual(report['factor'],173)
        self.assertIsNone(report['unsplit_n'])
        expected = [([0,1,2],True,21971,173),([2,3,4],False,477495,131)]
        self.assertEqual([(h['rows'],h['all_short'],h['minor'],h['gcd']) for h in report['hits']],
                         expected)
        work = report['work']
        self.assertEqual((work['short_triples'],work['unit_gcds'],work['proper_gcds'],
                          work['four_row_gcds'],work['four_row_proper_gcds']),(1,8,2,5,0))
        self.assertEqual(work['integer_root_nodes'],0)

    def test_zero_and_nonzero_multiple_of_the_full_input(self):
        work = search(361,schedule='midpoint',blocks=1)['work']
        self.assertEqual(work['triples_tested'],10)
        self.assertEqual((work['zero_minors'],work['minor_gcds'],work['whole_n_strips']),(5,5,1))
        self.assertEqual((work['unit_gcds'],work['whole_modulus_gcds'],work['proper_gcds']),
                         (3,0,2))

    def test_empty_budget(self):
        r = search(22663,schedule='midpoint',blocks=0)
        self.assertIsNone(r['factor'])
        self.assertEqual(r['unsplit_n'],22663)
        self.assertEqual((r['unvisited_blocks'],r['visited_blocks']),(1,0))
        self.assertEqual(r['work']['lll_calls'],0)
        self.assertFalse(r['schedule_exhausted'])
        with self.assertRaises(ValueError):
            search(22663,schedule='midpoint',blocks=-1)
