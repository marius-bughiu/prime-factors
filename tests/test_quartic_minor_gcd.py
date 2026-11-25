import unittest
from unittest.mock import patch

from experiments.norm_auxiliary import reduced_basis
from experiments.quartic_minor_gcd import search


class QuarticMinorGcdTests(unittest.TestCase):
    def test_dual_preserves_linear_combination(self):
        rows = [[6,2,1],[17,1,1],[13,5,2]]
        dual = [3,-2,6]
        target = [sum(value*row[i] for value,row in zip(dual,rows)) for i in range(3)]
        reduced, _ = reduced_basis(rows,dual_coordinates=dual)
        self.assertEqual(reduced,reduced_basis(rows)[0])
        self.assertEqual([sum(value*row[i] for value,row in zip(dual,reduced))
                          for i in range(3)],target)
        with self.assertRaises(ValueError):
            reduced_basis(rows,dual_coordinates=[1])

    def test_toy_occupied_window(self):
        with patch('experiments.quartic_basis_translation.integer_roots',
                   side_effect=AssertionError('unexpected root search')):
            report = search(2501,full=True,blocks=1,verify_minors=True)
        self.assertEqual(report['hits'],[dict(block=0,center=43,omitted_row=4,rank=4,
                                               normalized_minor_abs=61**2,gcd=61)])
        self.assertEqual(report['factor'],61)
        self.assertIsNone(report['unsplit_n'])
        self.assertEqual(report['work']['direct_proper_gcds'],1)
        self.assertEqual(report['work']['integer_root_nodes'],0)
        self.assertFalse(report['schedule_exhausted'])

    def test_capped_or_unproductive_schedule(self):
        for cap,visited in [(0,0),(1,1),(3,2)]:
            result = search(2503,full=True,blocks=cap)
            self.assertEqual((result['factor'],result['unsplit_n']),(None,2503))
            self.assertEqual(result['work']['normalized_minor_gcds'],5*visited)
            self.assertEqual(result['work']['direct_minors_verified'],0)
            self.assertEqual(result['schedule_exhausted'],visited==2)
        for cap in (-1,None):
            with self.assertRaises(ValueError):
                search(2501,full=True,blocks=cap)

    def test_translated_sweep_against_independent_minors(self):
        report = search(502005281288939,full=True,blocks=4827,verify_minors=True)
        self.assertTrue(report['schedule_exhausted'])
        self.assertEqual(report['hits'],[dict(block=910,center=17838859,omitted_row=4,rank=4,
                                               normalized_minor_abs=28141469**2,gcd=28141469)])
        work = report['work']
        self.assertEqual(work['normalized_minor_gcds'],24135)
        self.assertEqual(work['direct_minors_verified'],24135)
        self.assertEqual((work['unit_gcds'],work['proper_gcds'],work['direct_proper_gcds'],
                          work['whole_modulus_gcds'],work['integer_root_nodes']),(24134,1,1,0,0))
