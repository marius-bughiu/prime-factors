import unittest

from experiments.cyclotomic_small_norm import census, local_context, search


class CyclotomicSmallNorm(unittest.TestCase):
    def test_spent_work_and_failed_probes(self):
        factor, work = search(2748959, 11, 0)
        self.assertIsNone(factor)
        self.assertEqual((work['outcome'], work['setup_roots'], work['square_probes'], work['unvisited']),
                         ('test_cap', 1, 1, 1))
        self.assertEqual(search(174717, 9, 1)[1]['setup_roots'], 0)
        self.assertEqual(search(174729, 9, 1)[1]['outcome'], 'no_square')

    def test_comparison_order_and_modular_controls(self):
        for n, bits, count, before_tests, factor in ((174719, 9, 1, 1, 379),
                                                   (419899, 10, 3, 1, 599),
                                                   (2748959, 11, 3, 2, 1409)):
            actual, primary = search(n, bits, 1)
            reference, ordinary = search(n, bits, 3, square_probe=False)
            self.assertEqual((actual, reference, primary['before']), (factor, factor, count))
            self.assertEqual((ordinary['discriminant_tests'], primary['discriminant_tests']), (before_tests, 1))
            for run in (primary, ordinary):
                self.assertEqual((run['setup_roots'], run['upper_divisions']), (1, 1))
        context = local_context(2748959, 11, 4)
        self.assertEqual(context['through_11'], [3336, 3360, 3384])
        self.assertEqual(context['individual']['25'], [3360])

    def test_complete_ordered_population(self):
        report = census()
        self.assertEqual(report['first'], dict(selective=419899, full_width=2748959,
                                               fewer_discriminants=2748959))
        self.assertEqual(report['widths'][7], dict(bits=9, pairs=903, probes=218,
                                                 square_witnesses=1, selective=0, hits=[174719]))
