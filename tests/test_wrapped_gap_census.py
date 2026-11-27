import unittest

from experiments.weighted_global_trace import row_squares, schedule, trace_search
from experiments.wrapped_gap_census import PRIOR, scan


class WrappedGapCensus(unittest.TestCase):
    def test_exact_and_wrapped_alternates(self):
        for n, bits in ((91787,9), (1784821,11)):
            found, hits, _ = scan(n, bits)
            gaps, coords, _ = schedule(n, bits, 64, 2)
            for method, all_gaps in (("own_trace", False), ("global_trace", True)):
                old = trace_search(n,2,gaps,coords,all_gaps)[0]
                self.assertEqual(set(map(int,old["divisors"])), found[method] | found["precheck"])
            squares = row_squares(n,coords)[0]
            self.assertEqual(set(map(int,squares["divisors"])),found["row_square"])
            if n == 91787:
                self.assertEqual(found["sum_gcd"], {263})
                self.assertEqual(found["alternate_square"], {263})
            else:
                self.assertFalse(any(found[key] for key in PRIOR))
                self.assertEqual(found["global_trace"], {1249})
                self.assertEqual([(r["k"],r["own_gap"],r["matched_gap"]) for r in hits],[(45,4,3)])
                self.assertEqual(found["ordinary_fermat"],{1249,1429})
