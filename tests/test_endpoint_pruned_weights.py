import unittest
from math import isqrt
from unittest.mock import patch

from experiments.endpoint_pruned_weights import compare, search, spans


class EndpointPruningTests(unittest.TestCase):
    def test_search_and_diagnostics_count_the_actual_roots(self):
        for n in (3758628473, 2415956311, 1195060057):
            with patch('experiments.endpoint_pruned_weights.isqrt', wraps=isqrt) as roots:
                output = search(n, 16)
                self.assertEqual(roots.call_count, 34)
            with patch('experiments.endpoint_pruned_weights.isqrt', wraps=isqrt) as roots:
                replay = compare(n, 16, True)
                self.assertEqual(roots.call_count, 51)
            self.assertEqual(output['new_found'], replay['new_found'])

    def test_post_miss_endpoint_recovers_a_pair_the_bit_width_bounds_miss(self):
        result = compare(7253249, 12, True)
        self.assertEqual(result['bit_width_only_extra'], 0)
        self.assertEqual(result['ordinary_extra'], 15)
        self.assertEqual(result['bit_width_only_found'], [])
        self.assertEqual(result['new_found'], ['2053'])

    def test_unintended_allocation_survives_endpoint_restrictions(self):
        # 35=5*7=7*5. Both allocations share the admitted trace lane here.
        p,q = 211,223
        n = p*q
        low,high = p,p
        start = 1+isqrt(4*35*n-1)
        for i,j in ((5,7), (7,5)):
            trace = i*p+j*q
            self.assertTrue(any(l<=trace<=u for l,u in spans(n,7,5,low,high,start)))
