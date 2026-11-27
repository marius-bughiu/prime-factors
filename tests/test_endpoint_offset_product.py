import json
from math import isqrt
from pathlib import Path
import unittest
from unittest.mock import patch

from scripts.benchmark import agree
from scripts.endpoint_offset_benchmark import endpoint_offset_case, ordinary_distance, search


class EndpointOffsetTests(unittest.TestCase):
    def test_exact_number_of_square_roots(self):
        for n in (7, 37*61, 101*131):
            with patch('scripts.endpoint_offset_benchmark.isqrt', wraps=isqrt) as calls:
                factor,work = search(n)
                self.assertEqual(calls.call_count, work['search_roots'])
                self.assertEqual(calls.call_count, 1)
                if factor:
                    distance = ordinary_distance(n, factor, n//factor)
                    self.assertEqual(calls.call_count, 2)
                    self.assertEqual(distance['roots'], 1)
        self.assertEqual(search(7)[1]['root'], '0')

    def test_public_offset_readout_small(self):
        factor,work = search(37*61)
        self.assertEqual(factor,37)
        self.assertEqual((work['endpoint'],work['stride'],work['residue']), ('64',4,'81'))
        self.assertEqual(work['candidates'], ['37','61'])
        comparison = ordinary_distance(37*61,37,61)
        self.assertEqual(comparison['trace_distance'],'2')
        self.assertEqual(comparison['midpoint_distance'],'1')

    def test_unsplit_controls_do_not_compute_ordinary_diagnostics(self):
        fixture = Path(__file__).resolve().parents[1]/'benchmarks'/'endpoint-offset-product.json'
        case = next(row for row in json.loads(fixture.read_text()) if row['status']=='partial')
        with patch('scripts.endpoint_offset_benchmark.ordinary_distance') as diagnostic:
            with patch('scripts.endpoint_offset_benchmark.receipt', return_value={}):
                def capture(case, proof, factor, elapsed, key, work):
                    self.assertIsNone(factor)
                    self.assertNotIn('ordinary',work)
                    return {}
                endpoint_offset_case(case,Path('unused.lean'),agree,capture)
            diagnostic.assert_not_called()
