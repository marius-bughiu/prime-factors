import unittest
from math import isqrt

from experiments.weighted_divisor_exclusion import search


class WeightedDivisorExclusionTests(unittest.TestCase):
    def test_every_small_integer_against_direct_division(self):
        # Includes squares, even products, unequal/nonprimitive weights and
        # windows clipped at 1 or N. Reference bounds do not use the search.
        for n in range(1,65):
            for a,b in ((1,1),(5,4),(4,5),(2,4),(9,1),(1,25)):
                center = isqrt(b*n//a)
                for radius in (0,1,4):
                    expected = [d for d in range(1,n+1) if abs(d-center)<=radius and n%d==0]
                    for modulus in (None,12):
                        result = search(n,a,b,radius,max_trace_tests=10000,modulus=modulus)
                        self.assertTrue(result['exhausted'])
                        self.assertEqual(result['divisors'],expected,(n,a,b,radius))
                        self.assertEqual(result['excluded'],not expected)
                        self.assertEqual(result['square_tests']+result['modular_rejections'],
                                         result['tested_traces'])
                        for row in result['hits']:
                            self.assertEqual(row['divisor']*row['cofactor'],n)
                            self.assertEqual(a*row['divisor']+b*row['cofactor'],row['trace'])

    def test_caps_and_oriented_roots(self):
        partial = search(15,1,1,7,max_trace_tests=1,modulus=8)
        self.assertEqual(partial['divisors'],[3,5])
        self.assertEqual((partial['tested_traces'],partial['remaining_traces']),(1,4))
        self.assertEqual((partial['status'],partial['excluded']),('partial',False))
        skipped = search(34387,3,2,6,max_trace_tests=0,modulus=23)
        self.assertEqual((skipped['status'],skipped['residue_setup_squares'],
                          skipped['divisors'],skipped['excluded']),('partial',0,[],False))
        square = search(9,1,1,0,max_trace_tests=1)
        self.assertEqual(square['hits'],[dict(trace=6,divisor=3,cofactor=3)])

    def test_empty_band_and_one_trace_examples(self):
        empty = search(3,100,1,0,max_trace_tests=0)
        self.assertEqual((empty['interval_size'],empty['total_traces'],empty['excluded']),(0,0,True))
        miss = search(34387,3,2,6,max_trace_tests=1,modulus=5)
        self.assertEqual((miss['lower'],miss['upper'],miss['modular_rejections'],
                          miss['square_tests'],miss['status']),(145,157,1,0,'excluded'))
        hit = search(34387,2,1,8,max_trace_tests=1)
        self.assertEqual(hit['hits'],[dict(trace=525,divisor=137,cofactor=251)])

    def test_invalid_parameters(self):
        for args in ((0,1,1,0), (7,0,1,0), (7,1,0,0), (7,1,1,-1)):
            with self.assertRaises(ValueError):
                search(*args,max_trace_tests=0)
        for options in (dict(max_trace_tests=-1),dict(max_trace_tests=1,modulus=1)):
            with self.assertRaises(ValueError):
                search(7,1,1,0,**options)
