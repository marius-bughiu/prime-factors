from math import gcd
import unittest

from experiments.weighted_trace_representatives import POLICIES, evaluate


class WeightedTraceRepresentatives(unittest.TestCase):
    def test_mixed_equal_and_inverse_entries(self):
        n = 77

        def entry(y):
            return y, pow(y,-1,n), gcd(y*y-1,n)

        # In the trace-41 bucket the right entries are a repetition of 2,
        # its exact inverse 39, and the mixed orientation 72.
        values = [2,2,39,72]
        bucket = {41: [entry(y) for y in values]}
        left = [(x,41) for x in (2,39,72,46)]
        self.assertTrue(all((x+pow(x,-1,n))%n == 41 for x in (*values,46)))
        for policy in POLICIES:
            raw, *_ = evaluate(n,bucket,left,set(),policy)
            classified, calls, avoided, _, _ = evaluate(n,bucket,left,set(),policy,True)
            self.assertEqual(classified, raw)
            self.assertEqual(classified, {7,11})
            self.assertGreater(avoided['left'], 0)
            if policy != 'original':
                self.assertEqual(calls['duplicates'], 1)

    def test_exact_inverse_recovers_the_cached_factor(self):
        n, y = 77, 8
        inverse = pow(y,-1,n)
        precheck = gcd(y*y-1,n)
        self.assertEqual(precheck, 7)
        key = (y+inverse)%n
        # An empty incoming set makes the inverse branch itself return 7.
        found,calls,avoided,_,_ = evaluate(n,{key:[(y,inverse,precheck)]},
                                           [(inverse,key)],set(),'original',True)
        self.assertEqual(found,{7})
        self.assertEqual(sum(calls.values()),0)
        self.assertEqual(avoided['left'],1)
