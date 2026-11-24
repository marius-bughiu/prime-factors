"""Independent checks of the fixed-frequency decoder and the full-width replay."""
import hashlib
import json
import subprocess
import sys
import unittest
from unittest.mock import patch

from experiments import folded_square as fs
from experiments.salie_reference import cosine_bounds
from experiments.salie_seed import rounded_sum


class FoldedSquareTests(unittest.TestCase):
    def test_public_direct_sums_cover_both_signs_and_gauss_units(self):
        for p, q, branch in [(7, 11, 2), (23, 29, 2), (41, 43, 1)]:
            n = p*q
            with self.subTest(n=n):
                work = dict(unit_gcds=0, unit_inverses=0, jacobi_evaluations=0, terms=0, sums=0)
                word = rounded_sum(n, 1, n.bit_length(), n, work)
                decoded = fs.decode(n, word)
                self.assertEqual(work['terms'], (p-1)*(q-1))
                self.assertEqual(work['sums'], 1)
                self.assertEqual(decoded['factors'], [str(p), str(q)])
                self.assertEqual(decoded['multiplier'], branch)
                payload, audit = fs.produce(p, q)
                self.assertEqual(int(payload['word']), word)
                self.assertGreater(audit['raw_rounding_margin_units'], 0)
                self.assertTrue(all(b['rounding_margin_units'] > 0 for b in decoded['branches']))
                if n == 667:
                    self.assertEqual(word, 883)
                    self.assertEqual([row['quotient'] for row in decoded['branches']], [42, 63])

    def test_quarter_phase_encloses_known_rational_turns(self):
        bits = 800
        scale = 1 << bits
        for numerator, denominator in [(0, 1), (1, 4), (1, 6), (1, 1 << 310), (5, 47)]:
            with self.subTest(turn=(numerator, denominator)):
                cosine = cosine_bounds(numerator, denominator, bits)
                lo, hi = fs.first_quarter_phase(*cosine, bits)
                self.assertLessEqual(lo*denominator, numerator*scale)
                self.assertLessEqual(numerator*scale, hi*denominator)

    def test_synthetic_2048_two_process_word_replay(self):
        p, q = fs.fixture()
        producer = subprocess.run([sys.executable, fs.__file__, '--emit'], check=True,
                                  capture_output=True, text=True)
        payload = json.loads(producer.stdout)
        self.assertEqual(set(payload), {'n', 'word'})
        self.assertEqual(int(payload['n']), p*q)
        digest = hashlib.sha256(payload['word'].encode()).hexdigest()
        self.assertEqual(digest, '0fe0d2ffb73a15d4eef995e20f9e83b436b1f902d0cd050e274314351d821761')
        replay = subprocess.run([sys.executable, fs.__file__, '--decode'], input=producer.stdout,
                                check=True, capture_output=True, text=True)
        received = json.loads(replay.stdout)
        with patch.object(fs, 'fixture', side_effect=AssertionError), \
             patch.object(fs, 'produce', side_effect=AssertionError):
            self.assertEqual(fs.decode(p*q, int(payload['word'])), received)
        self.assertEqual(received['readings'], 1)
        self.assertEqual(received['bits'], 2048)
        self.assertEqual(received['factors'], [str(prime) for prime in sorted((p, q))])
        self.assertEqual(received['multiplier'], 2)
        self.assertEqual([row['rounding_margin_units'] for row in received['branches']],
                         [481036337152, 502856881119])

    def test_bounded_public_input(self):
        with self.assertRaises(ValueError):
            fs.decode((1 << 2049)-1, 0)
        with self.assertRaises(ValueError):
            fs.decode(667, -3 << 10)
