import unittest
from itertools import combinations

from experiments.translated_image_runs import finite_cutoffs, missing_discriminants, prime


class TranslatedImageRunTests(unittest.TestCase):
    def test_arbitrary_templates_against_character_bound(self):
        for p in (3, 5, 7, 11, 13):
            squares = {x * x % p for x in range(p)}
            for length in range(1, min(5, p)):
                scale = 1 << length
                error = (length - 2) * scale + 2
                for c in range(1, p):
                    omitted = {s for s in range(p) if (s * s - c) % p not in squares}
                    # Every translate class has a representative containing zero.
                    for other in combinations(range(1, p), length - 1):
                        template = (0,) + other
                        count = sum(all((x + j) % p in omitted for j in template)
                                    for x in range(p))
                        zeros = length if c in squares else 0
                        deficit = max(0, p + 1 - scale * (count + zeros))
                        self.assertLessEqual(deficit * deficit, p * error * error)

    def test_masks_against_weighted_image(self):
        for p in range(3, 54, 2):
            if not prime(p):
                continue
            quarter = pow(4, -1, p)
            for length in range(1, min(7, p)):
                missing = []
                for c in range(1, p):
                    image = {(u + c * quarter * pow(u, -1, p)) % p for u in range(1, p)}
                    has_run = any(all((x + j) % p not in image for j in range(length))
                                  for x in range(p))
                    if not has_run:
                        missing.append(c)
                self.assertEqual(missing_discriminants(p, length), missing)

    def test_sharp_universal_cutoffs(self):
        self.assertEqual(list(finite_cutoffs()), [
            (1, 3, None, []),
            (2, 17, 11, [9]),
            (3, 149, 41, [21, 36]),
            (4, 1279, 313, [236]),
            (5, 9923, 733, [719]),
        ])
