from collections import Counter
from math import isqrt
import unittest

from experiments.norm_residue_curves import coefficient_lattice, scan, taylor_rows


class LocalCurveTests(unittest.TestCase):
    def test_complete_residue_classes_and_opposite_signs(self):
        for total in range(3, 91, 2):
            for d in (1, 2, 3, 5, 9):
                want = []
                for y in range(1, isqrt((total-1)//d)+1):
                    x = isqrt(total-d*y*y)
                    if x*x+d*y*y == total:
                        want.append((x,y))
                for degree in (1, 2, 3):
                    with self.subTest(total=total, d=d, degree=degree):
                        self.assertCountEqual(scan(total,d,1,Counter(),1000,degree=degree),want)

    def test_taylor_expansion_and_kernel_at_lifted_points(self):
        # Cover the smooth branch of 1445=x²+y² at 5 mod 9, y=1 mod 3.
        # All points in this test are constructed independently by literal congruences.
        total, u, prime, modulus, degree = 1445, 5, 3, 9, 2
        # 1445-5²=1420 is 1 mod 3.
        order = 2*degree
        images = taylor_rows(total,1,1,u,1,prime,modulus,degree,Counter())
        kernel = coefficient_lattice(images,modulus,Counter())
        for row in kernel:
            for j in range(order):
                self.assertEqual(sum(c*im[j] for c,im in zip(row, images)) % modulus**(order-j),0)
        for j in (-9,-2,0,1,5):
            x = u+modulus*j
            precision = modulus**order
            choices = [v for v in range(1, precision, prime) if (x*x+v*v-total) % precision == 0]
            self.assertEqual(len(choices), 1)
            y, = choices
            monomials = (1,x,x*x,y,x*y)
            for value, image in zip(monomials,images):
                self.assertEqual((value-sum(c*(x-u)**i for i,c in enumerate(image))) % precision,0)
            for row in kernel:
                self.assertEqual(sum(c*v for c,v in zip(row,monomials)) % precision,0)
