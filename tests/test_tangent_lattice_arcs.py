import json
from pathlib import Path
import unittest

from experiments.tangent_lattice_arcs import collect, full_size, split_basis, validate_small
from experiments.tangent_lattice_receipt import public_charts, split_points


ROOT = Path(__file__).resolve().parents[1]


class TangentLatticeTests(unittest.TestCase):
    def test_graph_and_vertical_branches_modulo_prime_squared(self):
        for level in (1, 2):
            classes = list(split_basis(1, 2, 1, -1, level))
            h = 3**level
            self.assertEqual(len(classes), 2*h//3)
            physical = []
            for modulus,g,r,s,step,shear,height in classes:
                self.assertEqual(modulus,h)
                self.assertEqual(step*height,h**3)
                for i in range(h//g):
                    for j in range(g):
                        physical.append(((r+step*i) % h**2,(s+shear*i+height*j) % h**2))
            expected = {(u,z) for u in range(h**2) for z in range(h**2)
                        if (z*z+2*u*u-1) % h**2 == 0}
            self.assertEqual(len(physical),len(expected))
            self.assertEqual(set(physical),expected)

    def test_coordinate_oracle_and_public_split(self):
        self.assertEqual(validate_small(),210)
        n = 2336879
        baseline, _ = collect(n,0)
        points, work = collect(n,"pair")
        self.assertEqual(points,baseline)
        factor, witnesses = split_points(n,points)
        self.assertEqual((factor,n//factor),(1871,1249))
        self.assertEqual(witnesses,[[2,1,1679,491],[2,1,1721,559]])
        self.assertEqual((work["blocks"],work["line_tests"]),(670,97))

    def test_2048_chart_bounds_and_closed_fixture(self):
        saved = json.loads((ROOT/"benchmarks/tangent-lattice-arcs.json").read_text())
        counts = {case["n"]:case for case in saved if case["mode"]=="count"}
        for result in full_size():
            n = int(result["product"])
            config = counts[str(n)]
            plan = public_charts(n)
            self.assertEqual(int(result["tangent_block_upper"]),sum(p["upper"] for p in plan))
            self.assertEqual(int(result["ordinary_blocks"]),sum(p["ordinary"] for p in plan))
            for key in ("classes","ordinary_blocks","upper_ppm","tangent_block_upper","scanned_blocks"):
                self.assertEqual(result[key],config["checks"][key])
            for row in plan:
                x,w,a,b,k = (row[key] for key in ("x","w","a","b","k"))
                self.assertLessEqual(2*a*x*x,k*n)
                self.assertLess(k*n,2*a*(x+1)**2)
                self.assertLessEqual((8*a*w**3)**2,b*n)
                self.assertLess(b*n,(8*a*(w+1)**3)**2)
            self.assertEqual(result["remaining"],[str(n)])


if __name__ == "__main__":
    unittest.main()
