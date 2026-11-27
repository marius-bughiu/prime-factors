"""Measure fixed power transformations of uniform seeds on the two known control products."""
import argparse
import json
from fractions import Fraction
from math import gcd, lcm
from pathlib import Path

from experiments.continued_square import convergents
from experiments.offset_winner_positions import published_controls
from experiments.trace_base_population import cells, parameters

ROOT = Path(__file__).resolve().parents[1]
RECORD = ROOT / "research/powered-trace-population.json"


def image_counts(left_order, right_order, setup, winning_orders):
    """The uniform seed maps uniformly onto the product of the two images."""
    left_cells = cells(left_order, setup)
    right_cells = cells(right_order, setup)
    setup_wins = sum(lp*rq for r, lp in left_cells.items() for t, rq in right_cells.items()
                     if any((e % r == 0) != (e % t == 0) for e in setup))
    after_setup = sum(weight for r, t, weight in winning_orders
                      if left_order % r == 0 and right_order % t == 0)
    size = left_order*right_order
    if after_setup + setup_wins > size:
        raise ArithmeticError("the two phases overlap")
    return size, setup_wins, after_setup


def test_exponents(n):
    return [("unchanged", 1), ("product-minus-one", n-1), ("half-product-minus-one", (n-1)//2),
            ("lcm-through-64", lcm(*range(1, 65))), ("lcm-through-256", lcm(*range(1, 257)))]


def control(label, n, p, q):
    gaps, _, _, _, _ = parameters(n, 1024, 64, 2)
    setup = [(n-1)*d for d in gaps]
    choices = test_exponents(n)
    # These classes are supplied by the separate Lean receipt for this schedule.
    if label == "fresh":
        wins = [(7, 8, 24), (14, 8, 24)]
        choices.append(("chosen-with-known-factors", lcm((p-1)//7, (q-1)//8)))
    elif label == "crossed":
        wins = []
    else:
        raise ValueError("expected one of the two certified products")
    rows = []
    for name, e in choices:
        left_fiber, right_fiber = gcd(e, p-1), gcd(e, q-1)
        left, right = (p-1)//left_fiber, (q-1)//right_fiber
        size, first, second = image_counts(left, right, setup, wins)
        phi = (p-1)*(q-1)
        ratio = Fraction(e, phi)
        index = next((i for i, pair in enumerate(convergents(e, n), 1)
                      if pair == (ratio.numerator, ratio.denominator)), None)
        rows.append(dict(choice=name, exponent=str(e), image_sizes=[str(left), str(right)],
                         true_ratio_denominator=str(ratio.denominator), true_convergent_index=index,
                         image_size=str(size), preimages_per_element=str(left_fiber*right_fiber),
                         setup_hits=str(first), hits_after_setup=str(second),
                         setup_fraction=str(Fraction(first, size)),
                         after_setup_fraction=str(Fraction(second, size))))
    return dict(control=label, n=str(n), parameters=dict(multiplier_cap=64, positions_per_row=2),
                inputs="uniform units before applying the chosen exponent", rows=rows)


def report():
    return [control(*args) for args in published_controls()[1:]]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    data = json.dumps(report(), indent=2) + "\n"
    if args.check:
        if RECORD.read_text() != data:
            raise SystemExit("fixed-power population record differs")
    else:
        print(data, end="")
