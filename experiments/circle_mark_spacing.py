"""Finite controls for circle mark overlaps and three small gcd budgets."""

import json
from collections import Counter
from dataclasses import dataclass
from math import gcd
from pathlib import Path
from tempfile import TemporaryDirectory

from experiments.mixed_ratio_heights import jacobi
from scripts.factor import render_certificate, verify_file


FIXTURE = Path(__file__).resolve().parents[1] / "benchmarks/circle-mark-spacing.json"
CASES = ((77, 1), (7387, 4), (82919, 8))
METHODS = ("single", "scaled", "paired")


@dataclass
class Measurement:
    n: int
    limit: int
    targets: int
    hits: dict
    calls: dict
    first_success: dict
    examples: dict
    factors: tuple
    first_nonunit: int


def spacing_control(factors):
    """Directly measure all lags before comparing to algebraic predictions."""
    n = 77
    targets = (2, 3, 8)
    marks = {a: {x for x in range(n) if gcd(a - x*x, n) > 1} for a in targets}
    overlaps = {}
    for b in targets:
        overlaps[b] = [sum((x+h) % n in marks[b] for x in marks[2]) for h in range(n)]

    p, q = factors
    squares = {x*x % n for x in range(n)}
    rows = []
    for b, counts in overlaps.items():
        # This complete small square table independently labels local orientation.
        same = (2*b) % n in squares
        # The two factors are used here only to verify lags, including nonunits.
        square_side = p if jacobi(2, p) == 1 else q
        other = n // square_side
        local = [(x*x - 2) % square_side == 0 for x in range(square_side)]
        checked_unit_lags = 0
        for h, value in enumerate(counts):
            predicted = (other * sum(root and ((x+h)**2-b) % square_side == 0
                                     for x, root in enumerate(local)) if same else 4)
            if value != predicted:
                raise ArithmeticError("CRT prediction disagrees with measured overlap")
            if gcd(n, h) == 1:
                g = gcd(n, (b-2-h*h)**2 - 8*h*h)
                if same:
                    if value != (0 if g == 1 else n//g):
                        raise ArithmeticError("unit-lag resultant disagrees with census")
                elif g != 1 or value != 4:
                    raise ArithmeticError("opposite orientations failed the four-point control")
                checked_unit_lags += 1
        rows.append({"targets": [2, b], "same_square_side": same,
                     "unit_lags_checked": checked_unit_lags,
                     "overlap_by_lag_0_through_76": counts,
                     "overlap_histogram": {str(k): v for k, v in sorted(Counter(counts).items())}})
    return {"product": str(n), "mark_sets": len(targets),
            "gcd_calls_to_construct_marks": len(targets)*n,
            "rows": rows}


def measure(n, limit):
    """Measure each target and each prefix on these fixed teaching inputs."""
    if (n, limit) not in CASES:
        raise ValueError("expected one of the three declared teaching fixtures")
    d = 2*limit
    small_square, large_square = (d-1)**2, (d+1)**2
    rounds = [(h*h, (2*h-1)**2, (2*h)**2) for h in range(1, limit+1)]
    hits = {name: [0]*limit for name in METHODS}
    calls = dict.fromkeys(METHODS, 0)
    first_success = {}
    examples = {}
    target_count = 0
    factors = None
    first_nonunit = None
    for a in range(1, n):
        symbol = jacobi(a, n)
        if symbol == 0 and first_nonunit is None:
            first_nonunit = a
        if symbol != -1:
            continue
        target_count += 1
        ranks = {}
        left, right = a*small_square, a*large_square
        for name in METHODS:
            rank = None
            for h, (h2, odd2, even2) in enumerate(rounds, 1):
                if name == "single":
                    value = h2-a
                elif name == "scaled":
                    value = (h2-left)*(h2-right)
                else:
                    value = (odd2-a)*(even2-a)
                divisor = gcd(value, n)
                calls[name] += 1
                if divisor == n:
                    raise ArithmeticError("a negative-Jacobi target yielded the whole modulus")
                if divisor != 1:
                    rank = h
                    hits[name][h-1] += 1
                    pair = tuple(sorted((divisor, n//divisor)))
                    if pair[0]*pair[1] != n or (factors is not None and pair != factors):
                        raise ArithmeticError("inconsistent proper gcd across independent hits")
                    factors = pair
                    if name not in first_success:
                        first_success[name] = {"target": a, "jacobi_tests_from_1": a,
                                               "negative_targets_in_prefix": target_count,
                                               "search_gcd_calls_from_1": calls[name],
                                               "first_hit_rank": h}
                    break
            ranks[name] = rank
        for comparison in ("single", "paired"):
            ranked = {key: limit+1 if rank is None else rank for key, rank in ranks.items()}
            if ranked["scaled"] == ranked[comparison]:
                continue
            relation = "earlier" if ranked["scaled"] < ranked[comparison] else "later"
            key = f"scaled_{relation}_than_{comparison}"
            if key not in examples:
                examples[key] = {"target": a, "first_hit_rank": ranks.copy(),
                                 "gcd_calls_spent": {k: limit if r is None else r
                                                     for k, r in ranks.items()}}
    if factors is None or first_nonunit is None:
        raise ArithmeticError("the fixture did not exhibit its expected proper gcds")
    return Measurement(n, limit, target_count, hits, calls, first_success, examples,
                       factors, first_nonunit)


def verify_measurement(measured):
    """Check predictions only after gathering the divisor and the complete histograms."""
    n, limit, total = measured.n, measured.limit, measured.targets
    p, q = measured.factors
    per_square = (p+q-2)//2
    if total != (p-1)*(q-1)//2 or min(p,q) <= 2*(2*limit+1)*limit:
        raise ArithmeticError("control does not satisfy the finite coverage hypotheses")
    summaries = {}
    for name in METHODS:
        per_rank = per_square if name == "single" else 2*per_square
        hits = measured.hits[name]
        if hits != [per_rank]*limit:
            raise ArithmeticError("first-hit histogram disagrees with local root-class counts")
        successes = sum(hits)
        misses = total-successes
        expected_calls = sum(rank*count for rank, count in enumerate(hits, 1)) + misses*limit
        if measured.calls[name] != expected_calls:
            raise ArithmeticError("measured gcd budget disagrees with the stopping ranks")
        summaries[name] = {"first_hits_by_rank": hits, "successes": successes,
                           "misses": misses, "search_gcd_calls": measured.calls[name]}
    if summaries["scaled"] != summaries["paired"]:
        raise ArithmeticError("the two packed strategies had different aggregate costs")
    nonunit_divisor = gcd(measured.first_nonunit, n)
    if nonunit_divisor not in measured.factors:
        raise ArithmeticError("the first skipped nonunit did not supply a verified factor")
    return {"product": str(n), "budget": limit, "scale": 2*limit,
            "jacobi_tests_to_select_targets": n-1, "negative_jacobi_targets": total,
            "methods": summaries, "first_success_scanning_negative_targets_from_1": measured.first_success,
            "first_zero_jacobi_target": measured.first_nonunit,
            "factor_from_one_gcd_at_that_skipped_target": str(nonunit_divisor),
            "selected_first_comparisons_in_target_order": measured.examples,
            "certified_factors": [str(p), str(q)]}


def study():
    measurements = [measure(n, limit) for n, limit in CASES]
    return {"lag_census": spacing_control(measurements[0].factors),
            "gcd_budget_censuses": [verify_measurement(row) for row in measurements],
            "cost_convention": "Search gcd calls stop at the first proper gcd for each target. "
                               "Target screening, small square precomputation, mark enumeration, "
                               "independent validation and certificate time are separate. "
                               "Both packed designs multiply two differences per call. "
                               "The scaled design also computes two target-dependent products "
                               "per negative target. The target-prefix comparison continues past zero "
                               "Jacobi symbols; their gcd can already give a factor. "
                               "Equal gcd-call counts do not measure runtime."}


def main():
    observed = study()
    if observed != json.loads(FIXTURE.read_text()):
        raise SystemExit("circle mark spacing differs from the reviewed fixture")
    with TemporaryDirectory() as tmp:
        for row in observed["gcd_budget_censuses"]:
            n = int(row["product"])
            path = Path(tmp) / f"CircleMarkSpacing{n}.lean"
            path.write_text(render_certificate(n, [int(p) for p in row["certified_factors"]]))
            verify_file(path)
    print(json.dumps(observed))


if __name__ == "__main__":
    main()
