"""Count every invertible base for a fixed power-comparison search on a known prime pair."""
import argparse
import json
from collections import Counter
from math import gcd
from pathlib import Path

from experiments.offset_winner_positions import published_controls
from experiments.weighted_global_trace import schedule

ROOT = Path(__file__).resolve().parents[1]
RECORD = ROOT / "research/trace-base-population.json"
CATEGORIES = ("units", "setup", "own_after_setup", "off_after_setup", "all_after_setup",
              "extra_after_own", "off_including_setup_bases", "local_after_setup")


def cells(order, tests):
    """Partition the cyclic group using intersections of the tested subgroups."""
    divisors = {order}
    for exponent in sorted({gcd(order, value) for value in tests}):
        divisors.update(gcd(previous, exponent) for previous in tuple(divisors))
    weights = {}
    for divisor in sorted(divisors):
        count = divisor - sum(size for smaller, size in weights.items() if divisor % smaller == 0)
        if count < 0:
            raise ArithmeticError("negative cyclic group cell")
        if count:
            weights[divisor] = count
    if sum(weights.values()) != order:
        raise ArithmeticError("incomplete cyclic group partition")
    return weights


def mask_for(divisor, tests):
    return sum(1 << i for i, value in enumerate(tests) if value % divisor == 0)


def signatures(order, setup, plus, minus):
    half = order // 2
    weights = cells(order, [*setup, *plus, *minus, half])
    return [(count, half % divisor != 0, mask_for(divisor, setup),
             mask_for(divisor, plus), mask_for(divisor, minus))
            for divisor, count in weights.items()]


def parameters(n, bits, cap, per_row):
    """Keep membership in both sets when different originating rows share a query."""
    gaps, coordinates, work = schedule(n, bits, cap, per_row)
    own = {(c, s, gap) for _, _, c, s, gap in coordinates}
    off = {(c, s, d) for _, _, c, s, gap in coordinates for d in gaps if d != gap}
    return gaps, sorted(own | off), own, off, work


def tally(p, q, bits, cap, per_row):
    n = p*q
    h = n//2
    gaps, queries, own, off, work = parameters(n, bits, cap, per_row)
    setup = [(n-1)*d for d in gaps]
    plus = [abs(s-(h+1)*c-h*d) for c, s, d in queries]
    minus = [abs(s-(h+1)*c+h*d) for c, s, d in queries]
    own_mask = sum(1 << i for i, z in enumerate(queries) if z in own)
    off_mask = sum(1 << i for i, z in enumerate(queries) if z in off)
    left = signatures(p-1, setup, plus, minus)
    right = signatures(q-1, setup, plus, minus)
    totals = {"positive": Counter(), "negative": Counter()}
    for pcount, pnegative, psetup, psame, pinverse in left:
        for qcount, qnegative, qsetup, qsame, qinverse in right:
            size = pcount*qcount
            counts = totals["negative" if pnegative != qnegative else "positive"]
            counts["units"] += size
            hits = (psame & qinverse & ~qsame) | (qsame & pinverse & ~psame)
            if hits & off_mask:
                counts["off_including_setup_bases"] += size
            if psetup != qsetup:
                counts["setup"] += size
                continue
            if hits & own_mask:
                counts["own_after_setup"] += size
            elif hits:
                counts["extra_after_own"] += size
            if hits & off_mask:
                counts["off_after_setup"] += size
            if hits:
                counts["all_after_setup"] += size
            if psame != qsame or pinverse != qinverse:
                counts["local_after_setup"] += size
    return dict(left_cells=len(left), right_cells=len(right), comparisons=len(queries),
                work=work, totals={sign: {k: str(counts[k]) for k in CATEGORIES}
                                   for sign, counts in totals.items()})


def report():
    return [dict(label=label, n=str(n), factors=[str(p), str(q)], factor_bits=1024,
                 multiplier_limit=64, per_row=2, **tally(p, q, 1024, 64, 2))
            for label, n, p, q in published_controls() if label in ("fresh", "crossed")]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="compare with the committed record")
    args = parser.parse_args()
    result = json.dumps(report(), indent=2) + "\n"
    if args.check:
        if result != RECORD.read_text():
            raise SystemExit("record differs from the regenerated population counts")
    else:
        print(result, end="")
