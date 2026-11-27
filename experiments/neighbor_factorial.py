"""Compare an affine gcd batch with its exact 72-residue filter on balanced semiprimes."""

import argparse
from itertools import combinations
import json
from math import gcd, isqrt
from pathlib import Path
from tempfile import TemporaryDirectory
from time import perf_counter


ROOT = Path(__file__).resolve().parents[1]
RESIDUES = tuple(
    r for r in range(72)
    if (r % 4 == 0 and gcd(r // 4, 6) == 1)
    or (r % 3 == 0 and gcd(r // 3, 6) == 1)
)


def batch(n, terms):
    value, count = 1, 0
    for term in terms:
        value = value * term % n
        count += 1
    return gcd(value, n), count


def filtered_terms(start, stop):
    """Visit the eligible residues directly, with no test at each skipped position."""
    first_residue = start % 72
    for r in RESIDUES:
        first = start + (r - first_residue) % 72
        yield from range(first, stop, 72)


def wheel_below(x, count):
    """The same number of odd candidates coprime to three, downward from the root."""
    while count and x > 1:
        if gcd(x, 6) == 1:
            yield x
            count -= 1
        x -= 1


def first_traces(n):
    """Try the first possible parity for the known weights and odd prime factors."""
    outcomes = []
    gcds = 0
    for multiplier, parity in ((1, 0), (144, 1)):
        discriminant = 4 * multiplier * n
        trace = isqrt(discriminant - 1) + 1
        trace += (parity - trace) % 2
        gap = trace * trace - discriminant
        root = isqrt(gap)
        if root * root == gap:
            outcomes.append(str(gcd(n, trace + root)))
            gcds += 1
        else:
            outcomes.append(None)
    return outcomes, gcds


def search(n, first, last):
    """The only factor-size promise is p<q≤2p. Terms correspond to widths w=c−4."""
    started = perf_counter()
    if n <= 1 or gcd(n, 6) != 1:
        raise ValueError("the batch needs a positive odd semiprime coprime to three")
    lower = isqrt((n - 1) // 2) + 1
    if not 7 <= first <= last or 2 * last > lower:
        raise ValueError("offsets must fit between 7 and half the public lower bound on p")
    x = isqrt(n)
    start, stop = 3 * x + first, 3 * x + last + 1
    divisor, kept = batch(n, filtered_terms(start, stop))
    elapsed = perf_counter() - started
    raw, total = batch(n, range(start, stop))
    adjacent, matched = batch(n, wheel_below(x, kept))
    if divisor != raw or divisor == n or matched != kept:
        raise ArithmeticError("the supplied input did not satisfy the checked batch comparison")
    traces, trace_gcds = first_traces(n)
    if last**2 < lower and divisor > 1 and not any(d and 1 < int(d) < n for d in traces):
        raise ArithmeticError("a short affine batch escaped both first-trace controls")
    work = dict(
        offset_first=first, offset_last=last, raw_terms=total, filtered_terms=kept,
        trial_terms=matched, square_roots=2, setup_gcds=1, gcds_per_method=1,
        raw_gcd=str(raw), filtered_gcd=str(divisor), trial_gcd=str(adjacent),
        trace_controls=traces, trace_square_roots=4, trace_gcds=trace_gcds,
    )
    return (divisor if divisor > 1 else None), work, elapsed


def benchmark_case(case, proof, agree, certify_split):
    divisor, work, elapsed = search(int(case["n"]), case["first"], case["last"])
    agree(dict(id=case["id"], **case["checks"]), work, case["checks"])
    return certify_split(case, proof, divisor, elapsed, "neighbor_factorial", work)


def census(bits):
    """Complete b-bit prime pairs with 2b-bit product. Width six has c=10."""
    primes = [
        p for p in range(2 ** (bits - 1), 2**bits)
        if all(p % d for d in range(2, isqrt(p) + 1))
    ]
    counts = dict(pairs=0, unit_intervals=0, affine_splits=0, adjacent_splits=0, both=0)
    for p, q in combinations(primes, 2):
        n = p * q
        if n.bit_length() != 2 * bits:
            continue
        counts["pairs"] += 1
        x = isqrt(n)
        if batch(n, range(x, x + 9))[0] != 1:
            continue
        counts["unit_intervals"] += 1
        affine = 1 < gcd(3 * x + 10, n) < n
        adjacent = 1 < gcd(x + 9, n) < n
        counts["affine_splits"] += affine
        counts["adjacent_splits"] += adjacent
        counts["both"] += affine and adjacent
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--census", action="store_true", help="enumerate four small complete populations")
    parser.add_argument("--verify", action="store_true", help="replay fixtures and certify every split in Lean")
    args = parser.parse_args()
    if args.census:
        for bits in (6, 8, 10, 12):
            print(bits, json.dumps(census(bits)))
    if args.verify:
        from scripts.benchmark import agree, certify_split
        cases = json.loads((ROOT / "benchmarks/neighbor-factorial.json").read_text())
        with TemporaryDirectory() as location:
            for case in cases:
                proof = Path(location) / (case["id"] + ".lean")
                result = benchmark_case(case, proof, agree, certify_split)
                agree(case, result, ("factors", "remaining", "status"))
                if result["factors"] and not result["verified"]:
                    raise ArithmeticError("a prime factorization failed to verify")
                print(case["id"], result["status"], json.dumps(result["neighbor_factorial"]))
    if not args.census and not args.verify:
        parser.error("select --census or --verify")


if __name__ == "__main__":
    main()
