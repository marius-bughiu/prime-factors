"""Test small rational divisors of the first square at or above an odd product."""
import argparse
from collections import Counter
from itertools import combinations, count
import json
from math import gcd, isqrt
from pathlib import Path
from time import perf_counter

from experiments.intermediate_totient_rows import ORIGINAL, verify
from experiments.midpoint_table_band import upper_endpoint
from experiments.shared_multiplier_prefix import divisors
from scripts.factor import fermat_split, primes_through

ROOT = Path(__file__).resolve().parents[1]
RECORD = ROOT / "research/square-anchor-slopes.json"
SLOPES = tuple((a, b) for b in range(1, 9) for a in range(2*b, 5*b) if gcd(a, b) == 1)


def search(n, bits):
    """Use only N, the common width and the fixed menu. Stop at the first split."""
    if bits < 2 or n % 2 == 0 or not 1 << (2*bits-2) <= n < 1 << (2*bits):
        raise ValueError("expected an odd potential product of two primes of the given width")
    r = isqrt(n-1)+1
    shift = r*r-n
    # A correct sum is even and lies between 2r and the folded public upper endpoint.
    g_low, g_high = 2*r+shift-1, upper_endpoint(n, bits)+shift-1
    counts = dict(setup_roots=1, slopes_visited=0, band_passes=0, divisibility_tests=0,
                  integral_divisors=0, quotient_divisions=0, parity_passes=0, discriminant_roots=0)
    pair, witness = [], None
    for a, b in SLOPES:
        counts["slopes_visited"] += 1
        scaled = r*a
        if not b*g_low <= scaled <= b*g_high:
            continue
        counts["band_passes"] += 1
        counts["divisibility_tests"] += 1
        if r % (a*b):
            continue
        counts["integral_divisors"] += 1
        counts["quotient_divisions"] += b != 1
        g = scaled if b == 1 else scaled//b
        total = g-shift+1
        if total % 2:
            continue
        counts["parity_passes"] += 1
        counts["discriminant_roots"] += 1
        delta = total*total-4*n
        gap = isqrt(delta)
        if gap*gap != delta:
            continue
        p, q = (total-gap)//2, (total+gap)//2
        if 1 < p <= q and p*q == n:
            pair = [str(p), str(q)]
            witness = dict(a=a, b=b, g=str(g), prime_sum=str(total))
            break
    return dict(pair=pair, r=str(r), shift=str(shift), slopes_available=len(SLOPES),
                counts=counts, witness=witness)


def weighted_first(n):
    """Independently test the first odd trace for multiplier 16*9."""
    target = 4*16*9*n
    s = (isqrt(target-1)+1) | 1
    gap2 = s*s-target
    gap = isqrt(gap2)
    factor = gcd(s-gap, n) if gap*gap == gap2 else None
    if factor in (1, n):
        factor = None
    return dict(odd_trace=str(s), square_tests=1, setup_roots=1, gcds=int(gap*gap == gap2),
                pair=[str(x) for x in sorted((factor, n//factor))] if factor else [])


def ordinary(n, budget):
    p, spent = fermat_split(n, budget)
    return dict(limit=budget, setup_roots=1, midpoint_roots=spent,
                pair=[str(p), str(n//p)] if p else [])


def benchmark_case(case, proof, agree, certify_split):
    """Time discovery independently from comparator replays and certificate generation."""
    n = int(case["n"])
    start = perf_counter()
    work = search(n, case["factor_bits"])
    elapsed = perf_counter()-start
    start = perf_counter()
    matched = ordinary(n, work["counts"]["discriminant_roots"])
    weighted = weighted_first(n)
    comparisons = dict(matched_ordinary=matched, first_weighted_16_9=weighted)
    if "ordinary_limit" in case:
        comparisons["extended_ordinary"] = ordinary(n, case["ordinary_limit"])
    comparison_seconds = perf_counter()-start
    work["comparisons"] = comparisons
    agree(dict(id=case["id"], **case["checks"]), work, case["checks"])
    work["comparison_seconds"] = comparison_seconds
    pair = work["pair"]
    return certify_split(case, proof, int(pair[0]) if pair else None, elapsed,
                         "square_anchor_slopes", work)


def retrospective(p, q):
    """Known-primes ceiling. Every positive g|F with F+g square supplies a valid square anchor."""
    n, f = p*q, (p-1)*(q-1)
    r = isqrt(n-1)+1
    anchors = []
    ds = divisors(f)
    for g in ds:
        s = isqrt(f+g)
        if s*s == f+g:
            anchors.append(s)
    nearest_g = r*r-f
    if (r in anchors) != (nearest_g > 0 and r*r % nearest_g == 0):
        raise AssertionError("the independent ceiling-square criterion disagrees")
    return anchors, len(ds)


def family():
    for u in count(1_000_000):
        p, q = 18*u+1, 32*u-3
        if all(all(x % d for d in range(3, isqrt(x)+1, 2)) for x in (p, q)):
            return u, p, q


def measure():
    certified = {}
    prior = json.loads(ORIGINAL.read_text())
    primes = [p for p in primes_through(511) if p >= 256]
    work, reach = Counter(), Counter(dict.fromkeys((
        "inputs", "bounded_splits", "ceiling_square_all_divisors", "any_square_all_divisors",
        "at_least_one_below_product", "at_least_one_above_product", "divisors_of_F_examined",
        "square_witnesses", "divisor_enumeration_trial_divisions", "matched_root_fermat_splits",
        "matched_root_fermat_midpoints_spent", "matched_root_fermat_overlap",
        "first_weighted_splits", "first_weighted_overlap"), 0))
    examples = {}
    for p, q in combinations(primes, 2):
        n = p*q
        row = search(n, 9)
        anchors, ds = retrospective(p, q)
        r = int(row["r"])
        bounded, ceiling, any_square = bool(row["pair"]), r in anchors, bool(anchors)
        if bounded and not ceiling:
            raise AssertionError("bounded recovery was absent from the complete ceiling-square set")
        matched = ordinary(n, row["counts"]["discriminant_roots"])
        weight = weighted_first(n)
        for test in (row, matched, weight):
            if test["pair"] and list(map(int, test["pair"])) != [p, q]:
                raise AssertionError("computed divisor disagrees with census labels")
        if any_square or matched["pair"] or weight["pair"]:
            certified[n] = [p, q]
        work.update(row["counts"])
        reach.update(inputs=1, bounded_splits=bounded, ceiling_square_all_divisors=ceiling,
                     any_square_all_divisors=any_square, divisors_of_F_examined=ds,
                     at_least_one_below_product=any(s*s < n for s in anchors),
                     at_least_one_above_product=any(s*s > n for s in anchors),
                     square_witnesses=len(anchors), divisor_enumeration_trial_divisions=isqrt((p-1)*(q-1)),
                     matched_root_fermat_splits=bool(matched["pair"]),
                     matched_root_fermat_midpoints_spent=matched["midpoint_roots"],
                     matched_root_fermat_overlap=bounded and bool(matched["pair"]),
                     first_weighted_splits=bool(weight["pair"]),
                     first_weighted_overlap=bounded and bool(weight["pair"]))
        for key, flag in (("bounded", bounded), ("ceiling_only", ceiling and not bounded),
                          ("other_square_only", any_square and not ceiling)):
            if flag and key not in examples:
                examples[key] = dict(n=str(n), factors=list(map(str, (p, q))), r=r, roots=anchors,
                                     public_witness=row["witness"])
    holdouts = []
    for block in prior["small"]:
        hits, counts = [], Counter()
        for item in block["rows"]:
            n = int(item["n"])
            row = search(n, block["factor_bits"])
            counts.update(row["counts"])
            if row["pair"]:
                hits.append(dict(n=str(n), pair=row["pair"]))
                certified[n] = list(map(int, row["pair"]))
        holdouts.append(dict(factor_bits=block["factor_bits"], inputs=len(block["rows"]),
                             splits=len(hits), hits=hits, counts=dict(counts)))
    controls = []
    for item in prior["controls"]:
        n = int(item["n"])
        controls.append(dict(id=item["id"], n=str(n), factor_bits=item["factor_bits"],
                             result=search(n, item["factor_bits"])))
    u, p, q = family()
    n = p*q
    selected = dict(u=u, n=str(n), factor_bits=p.bit_length(), result=search(n, p.bit_length()),
                    ordinary=ordinary(n, 2**21), weighted=weighted_first(n))
    if any(list(map(int, row["pair"])) != [p, q] for row in
           (selected["result"], selected["ordinary"], selected["weighted"])):
        raise AssertionError("a constructed-family comparison failed")
    certified[n] = [p, q]
    return dict(policy="By increasing b then a, test coprime 2 <= a/b < 5, b <= 8, a*b dividing ceil(sqrt(N)). Stop at the first split.",
                sources="All distinct nine-bit prime pairs and the original 64 scaled-power-menu holdouts plus both full-size controls.",
                retrospective="Nine-bit ceiling uses the true factorization to enumerate all positive divisors of F=(p-1)(q-1); anchors on both sides of N are included.",
                nine_bit=dict(counts=dict(work), comparison=dict(reach), examples=examples),
                holdouts=holdouts, controls=controls, constructed=selected), certified


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    parser.add_argument("--verify", action="store_true")
    args = parser.parse_args()
    record, pairs = measure()
    if args.write:
        RECORD.write_text(json.dumps(record, indent=2)+"\n")
    if args.check and record != json.loads(RECORD.read_text()):
        raise SystemExit("square-anchor results differ from the stored census")
    if args.verify:
        verify(pairs, "SquareAnchorPanel")
        print(f"Lean verified {len(pairs)} distinct products.")
    print(json.dumps(record["nine_bit"]["comparison"]))


if __name__ == "__main__":
    main()
