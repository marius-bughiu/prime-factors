"""Compare intermediate totient ratios with ordinary convergents on the same prefix LCMs."""
import argparse
from collections import Counter
from itertools import combinations
import json
from math import gcd, isqrt
from pathlib import Path

from experiments.power_denominator_census import probe
from experiments.scaled_power_menu import FERMAT_LIMIT, prefixes
from scripts.factor import fermat_split, primes_through, render_certificate, verify_file

ROOT = Path(__file__).resolve().parents[1]
RECORD = ROOT / "research/intermediate-totient-rows.json"
ORIGINAL = ROOT / "research/scaled-power-menu.json"


def product_band(n, bits):
    """Inclusive lower and exclusive upper deficit for two odd factors of the advertised width."""
    lower_factor, upper_factor = 1 << (bits-1), (1 << bits)-1
    min_sum = 2*(isqrt(n-1)+1)
    max_sum = min(lower_factor+n//lower_factor, upper_factor+n//upper_factor)
    return max(2*lower_factor+1, min_sum-1), min(4*lower_factor, max_sum-(max_sum % 2))


def readout(n, exponent, a, b):
    """Return a proper divisor, charging an integer square root only for a nonnegative discriminant."""
    total = n-(exponent//a)*b+1
    discriminant = total*total-4*n
    if discriminant < 0:
        return None, False
    distance = isqrt(discriminant)
    divisor = (total-distance)//2
    if distance*distance == discriminant and 1 < divisor < n and divisor*(total-divisor) == n:
        return divisor, True
    return None, True


def scan(n, bits, exponent, *, band=None, compare_raw=False, price_full=True):
    """Walk quotient blocks up to the strict lower-width cutoff. Optionally replay all positive indices."""
    if not 1 <= exponent <= n or bits < 2:
        raise ValueError("expected a positive exponent at most N and a common prime width")
    low, high = (1 << bits, 2 << bits) if band is None else band
    if not (0 < low and high <= 2*low):
        raise ValueError("a single block requires a positive lower endpoint and high <= 2*low")
    if low >= high:
        return Counter(), {}
    # A subset of the dyadic window can only occur in that window's one eligible block.
    # Keep its earlier stopping point even when the new upper endpoint is much smaller.
    dyadic_low = 1 << bits
    locator_high = 2*dyadic_low if dyadic_low <= low and high <= 2*dyadic_low else high
    a0, b0, a1, b1 = 0, 1, 1, 0
    u, v = exponent, n
    counts = Counter()
    found = {}
    stopped = False
    previous_stopped = False
    while v:
        quotient, remainder = divmod(u, v)
        counts["full_blocks"] += 1
        counts["full_raw_indices"] += quotient
        upper = counts["full_blocks"] % 2 == 0
        next_a, next_b = a0+quotient*a1, b0+quotient*b1
        if price_full and not previous_stopped:
            counts["previous_visited_blocks"] += 1
            if upper:
                counts["previous_endpoint_divisions"] += 2
                if remainder < low*next_a:
                    previous_stopped = True
        selected = range(0)
        if not stopped:
            counts["visited_blocks"] += 1
            if upper and remainder < locator_high*next_a:
                # All earlier upper blocks are above the band. Every later upper intermediate
                # has at least twice this endpoint numerator and no larger cross error.
                stopped = True
                counts["early_stops"] += 1
                overlaps = True
                if band is not None:
                    # D(t) decreases across this block. Its endpoint must lie below the new
                    # ceiling, and its first row must reach the new floor.
                    counts["block_edge_checks"] += 1
                    overlaps = remainder < high*next_a
                    if overlaps:
                        counts["block_edge_checks"] += 1
                        overlaps = u-v >= low*(a0+a1)
                if overlaps:
                    counts["blocks_clipped"] += 1
                    counts["endpoint_divisions"] += 2
                    lo = 1+max(0, u-high*a0)//(v+high*a1)
                    hi = min(quotient, max(0, u-low*a0)//(v+low*a1))
                    selected = range(lo, hi+1)
                    counts["width_indices"] += max(0, hi-lo+1)
                    if a1 == 0:
                        counts["first_block_indices"] += max(0, hi-lo+1)
                    for t in selected:
                        a, b = a0+t*a1, b0+t*b1
                        if exponent % a:
                            continue
                        counts["integer_candidates"] += 1
                        p, tested = readout(n, exponent, a, b)
                        counts["discriminant_roots"] += tested
                        if p:
                            categories = []
                            if t == quotient:
                                categories.append("ordinary")
                            if a1 == 0:
                                categories.append("first_block")
                            elif t < quotient:
                                categories.append("later_intermediate")
                            for category in categories:
                                found.setdefault(category, dict(factor=str(p), exponent=str(exponent), t=t,
                                    quotient=quotient, first=lo, last=hi, a=str(a), b=str(b),
                                    previous=[str(a0), str(b0)], lower=[str(a1), str(b1)]))
        if compare_raw:
            brute = []
            for t in range(1, quotient+1):
                a, b = a0+t*a1, b0+t*b1
                if a and low*a <= n*a-exponent*b < high*a:
                    brute.append(t)
            if brute != list(selected):
                raise ArithmeticError("clipped indices differ from the complete intermediate walk")
        a0, a1 = a1, next_a
        b0, b1 = b1, next_b
        if stopped and not compare_raw and not price_full:
            break
        u, v = v, remainder
    return counts, found


def search(n, bits, *, sharp=True, compare_raw=False, price_full=True):
    """The search inputs are N and the common prime width. All exponents are public."""
    if n < 3 or n % 2 == 0 or bits < 2:
        raise ValueError("expected an odd product and a common prime width of at least two")
    counts, found = Counter(dict.fromkeys(("blocks_clipped", "discriminant_roots", "early_stops",
        "endpoint_divisions", "exponents", "first_block_indices", "integer_candidates", "width_indices",
        "matched_midpoint_setup_roots", "matched_midpoints_spent", "matched_total_setup_roots",
        "matched_total_midpoints_spent"), 0)), {}
    band = product_band(n, bits) if sharp else None
    if sharp:
        counts["block_edge_checks"] = 0
        counts["band_setup_roots"] = 1
        counts["band_setup_divisions"] = 2
    residue = 2 % n
    for index, exponent, ratio in prefixes(n):
        residue = pow(residue, ratio, n)
        counts["power_updates"] += 1
        if (exponent+1)**2 < 4*n:
            continue
        counts["exponents"] += 1
        gcd_value = gcd(residue-1, n)
        if 1 < gcd_value < n:
            found.setdefault("gcd", dict(factor=str(gcd_value), prefix_index=index))
        counts["proper_gcds"] += 1 < gcd_value < n
        counts["whole_product_gcds"] += gcd_value == n
        work, rows = scan(n, bits, exponent, band=band, compare_raw=compare_raw, price_full=price_full)
        counts.update(work)
        for name, row in rows.items():
            found.setdefault(name, dict(prefix_index=index, **row))
        ordinary = probe(n, exponent, factor_bits=bits, early_stop=True)
        counts["ordinary_gates_passed"] += ordinary["passed"]
        counts["ordinary_visits"] += ordinary["convergents"]
        counts["ordinary_roots"] += ordinary["square_tests"]
        canonical = bool(ordinary["pair"])
        if canonical and sharp:
            canonical = band[0] <= sum(map(int, ordinary["pair"]))-1 < band[1]
        if canonical != ("ordinary" in rows):
            raise ArithmeticError("the canonical endpoint disagrees with the independent ordinary scan")
    p, spent = fermat_split(n, FERMAT_LIMIT)
    counts["fermat_midpoints"] = spent
    if p:
        found["fermat"] = dict(factor=str(p))
    counts["fermat_setup_roots"] = 1
    budget = counts["discriminant_roots"]
    # Independently priced Fermat baselines share their prefix when computing the benchmark.
    # The exact total-root comparison allows one extra trial when the sharp band paid a setup root.
    if budget or sharp:
        p, spent = fermat_split(n, budget)
        if budget:
            counts["matched_midpoint_setup_roots"] = 1
            counts["matched_midpoints_spent"] = spent
            if p:
                found["matched_midpoints"] = dict(factor=str(p))
        total_midpoints = max(0, budget+int(sharp)-1)
        counts["matched_total_setup_roots"] = 1
        counts["matched_total_midpoints_spent"] = min(spent, total_midpoints)
        if p and spent <= total_midpoints:
            found["matched_total_roots"] = dict(factor=str(p))
        if sharp:
            counts["matched_without_setup_initial_roots"] = int(budget > 0)
            counts["matched_without_setup_midpoints"] = min(spent, max(0, budget-1))
            if p and spent < budget:
                found["matched_without_setup"] = dict(factor=str(p))
    counts["inputs"] = 1
    return counts, found, band


def run_fixture(case):
    """Record primary factors from the intermediate walk and disclose separate baseline costs."""
    n = int(case["n"])
    counts, found, band = search(n, case["factor_bits"], price_full=False)
    # The native timed search does not walk the omitted tail to price the raw reference.
    counts.pop("full_raw_indices", None)
    counts.pop("full_blocks", None)
    primary = next((found[name] for name in ("later_intermediate", "ordinary", "first_block") if name in found), None)
    p = int(primary["factor"]) if primary else None
    pair = [str(v) for v in sorted((p, n//p))] if p else []
    return dict(deficit_lower=str(band[0]), deficit_upper_exclusive=str(band[1]),
                counts=dict(sorted(counts.items())), hits=found, pair=pair)


def summarize(cases, *, raw=False, sharp=True):
    counts, splits = Counter(), Counter(dict.fromkeys(("ordinary", "first_block", "later_intermediate",
        "gcd", "fermat", "matched_midpoints", "matched_total_roots"), 0))
    if sharp:
        splits["matched_without_setup"] = 0
    examples, successes, primary_hits = {}, {}, {}
    for n, bits in cases:
        work, found, _ = search(n, bits, compare_raw=raw, sharp=sharp)
        counts.update(work)
        for method in found:
            splits[method] += 1
        primary_hits[n] = {name: (found[name]["factor"], found[name]["exponent"], found[name]["t"])
                           for name in ("ordinary", "later_intermediate", "first_block") if name in found}
        intermediate = bool(primary_hits[n])
        gain = intermediate and "ordinary" not in found
        splits["intermediate_union"] += intermediate
        splits["gain_over_ordinary"] += gain
        splits["gain_over_ordinary_and_first_block"] += gain and "first_block" not in found
        splits["gain_over_ordinary_first_block_and_gcd"] += gain and not ({"first_block", "gcd"} & found.keys())
        splits["gain_over_ordinary_gcd_and_fermat"] += gain and not ({"gcd", "fermat"} & found.keys())
        for name in (("matched_total_roots", "matched_midpoints", "matched_without_setup")
                     if sharp else ("matched_total_roots", "matched_midpoints")):
            baseline = name in found
            splits["intermediate_and_"+name] += intermediate and baseline
            splits["intermediate_only_vs_"+name] += intermediate and not baseline
            splits[name+"_only_vs_intermediate"] += baseline and not intermediate
        if gain and "later_intermediate" in found:
            labels = ["first_gain"]
            if "gcd" not in found and "first_block" not in found:
                labels.append("first_gain_beyond_gcd")
            for label in labels:
                if label not in examples:
                    row = found["later_intermediate"]
                    p = int(row["factor"])
                    examples[label] = dict(n=str(n), factors=[str(x) for x in sorted((p, n//p))], witness=row,
                                           gcd_also_split="gcd" in found, fermat_midpoints=work["fermat_midpoints"],
                                           square_roots=work["discriminant_roots"],
                                           same_total_roots_fermat_split="matched_total_roots" in found)
        for hit in found.values():
            p = int(hit["factor"])
            if p <= 1 or n % p or p == n:
                raise ArithmeticError("bad split")
            pair = sorted((p, n//p))
            if n in successes and successes[n] != pair:
                raise ArithmeticError("methods returned different pairs for a semiprime")
            successes[n] = pair
    count_json = {key: str(count) if key=="full_raw_indices" else count for key,count in sorted(counts.items())}
    return dict(work=count_json, splits=dict(sorted(splits.items())), examples=examples), successes, primary_hits


def compare_bands(cases, *, raw=False):
    cases = list(cases)
    sharp, successes, sharp_hits = summarize(cases, raw=raw)
    dyadic, old_successes, old_hits = summarize(cases, raw=raw, sharp=False)
    if old_hits != sharp_hits:
        raise ArithmeticError("the product-only interval changed a primary signed fraction or factor")
    if any(n in successes and pair != successes[n] for n, pair in old_successes.items()):
        raise ArithmeticError("inconsistent factorizations between the two methods")
    return dict(**sharp, dyadic=dyadic), successes | old_successes


def measure():
    primes = [p for p in primes_through(511) if p >= 256]
    main, successes = compare_bands(((p*q, 9) for p, q in combinations(primes, 2)), raw=True)
    prior = json.loads(ORIGINAL.read_text())
    heldout = []
    for block in prior["small"]:
        bits = block["factor_bits"]
        row, pairs = compare_bands((int(r["n"]), bits) for r in block["rows"])
        successes.update(pairs)
        heldout.append(dict(factor_bits=bits, **row))
    controls = []
    for row in prior["controls"]:
        result, pairs = compare_bands([(int(row["n"]), row["factor_bits"])])
        successes.update(pairs)
        controls.append(dict(id=row["id"], n=row["n"], **result))
    return dict(menu="All distinct prefix LCMs E <= N satisfying (E+1)^2 >= 4N.",
                inputs="Every unordered pair of distinct nine-bit primes; then the fixed scaled-power-menu panel.",
                raw="Full raw t counts are sums of Euclidean quotients. Only the nine-bit panel enumerates all t independently.",
                band="Primary uses the factor-width endpoints and the product to bound the even sum. The dyadic baseline uses only the common factor width.",
                matched_budget="B is the number of discriminant roots. The primary spends 1+B total roots; matched_total_roots permits one Fermat setup and B midpoints. matched_without_setup excludes the primary setup, permitting up to B-1 midpoints and skipping B=0. matched_midpoints always permits B midpoints plus a setup and skips B=0. The dyadic baseline spends B total roots.",
                fermat_limit=FERMAT_LIMIT, nine_bit=main, holdout=heldout, controls=controls), successes


def verify(pairs, panel_name="IntermediateTotientPanel"):
    """Certify all numerically reported splits, sharing the prime proofs across products."""
    by_prime = sorted({p for pair in pairs.values() for p in pair})
    imports, bodies = set(), []
    for p in by_prime:
        source = render_certificate(p, [p])
        imports.update(line for line in source.splitlines() if line.startswith("import "))
        body = source.split("namespace PrimeFactors.Generated\n", 1)[1].split("theorem factorization", 1)[0]
        bodies.append(f"namespace P{p}\n{body}theorem verified : Nat.Prime {p} := prime_{p}\nend P{p}")
    statements = []
    for i, (n, (p, q)) in enumerate(sorted(pairs.items())):
        statements.append(f"theorem case{i} : ExactFactorization {n} [{p}, {q}] :=\n"
                          f"  .cons (n := {q}) P{p}.verified (.cons (n := 1) P{q}.verified exactFactorization_nil)")
    # A single audited theorem depends on all recovered product statements, in a balanced conjunction.
    def join(lo, hi):
        if lo+1 == hi:
            n, pair = sorted_pairs[lo]
            return f"ExactFactorization {n} {pair}", f"case{lo}"
        mid = (lo+hi)//2
        a, ap = join(lo, mid)
        b, bp = join(mid, hi)
        return f"({a} ∧ {b})", f"⟨{ap}, {bp}⟩"

    sorted_pairs = sorted(pairs.items())
    goal, proof = join(0, len(sorted_pairs))
    path = ROOT/"build"/f"{panel_name}.lean"
    path.parent.mkdir(parents=True, exist_ok=True)
    ns = f"PrimeFactors.{panel_name}"
    path.write_text("\n\n".join(["\n".join(sorted(imports)), "set_option maxRecDepth 8192",
                                 f"namespace {ns}", *bodies, *statements, f"theorem panel : {goal} :=\n  {proof}",
                                 "#print axioms panel", f"end {ns}", ""]))
    verify_file(path, ns+".panel")


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    modes = cli.add_mutually_exclusive_group()
    modes.add_argument("--check", action="store_true")
    modes.add_argument("--write", action="store_true")
    cli.add_argument("--verify", action="store_true")
    args = cli.parse_args()
    record, pairs = measure()
    if args.write:
        RECORD.write_text(json.dumps(record, indent=2)+"\n")
    if args.check and record != json.loads(RECORD.read_text()):
        raise SystemExit("the counts differ from the stored record")
    if args.verify:
        verify(pairs)
        print(f"Lean checked {len(pairs)} distinct recovered products.")
    print("Nine-bit census", record["nine_bit"])
    for row in record["controls"]:
        print(row["id"], row["work"], row["splits"])
