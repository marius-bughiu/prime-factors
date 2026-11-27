"""Price a small square table for the lower endpoint of the equal-prime-width sum band."""
import argparse
from bisect import bisect_right
from collections import Counter
from hashlib import sha256
from itertools import combinations
import json
from math import isqrt
from pathlib import Path
import platform
from statistics import median
import subprocess
import sys
from time import perf_counter_ns

from experiments.intermediate_totient_rows import ORIGINAL, product_band, scan
from experiments.scaled_power_menu import prefixes
from scripts.factor import primes_through

ROOT = Path(__file__).resolve().parents[1]
RECORD = ROOT / "research" / "midpoint-table-band.json"
MODES = ("dyadic", "sharp", "sharp_folded", "table", "chord")
COUNTERS = ("visited_blocks", "block_edge_checks", "blocks_clipped", "endpoint_divisions",
            "width_indices", "integer_candidates", "discriminant_roots")


def upper_endpoint(n, bits):
    """Even strict upper bound, for 0 <= n < 2^(2*bits)."""
    mask = (1 << bits) - 1
    top = n >> bits
    folded = top + (n & mask)
    # n = mask*top + folded, and 0 <= folded <= 2*mask.
    mersenne_quotient = top + ((folded + 1 + (folded >> bits)) >> bits)
    return min((1 << (bits - 1)) + (n >> (bits - 1)), mask + mersenne_quotient) & ~1


def table_band(n, bits, squares, *, interpolate=False):
    """Enclose the true odd sum deficit of two odd factors of the advertised bit width."""
    shift = max(0, bits - 8)
    leading = n >> (2 * shift)
    # At width >=8, the product promise gives leading >=128².
    j = bisect_right(squares, leading, 129 if bits >= 8 else 1) - 1
    base = j << shift
    if interpolate and shift:
        fractional_bits = min(shift, 8)
        offset = ((leading - squares[j]) << fractional_bits) // (2*j + 1)
        base += offset << (shift - fractional_bits)
    # For a nonsquare leading word the chord lies strictly below its square root.
    # For a square leading word and positive shift, base is even and n is odd.
    ceiling_lower = base + int(shift != 0 or squares[j] < n)
    return max((1 << bits) + 1, 2 * ceiling_lower - 1), upper_endpoint(n, bits)


def panels():
    nine_bit = [p for p in primes_through(511) if p >= 256]
    yield "all_9_bit", [(p*q, 9) for p, q in combinations(nine_bit, 2)]
    prior = json.loads(ORIGINAL.read_text())
    for block in prior["small"]:
        bits = block["factor_bits"]
        yield f"holdout_{bits}", [(int(row["n"]), bits) for row in block["rows"]]
    for row in prior["controls"]:
        yield row["id"], [(int(row["n"]), row["factor_bits"])]


def worker(mode):
    """Run the primary scan, including regenerating every public exponent and band."""
    if mode not in MODES:
        raise ValueError("unknown comparison mode")
    squares = tuple(j*j for j in range(256)) if mode in ("table", "chord") else ()
    summaries = {}
    for label, cases in panels():
        work = Counter(dict.fromkeys(COUNTERS, 0))
        hits = []
        split_inputs = 0
        comparisons = tiny_divisions = 0
        scan_digest = sha256()
        for n, bits in cases:
            if mode in ("table", "chord"):
                band = table_band(n, bits, squares, interpolate=mode == "chord")
                tiny_divisions += mode == "chord" and bits > 8
                comparisons += (7 if bits >= 8 else 8) + (bits <= 8)
            elif mode == "sharp_folded":
                band = (max((1 << bits) + 1, 2*isqrt(n-1) + 1), upper_endpoint(n, bits))
            elif mode == "sharp":
                band = product_band(n, bits)
            else:
                band = None
            success = False
            for _, exponent, _ in prefixes(n):
                work["prefix_ratio_quotients"] += 1
                if (exponent + 1)**2 < 4*n:
                    continue
                work["exponents"] += 1
                counts, found = scan(n, bits, exponent, band=band, price_full=False)
                charged = tuple(counts[key] for key in COUNTERS)
                scan_digest.update(repr(charged).encode())
                for key, amount in zip(COUNTERS, charged):
                    work[key] += amount
                for kind, row in sorted(found.items()):
                    factor = int(row["factor"])
                    if not 1 < factor < n or n % factor:
                        raise ArithmeticError("invalid split")
                    hits.append((n, exponent, kind, row["a"], row["b"], row["t"], factor))
                    success = True
            split_inputs += success
        work["band_isqrts"] = len(cases) if mode in ("sharp", "sharp_folded") else 0
        work["band_divisions_with_numerator_n"] = 2*len(cases) if mode == "sharp" else 0
        work["small_table_comparisons"] = comparisons
        work["small_chord_divisions"] = tiny_divisions
        work["all_isqrts"] = work["band_isqrts"] + work["discriminant_roots"]
        work["inputs"] = len(cases)
        work["split_inputs"] = split_inputs
        # Every primary witness at every exponent (the clipped band limits may differ).
        digest = sha256(json.dumps(hits, separators=(",", ":")).encode()).hexdigest()
        summaries[label] = {"counts": dict(work), "witness_digest": digest,
                            "scan_digest": scan_digest.hexdigest()}
        if len(cases) == 1:
            summaries[label]["remaining"] = [] if split_inputs else [str(cases[0][0])]
    return summaries


def run(repeats):
    if repeats < 1:
        raise ValueError("at least one timing round required")
    measurements = {mode: [] for mode in MODES}
    data = {}
    for rep in range(repeats):
        for mode in MODES[rep % len(MODES):] + MODES[:rep % len(MODES)]:
            start = perf_counter_ns()
            payload = subprocess.check_output([sys.executable, "-m", "experiments.midpoint_table_band",
                                               "--worker", mode], cwd=ROOT)
            measurements[mode].append((perf_counter_ns() - start) / 1e6)
            output = json.loads(payload)
            if mode in data and data[mode] != output:
                raise ArithmeticError("nondeterministic search results")
            data[mode] = output
    for name in data["table"]:
        if len({data[m][name]["witness_digest"] for m in MODES}) != 1:
            raise ArithmeticError(f"the band changed a primary witness for {name}")
        if data["sharp"][name]["scan_digest"] != data["sharp_folded"][name]["scan_digest"]:
            raise ArithmeticError(f"folding changed the exact scan for {name}")
    totals = {}
    for mode, results in data.items():
        counter = Counter()
        for panel in results.values():
            counter.update(panel["counts"])
        totals[mode] = dict(counter)
    timings = {mode: {"elapsed_ms": [round(x, 3) for x in samples],
                      "median_ms": round(median(samples), 3)}
               for mode, samples in measurements.items()}
    return {"chord_math": "Let t be the leading word, j its table square root and h=min(shift,8). Chord offset=floor((t-j²)*2^h/(2j+1)). Since j+(t-j²)/(2j+1)<=sqrt(t), it gives a lower bound. Equality requires t=j². For positive shifts that base is even and N odd.",
            "inputs": "All distinct nine-bit prime pairs, the 64 original holdouts and both 2048-bit controls.",
            "pricing": "Per-process wall time includes interpreter, imports, input preparation, square table creation, prefix LCM generation, Euclidean scan, witness/count digests and output. Excludes Fermat and gcd baselines. Modes rotate by round.",
            "division_counts": "visited_blocks counts Euclidean divmod; endpoint_divisions counts clipped divisions; width_indices counts divisibility remainders; integer_candidates counts reconstruction quotients. Operand sizes vary. Initial sharp has two additional numerator-N floor divisions per input; folded, table and chord have zero. prefix_ratio_quotients counts shared quotient operations from prefix generation. lcm internals are timed and omitted from the arithmetic counters.",
            "table_setup": "Once per table or chord process, 256 small squares are generated and stored. Per input, seven bisection comparisons at widths >=8 and eight below; one additional small comparison when width <=8. The chord spends at most one 17-by-9-bit division per input.",
            "totals": totals, "panels": data, "python": platform.python_version(),
            "machine": platform.machine(), "timings": timings}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worker", choices=MODES)
    parser.add_argument("--repeats", type=int, default=10)
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--write", action="store_true")
    action.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.worker:
        print(json.dumps(worker(args.worker)))
    else:
        record = run(args.repeats)
        if args.write:
            RECORD.write_text(json.dumps(record, indent=2) + "\n")
        if args.check:
            stored = json.loads(RECORD.read_text())
            for key in ("totals", "panels"):
                if stored[key] != record[key]:
                    raise SystemExit(f"stored {key} differ")
        print(json.dumps({"totals": record["totals"], "timings": record["timings"]}, indent=2))
