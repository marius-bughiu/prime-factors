"""Translate X³−X and read its middle coefficient modulo an odd public product.

Run `python3 -m experiments.translated_hasse --verify` to replay the fixed panel.
All binomial updates divide exactly in Z. No denominator is inverted modulo N.
"""
import argparse
import json
from math import comb, gcd, isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SUMMARY = ROOT / "research" / "translated-hasse.json"


def search(n, shifts=(1, 2, 3), max_index=8192):
    """Return the first proper coefficient gcd and results for all requested shifts."""
    shifts = tuple(shifts)
    if n < 3 or not n % 2 or max_index < 0 or not shifts:
        raise ValueError("expected an odd product >= 3, shifts, and a nonnegative cap")
    m = (n - 1) // 2
    bottom = (m + 1) // 2
    work = dict(index=str(m), max_index=max_index, shifts=list(shifts),
                required_terms=str(m - bottom + 1), terms=0, initial_binomials=0,
                exact_divisions=0, horner_updates=0, coefficient_gcds=0,
                largest_binomial_bits=0, readings=[])
    if m > max_index:
        return None, dict(work, outcome="index_limit")

    # Descend j from m to ceil(m/2). The signed coefficient of c^(2j-m)
    # is (-1)^(m-j) choose(m,j) choose(m+2j,2m).
    left = 1
    right = comb(3*m, 2*m)
    sign = 1
    values = [0] * len(shifts)
    squares = [c*c % n for c in shifts]
    work["initial_binomials"] = 1
    for j in range(m, bottom - 1, -1):
        coefficient = sign * (left % n) * (right % n) % n
        for i, square in enumerate(squares):
            values[i] = (values[i]*square + coefficient) % n
        work["terms"] += 1
        work["horner_updates"] += len(shifts)
        work["largest_binomial_bits"] = max(
            work["largest_binomial_bits"], left.bit_length(), right.bit_length())
        if j != bottom:
            left = left*j // (m - j + 1)
            k = m + 2*j
            right = right*(k - 2*m)*(k - 2*m - 1) // (k*(k-1))
            work["exact_divisions"] += 2
            sign = -sign

    factor = None
    for c, value in zip(shifts, values):
        if m % 2:
            value = value*c % n
        g = gcd(value, n)
        work["readings"].append(dict(shift=c, residue=value, gcd=g))
        work["coefficient_gcds"] += 1
        if factor is None and 1 < g < n:
            factor = g
    work["outcome"] = "coefficient_divisor" if factor else "no_split"
    return factor, work


def delannoy_values(indices):
    """Compute D_j exactly from the central Delannoy recurrence, independently."""
    targets = set(indices)
    if any(j < 0 for j in targets):
        raise ValueError("negative Delannoy index")
    results = {}
    previous, current = 1, 3
    if 0 in targets:
        results[0] = previous
    max_index = max(targets, default=0)
    for j in range(1, max_index + 1):
        if j in targets:
            results[j] = current
        if j < max_index:
            following = (3*(2*j+1)*current - j*previous) // (j+1)
            previous, current = current, following
    return results


def first_singular_denominator(n, index):
    """Separate comparison for the recurrence over Z/nZ, starting at D0 and D1."""
    for divisor in range(2, index + 1):
        g = gcd(divisor, n)
        if g != 1:
            return divisor, g
    return None


def _primes(bits):
    start, stop = 1 << (bits-1), 1 << bits
    return [n for n in range(max(3, start | 1), stop, 2)
            if all(n % k for k in range(3, isqrt(n)+1, 2))]


def _bucket():
    return dict(products=0, c1_splits=0, c1_zero_mod_n=0, any_split=0,
                extra_over_c1=0, misses=0, singular_denominator_divisors=0)


def panel():
    """Complete equal-width census and two pre-capped 2048-bit controls."""
    pairs = []
    for bits in range(4, 8):
        primes = _primes(bits)
        pairs.extend((bits, p, q) for i, p in enumerate(primes) for q in primes[i+1:])
    exact = delannoy_values((p*q-1)//2 for _, p, q in pairs)
    grouped = {}
    totals = _bucket()
    for bits, p, q in pairs:
        n = p*q
        factor, work = search(n)
        readings = work["readings"]
        if readings[0]["residue"] != exact[(n-1)//2] % n:
            raise AssertionError("independent Delannoy recurrence disagrees")
        if factor is not None and factor not in (p, q):
            raise AssertionError("coefficient gcd disagrees with independent target")
        if any(row["gcd"] not in (1, p, q, n) for row in readings):
            raise AssertionError("unexpected divisor")
        singular = first_singular_denominator(n, (n-1)//2)
        if singular is not None and singular[1] not in (p, q, n):
            raise AssertionError("unexpected denominator gcd")
        label = "-".join(sorted(("split" if r % 4 == 1 else "inert" for r in (p, q))))
        group = grouped.setdefault(f"{bits}-bit {label}", _bucket())
        first = 1 < readings[0]["gcd"] < n
        for counts in (group, totals):
            counts["products"] += 1
            counts["c1_splits"] += first
            counts["c1_zero_mod_n"] += readings[0]["gcd"] == n
            counts["any_split"] += factor is not None
            counts["extra_over_c1"] += factor is not None and not first
            counts["misses"] += factor is None
            counts["singular_denominator_divisors"] += singular is not None and singular[1] < n

    examples = {}
    for n in (65, 77, 187):
        factor, work = search(n)
        examples[str(n)] = dict(factor=factor, work=work,
                                first_singular_denominator=list(first_singular_denominator(n, (n-1)//2)))
    controls = {}
    fixture = json.loads((ROOT / "benchmarks" / "near-smooth-sum.json").read_text())
    for ref in ("near-smooth-fresh-2048", "near-smooth-crossed-2048"):
        n = int(next(case["n"] for case in fixture if case["id"] == ref))
        factor, work = search(n)
        controls[ref] = dict(factor=factor, outstanding_cofactor=str(n), work=work)
    return dict(shifts=[1,2,3], max_index=8192,
                population="Every unordered pair of distinct odd primes of the same bit width, 4 through 7.",
                delannoy_indices_checked=len(exact), totals=totals, by_class=grouped,
                examples=examples, capped_controls=controls)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--verify", action="store_true")
    args = parser.parse_args()
    result = panel()
    if args.verify:
        if result != json.loads(SUMMARY.read_text()):
            raise SystemExit("translated Hasse census differs from stored results")
        print(json.dumps(result["totals"], sort_keys=True))
    elif args.write:
        SUMMARY.write_text(json.dumps(result, indent=2) + "\n")
    else:
        print(json.dumps(result, indent=2))
