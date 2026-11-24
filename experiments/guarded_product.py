"""Compare exact schoolbook multiplication with an exact guarded truncation.

Run `python3 experiments/guarded_product.py 143 8`, --fixtures, or --sweep.
Both inputs are in [0, 2**width). Omitting s output bits retains the low
2*width-s columns. A table on the top h=s+1 bits of each input removes all
aliases: x*y and N lie in the same half-open interval of width less than
2**(2*width-s). The guard is built by enumerating 4**h bit patterns, so
this experiment limits s to 1, 2 or 3 (at most 256 patterns).

Each comparison uses the same x>1, x<=y and t<(y mod 2**k) predicates and
the same min-fill rule. The reported modular sum ranges over all such input
pairs. On a distinct semiprime whose factors fit, it is the larger prime's
low k bits. The program returns this residue without reconstructing factors.
"""

import argparse
import json
from math import isqrt

if __package__:
    from .bit_marginals import multiplier_tables
    from .quarter_residue import FIXTURES, count_network, require_comparison, require_nontrivial
else:
    from bit_marginals import multiplier_tables
    from quarter_residue import FIXTURES, count_network, require_comparison, require_nontrivial


MAX_OMITTED = 3


def guarded_multiplier(n, width, omitted):
    if width < 1 or not 0 <= n < 1 << (2 * width):
        raise ValueError("target must fit a positive-width unsigned multiplier")
    if not 0 <= omitted <= min(MAX_OMITTED, width - 1):
        raise ValueError("omit at most three bits, with omitted + 1 <= width")
    kept = 2 * width - omitted
    net = multiplier_tables(n, width, output_bits=kept)
    if omitted == 0:
        return net, 0, 0

    h = omitted + 1
    block_squared = 1 << (2 * (width - h))
    # Both interval endpoints are multiples of block_squared.
    block_target = n // block_squared

    def possible(*bits):
        a = sum(bit << i for i, bit in enumerate(bits[:h]))
        c = sum(bit << i for i, bit in enumerate(bits[h:]))
        return a * c <= block_target < (a + 1) * (c + 1)

    net.relation([*net.xs[-h:], *net.ys[-h:]], possible)
    return net, 1 << (2 * h), len(net.tables[-1].rows)


def ordered_readout(n, width, omitted):
    if n < 1:
        raise ValueError("expected a positive product")
    net, guard_patterns, guard_rows = guarded_multiplier(n, width, omitted)
    k = (n.bit_length() + 3) // 4
    require_nontrivial(net, net.xs)
    require_comparison(net, net.xs, net.ys, strict=False)
    free_bits = [net.wire() for _ in range(k)]
    require_comparison(net, free_bits, net.ys[:k], strict=True)
    result = count_network(n, width, k, False, net)
    # Here width is supplied explicitly, independently of any balance promise.
    del result["balanced"]
    result.update(omitted=omitted, kept=2 * width - omitted,
                  guard_patterns=guard_patterns, guard_rows=guard_rows)
    return result


def compare(n, width):
    full = ordered_readout(n, width, 0)
    guarded = [ordered_readout(n, width, s)
               for s in range(1, min(MAX_OMITTED, width - 1) + 1)]
    if any(row["residue"] != full["residue"] for row in guarded):
        raise AssertionError(f"guarded readouts disagree with the full multiplier: {full}, {guarded}")
    return {"full": full, "guarded": guarded}


def run_fixtures():
    for case in json.loads(FIXTURES.read_text()):
        n = int(case["n"])
        width = isqrt(2 * n).bit_length() if case.get("balanced") else n.bit_length()
        result = compare(n, width)
        p, q = map(int, case["factors"])
        expected = q % int(result["full"]["modulus"]) if q < 1 << width else 0
        if not (1 < p < q and p * q == n and int(result["full"]["residue"]) == expected):
            raise AssertionError(f"unexpected reference or readout for {case['id']}: {result}")
        yield result


def equal_width_sweep():
    """Enumerate a bounded input family for comparison, then supply only N and width."""
    for b in (4, 5, 6):
        primes = [p for p in range(1 << (b - 1), 1 << b)
                  if all(p % d for d in range(2, isqrt(p) + 1))]
        products = [p * q for i, p in enumerate(primes) for q in primes[i + 1:]]
        totals = [0] * 4
        fewer_joins = [0] * 3
        smaller_peak = [0] * 3
        larger_peak = [0] * 3
        for n in products:
            result = compare(n, b)
            full = result["full"]
            totals[0] += full["matched_rows"]
            for i, row in enumerate(result["guarded"]):
                totals[i + 1] += row["matched_rows"]
                fewer_joins[i] += row["matched_rows"] < full["matched_rows"]
                smaller_peak[i] += row["peak_rows"] < full["peak_rows"]
                larger_peak[i] += row["peak_rows"] > full["peak_rows"]
        yield dict(width=b, products=len(products), omitted=[0, 1, 2, 3],
                   total_joins=totals, fewer_joins_than_full=fewer_joins,
                   smaller_peak_than_full=smaller_peak, larger_peak_than_full=larger_peak)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", nargs="?", type=int)
    parser.add_argument("width", nargs="?", type=int)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--fixtures", action="store_true")
    modes.add_argument("--sweep", action="store_true",
                       help="all products of distinct equal-width primes at 4, 5 and 6 bits")
    args = parser.parse_args()
    if args.sweep and args.n is None:
        for result in equal_width_sweep():
            print(json.dumps(result))
    elif args.fixtures and args.n is None:
        for result in run_fixtures():
            print(json.dumps(result))
    elif not args.fixtures and not args.sweep and args.n is not None and args.width is not None:
        print(json.dumps(compare(args.n, args.width)))
    else:
        parser.error("supply the product and input width, --fixtures, or --sweep")
