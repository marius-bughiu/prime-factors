"""Count ordered factor pairs with an auxiliary comparison modulo 2**k.

Run `python3 experiments/quarter_residue.py 143` for the full input box.
The --balanced option uses the public bound q <= isqrt(2*n) for q <= 2p.
For distinct prime factors p < q in the box, the count is q modulo 2**k.
The output is a residue. For a general product it sums the larger member
of every nontrivial ordered pair, modulo the same modulus.
"""

import argparse
import json
from math import isqrt
from pathlib import Path

if __package__:
    from .bit_marginals import Table, contract, multiplier_tables
else:
    from bit_marginals import Table, contract, multiplier_tables


FIXTURES = Path(__file__).resolve().parents[1] / "benchmarks" / "quarter-residues.json"


class ModularCounter:
    def __init__(self, modulus):
        self.modulus = modulus
        self.additions = 0
        self.multiplications = 0

    def gate(self, op, a, b):
        if op == "+":
            self.additions += 1
            return (a + b) % self.modulus
        if op == "*":
            self.multiplications += 1
            return (a * b) % self.modulus
        raise ValueError(f"unknown arithmetic operation {op}")


def require_comparison(net, left, right, *, strict):
    """A more significant unequal pair overrides the comparison of the lower bits."""
    if len(left) != len(right):
        raise ValueError("comparison requires equal input widths")
    state = net.wire()
    net.tables.append(Table(state, {state * int(not strict): 1}))
    for a, b in zip(left, right):
        following = net.wire()
        net.relation([a, b, state, following],
                     lambda x, y, prev, out: out == (prev if x == y else x < y))
        state = following
    net.tables.append(Table(state, {state: 1}))


def require_nontrivial(net, xs):
    # x > 1 iff its bits from position 1 up are not all zero.
    if len(xs) < 2:
        net.tables.append(Table(0, {}))
        return
    state = xs[1]
    for wire in xs[2:]:
        following = net.wire()
        net.relation([state, wire, following], lambda a, b, out: out == (a | b))
        state = following
    net.tables.append(Table(state, {state: 1}))


def ordered_network(n, balanced):
    if n < 1:
        raise ValueError("expected a positive product")
    nbits = n.bit_length()
    width = isqrt(2 * n).bit_length() if balanced else nbits
    net = multiplier_tables(n, width)
    require_nontrivial(net, net.xs)
    require_comparison(net, net.xs, net.ys, strict=False)
    return net, width, (nbits + 3) // 4


def read_residue(n, *, balanced=False):
    net, width, k = ordered_network(n, balanced)
    modulus = 1 << k
    free_bits = [net.wire() for _ in range(k)]
    require_comparison(net, free_bits, net.ys[:k], strict=True)

    counter = ModularCounter(modulus)
    residue, stats = contract(net, counter)
    return dict(n=str(n), width=width, balanced=balanced, k=k, modulus=str(modulus),
                residue=str(residue), remaining=[str(n)] if n > 1 else [],
                wires=net.wires, tables=len(net.tables), matched_rows=stats.matched_rows,
                peak_scope=stats.peak_scope, peak_rows=stats.peak_rows,
                additions=counter.additions, multiplications=counter.multiplications)


def compare_bit_queries(n, *, balanced=False):
    """Measure the same semiprime residue using k one-bit counts on the same multiplier."""
    one = read_residue(n, balanced=balanced)
    net, _, k = ordered_network(n, balanced)
    residue = 0
    joins = peak = 0
    counter = ModularCounter(2)
    for i, wire in enumerate(net.ys[:k]):
        net.tables.append(Table(wire, {wire: 1}))
        value, stats = contract(net, counter)
        net.tables.pop()
        residue += value << i
        joins += stats.matched_rows
        peak = max(peak, stats.peak_rows)
    return dict(single=one, bit_queries=dict(residue=str(residue), calls=k,
                matched_rows=joins, peak_rows=peak, additions=counter.additions,
                multiplications=counter.multiplications))


def run_fixtures():
    for case in json.loads(FIXTURES.read_text()):
        result = read_residue(int(case["n"]), balanced=case.get("balanced", False))
        # Read the reference factors only after the contraction is complete.
        p, q = map(int, case["factors"])
        if not 1 < p < q or p * q != int(result["n"]):
            raise AssertionError(f"invalid fixture reference pair for {case['id']}")
        expected = q % int(result["modulus"]) if q < 1 << result["width"] else 0
        if int(result["residue"]) != expected:
            raise AssertionError(f"{case['id']} expected residue {expected}, got {result}")
        yield result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int, nargs="?")
    parser.add_argument("--balanced", action="store_true")
    parser.add_argument("--fixtures", action="store_true")
    parser.add_argument("--compare-bits", action="store_true",
                        help="compare one count with separate binary queries on a semiprime")
    args = parser.parse_args()
    if args.fixtures and args.n is None and not args.balanced and not args.compare_bits:
        for result in run_fixtures():
            print(json.dumps(result))
    elif args.n is not None and not args.fixtures:
        run = compare_bit_queries if args.compare_bits else read_residue
        print(json.dumps(run(args.n, balanced=args.balanced)))
    else:
        parser.error("supply a product with optional --balanced, or --fixtures")
