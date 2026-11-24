"""Count ordered factor pairs with an auxiliary comparison modulo 2**k.

Run `python3 experiments/quarter_residue.py 143` for the full input box.
The --balanced option uses the public bound q <= isqrt(2*n) for q <= 2p.
For distinct prime factors p < q in the box, the count is q modulo 2**k.
The output is a residue. For a general product it sums the larger member
of every nontrivial ordered pair, modulo the same modulus.

For an odd semiprime, --unit-tags uses unary weights on the second input
bits. Combine it with --compare-bits to measure all three constructions.
Decoding a unit assumes a unique selected pair. An odd number of pairs
can produce a unit too.
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
    free_bits = [net.wire() for _ in range(k)]
    require_comparison(net, free_bits, net.ys[:k], strict=True)
    return count_network(n, width, k, balanced, net)


def count_network(n, width, k, balanced, net):
    modulus = 1 << k
    counter = ModularCounter(modulus)
    residue, stats = contract(net, counter)
    return dict(n=str(n), width=width, balanced=balanced, k=k, modulus=str(modulus),
                residue=str(residue), remaining=[str(n)] if n > 1 else [],
                wires=net.wires, tables=len(net.tables), matched_rows=stats.matched_rows,
                peak_scope=stats.peak_scope, peak_rows=stats.peak_rows,
                additions=counter.additions, multiplications=counter.multiplications)


def decode_unit(scalar, k):
    """Invert (-1)**bit1 * 5**(y//4) modulo 2**k on odd y residues."""
    if scalar % 2 == 0:
        return None
    if k == 1:
        return 1
    modulus = 1 << k
    sign = int(scalar % 4 == 3)
    target = (-scalar if sign else scalar) % modulus
    exponent = 0
    value, power = 1, 5 % modulus
    for j in range(k - 2):
        # 5**(2**j) agrees with 1 up to bit j+1 and toggles bit j+2.
        if (value ^ target) & (1 << (j + 2)):
            exponent += 1 << j
            value = value * power % modulus
        power = power * power % modulus
    return 1 + 2 * sign + 4 * exponent


def read_unit_residue(n, *, balanced=False):
    net, width, k = ordered_network(n, balanced)
    modulus = 1 << k
    power = 5 % modulus
    tagged_entries = 0
    for i, wire in enumerate(net.ys[1:k], start=1):
        unit = modulus - 1 if i == 1 else power
        # The first table incident to this bit is a three-wire AND.
        # Fuse the unary weight into that local predicate, preserving all scopes.
        table = next(t for t in net.tables if t.scope & wire)
        for bits, value in table.rows.items():
            if bits & wire:
                table.rows[bits] = value * unit % modulus
                tagged_entries += 1
        if i >= 2:
            power = power * power % modulus
    result = count_network(n, width, k, balanced, net)
    scalar = int(result["residue"])
    decoded = decode_unit(scalar, k) if n % 2 else None
    result.update(scalar=str(scalar), residue=None if decoded is None else str(decoded),
                  tagged_entries=tagged_entries,
                  status="unresolved" if decoded is None else "conditional",
                  assumption="product of two distinct odd primes inside the selected box")
    if decoded is None:
        result["reason"] = "product is even" if n % 2 == 0 else "scalar is even"
    return result


def compare_bit_queries(n, *, balanced=False, include_units=False):
    """Measure the same semiprime residue using k one-bit counts on the same multiplier."""
    one = read_residue(n, balanced=balanced)
    net, _, k = ordered_network(n, balanced)
    residue = 0
    joins = peak = 0
    parity_query_joins = 0
    counter = ModularCounter(2)
    for i, wire in enumerate(net.ys[:k]):
        net.tables.append(Table(wire, {wire: 1}))
        value, stats = contract(net, counter)
        net.tables.pop()
        residue += value << i
        joins += stats.matched_rows
        peak = max(peak, stats.peak_rows)
        if i == 0:
            parity_query_joins = stats.matched_rows
    comparison = dict(single=one, bit_queries=dict(residue=str(residue), calls=k,
                      matched_rows=joins, peak_rows=peak, additions=counter.additions,
                      multiplications=counter.multiplications))
    if include_units:
        comparison["unit_tags"] = read_unit_residue(n, balanced=balanced)
        if n % 2:
            comparison["bit_queries"]["assuming_odd_pair"] = dict(
                calls=k - 1, matched_rows=joins - parity_query_joins)
    return comparison


def run_fixtures(*, unit_tags=False, compare_bits=False):
    for case in json.loads(FIXTURES.read_text()):
        n = int(case["n"])
        balanced = case.get("balanced", False)
        if compare_bits:
            output = compare_bit_queries(n, balanced=balanced, include_units=unit_tags)
            result = output["single"]
        else:
            reader = read_unit_residue if unit_tags else read_residue
            output = result = reader(n, balanced=balanced)
        # Read the reference factors only after the contraction is complete.
        p, q = map(int, case["factors"])
        if not 1 < p < q or p * q != int(result["n"]):
            raise AssertionError(f"invalid fixture reference pair for {case['id']}")
        fits = q < 1 << result["width"]
        expected = str(q % int(result["modulus"])) if fits else "0"
        if unit_tags:
            weighted = output["unit_tags"] if compare_bits else output
            expected_unit = expected if fits and n % 2 else None
            if weighted["residue"] != expected_unit:
                raise AssertionError(f"{case['id']} expected unit readout {expected_unit}, got {weighted}")
        if (not unit_tags or compare_bits) and result["residue"] != expected:
            raise AssertionError(f"{case['id']} expected residue {expected}, got {result}")
        if compare_bits and output["bit_queries"]["residue"] != expected:
            raise AssertionError(f"{case['id']} expected bit queries {expected}, got {output}")
        yield output


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int, nargs="?")
    parser.add_argument("--balanced", action="store_true")
    parser.add_argument("--fixtures", action="store_true")
    parser.add_argument("--compare-bits", action="store_true",
                        help="compare one count with separate binary queries on a semiprime")
    parser.add_argument("--unit-tags", action="store_true",
                        help="read an odd semiprime residue using unary signed weights")
    args = parser.parse_args()
    if args.fixtures and args.n is None and not args.balanced:
        for result in run_fixtures(unit_tags=args.unit_tags, compare_bits=args.compare_bits):
            print(json.dumps(result))
    elif args.n is not None and not args.fixtures:
        if args.compare_bits:
            result = compare_bit_queries(args.n, balanced=args.balanced, include_units=args.unit_tags)
        else:
            run = read_unit_residue if args.unit_tags else read_residue
            result = run(args.n, balanced=args.balanced)
        print(json.dumps(result))
    else:
        parser.error("supply a product with optional --balanced, or --fixtures")
