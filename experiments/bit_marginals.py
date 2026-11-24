"""Contract a tagged Boolean multiplier and read its bit marginals over F_3.

Run `python3 experiments/bit_marginals.py --fixtures` or supply a decimal
product, e.g. `143`. For p <= q <= 2p the public bound q <= isqrt(2*n)
sets the width. Use --full-width to include every divisor and subtract
the publicly known orientations (1,n) and (n,1). An optional width b gives
each input the range [0, 2**b),
e.g. `143 4`. A distinct-prime semiprime with both primes inside and
2**b <= n has exactly two accepted assignments. Other products may give
different counts or residues that alias two modulo 3.
"""

import argparse
import itertools
import json
from dataclasses import dataclass
from math import isqrt
from pathlib import Path


FIXTURES = Path(__file__).resolve().parents[1] / "benchmarks" / "bit-marginals.json"


class Tape:
    """Share commutative gates. Simplifications use literal 0 and 1 only."""

    def __init__(self, width):
        self.nodes = [("constant", 0, 0), ("constant", 1, 0)]
        self.tags = []
        for i in range(width):
            self.tags.append(len(self.nodes))
            self.nodes.append(("tag", i, 0))
        self.gates = {}

    def gate(self, op, a, b):
        if a > b:
            a, b = b, a
        if op == "+" and a == 0:
            return b
        if op == "*":
            if a == 0:
                return 0
            if a == 1:
                return b
        key = (op, a, b)
        if key not in self.gates:
            self.gates[key] = len(self.nodes)
            self.nodes.append(key)
        return self.gates[key]

    def differentiate_at_one(self, root):
        """Each reachable arithmetic gate receives one forward and one reverse visit."""
        active = {root}
        for i in range(root, -1, -1):
            op, a, b = self.nodes[i]
            if i in active and op in ("+", "*"):
                active.update((a, b))

        values = [0] * len(self.nodes)
        for i, (op, a, b) in enumerate(self.nodes):
            if i not in active:
                continue
            if op == "constant":
                values[i] = a
            elif op == "tag":
                values[i] = 1
            elif op == "+":
                values[i] = (values[a] + values[b]) % 3
            else:
                values[i] = values[a] * values[b] % 3

        adjoints = [0] * len(self.nodes)
        adjoints[root] = 1
        active_gates = 0
        zero_gates_with_adjoint = 0
        for i in range(root, -1, -1):
            op, a, b = self.nodes[i]
            if i not in active or op not in ("+", "*"):
                continue
            active_gates += 1
            dz = adjoints[i]
            if values[i] == 0 and dz:
                zero_gates_with_adjoint += 1
            da, db = (dz, dz) if op == "+" else (dz * values[b], dz * values[a])
            adjoints[a] = (adjoints[a] + da) % 3
            adjoints[b] = (adjoints[b] + db) % 3
        return (values[root], [adjoints[i] for i in self.tags],
                active_gates, zero_gates_with_adjoint)


@dataclass
class Table:
    # Both fields use global wire masks. Omitted rows have identically zero weight.
    scope: int
    rows: dict


class Multiplier:
    def __init__(self):
        self.wires = 0
        self.tables = []

    def wire(self):
        wire = 1 << self.wires
        self.wires += 1
        return wire

    def relation(self, wires, allowed):
        rows = {}
        for bits in itertools.product(range(2), repeat=len(wires)):
            if allowed(*bits):
                rows[sum(w for w, bit in zip(wires, bits) if bit)] = 1
        self.tables.append(Table(sum(wires), rows))

    def adder(self, inputs):
        low, high = self.wire(), self.wire()
        self.relation([*inputs, low, high],
                      lambda *bits: sum(bits[:-2]) == bits[-2] + 2 * bits[-1])
        return low, high


def multiplier_tables(n, width, tape):
    net = Multiplier()
    xs = [net.wire() for _ in range(width)]
    ys = [net.wire() for _ in range(width)]
    columns = [[] for _ in range(2 * width)]
    for i, x in enumerate(xs):
        net.tables.append(Table(x, {0: 1, x: tape.tags[i]}))
        for j, y in enumerate(ys):
            out = net.wire()
            net.relation([x, y, out], lambda a, b, c: (a & b) == c)
            columns[i + j].append(out)

    # Add two or three bits of equal place value. Fix the final bit of each
    # column to N. The partial-product and carry wires are uniquely determined.
    for i, column in enumerate(columns):
        while len(column) > 1:
            arity = min(3, len(column))
            inputs = column[:arity]
            del column[:arity]
            low, high = net.adder(inputs)
            column.append(low)
            columns[i + 1].append(high)
        bit = (n >> i) & 1
        if column:
            net.tables.append(Table(column[0], {column[0] * bit: 1}))
        elif bit:
            net.tables.append(Table(0, {}))
    return net


def wires(scope):
    while scope:
        wire = scope & -scope
        yield wire
        scope ^= wire


def bit_count(mask):
    return bin(mask).count("1")


def min_fill_order(net):
    neighbors = {1 << i: 0 for i in range(net.wires)}
    for table in net.tables:
        for wire in wires(table.scope):
            neighbors[wire] |= table.scope ^ wire

    def cost(wire):
        scope = neighbors[wire]
        missing = sum(bit_count(scope & ~(v | neighbors[v])) for v in wires(scope)) // 2
        return missing, bit_count(scope), wire

    order = []
    while neighbors:
        wire = min(neighbors, key=cost)
        scope = neighbors.pop(wire)
        order.append(wire)
        for v in wires(scope):
            neighbors[v] = (neighbors[v] | scope) & ~(wire | v)
    return order


@dataclass
class Construction:
    matched_rows: int = 0
    peak_rows: int = 0
    peak_scope: int = 0

    def record(self, table):
        self.peak_rows = max(self.peak_rows, len(table.rows))
        self.peak_scope = max(self.peak_scope, bit_count(table.scope))


def join(left, right, tape, stats):
    shared = left.scope & right.scope
    index = {}
    for bits, node in right.rows.items():
        index.setdefault(bits & shared, []).append((bits, node))
    rows = {}
    for bits, node in left.rows.items():
        for other, other_node in index.get(bits & shared, ()):
            rows[bits | other] = tape.gate("*", node, other_node)
    joined = Table(left.scope | right.scope, rows)
    stats.matched_rows += len(rows)
    stats.record(joined)
    return joined


def contract(net, tape):
    tables = list(net.tables)
    stats = Construction()
    for table in tables:
        stats.record(table)
    for wire in min_fill_order(net):
        bucket = [table for table in tables if table.scope & wire]
        tables = [table for table in tables if not table.scope & wire]
        bucket.sort(key=lambda table: len(table.rows))
        merged = bucket[0]
        for part in bucket[1:]:
            merged = join(merged, part, tape, stats)
        rows = {}
        for bits, node in merged.rows.items():
            projected = bits & ~wire
            rows[projected] = tape.gate("+", rows.get(projected, 0), node)
        tables.append(Table(merged.scope ^ wire, rows))
    root = 1
    for table in tables:
        assert table.scope == 0
        root = tape.gate("*", root, table.rows.get(0, 0))
    return root, stats


def discover(n, width=None, *, full_width=False):
    if n < 1:
        raise ValueError("expected a positive product")
    if full_width:
        if width is not None:
            raise ValueError("full width is determined by the product")
        width = n.bit_length()
    elif width is None:
        width = isqrt(2 * n).bit_length()
    if width < 1 or n >= 1 << (2 * width):
        raise ValueError("product must be positive and fit the multiplier output width")
    tape = Tape(width)
    net = multiplier_tables(n, width, tape)
    root, stats = contract(net, tape)
    count, marginals, active_gates, zero_gates = tape.differentiate_at_one(root)
    if full_width:
        # Only the orientation (1,1) exists when n=1.
        for first in ((1, n) if n > 1 else (1,)):
            count = (count - 1) % 3
            marginals = [(value - ((first >> i) & 1)) % 3 for i, value in enumerate(marginals)]
    total = sum(c << i for i, c in enumerate(marginals))
    factors = []
    discriminant = total * total - 4 * n
    if count == 2 and discriminant >= 0:
        gap = isqrt(discriminant)
        low, high = (total - gap) // 2, (total + gap) // 2
        if gap * gap == discriminant and 1 < low < high < 1 << width and low * high == n:
            factors = [str(low), str(high)]
    return dict(n=str(n), width=width, full_width=full_width, count_mod3=count, marginals=marginals,
                weighted_sum=total, factors=factors, remaining=[] if factors or n == 1 else [str(n)],
                wires=net.wires, tables=len(net.tables),
                matched_rows=stats.matched_rows, peak_rows=stats.peak_rows,
                peak_scope=stats.peak_scope, tape_nodes=len(tape.nodes),
                built_gates=len(tape.gates), active_gates=active_gates,
                zero_gates_with_adjoint=zero_gates)


def run_fixtures():
    for case in json.loads(FIXTURES.read_text()):
        result = discover(int(case["n"]), case.get("width"), full_width=case.get("full_width", False))
        if result["factors"] != case["factors"] or result["count_mod3"] != case["count_mod3"]:
            raise AssertionError(f"{case['id']} gave {result}")
        if result["factors"]:
            p, q = map(int, result["factors"])
            expected = [((p >> i) & 1) + ((q >> i) & 1) for i in range(result["width"])]
            if result["marginals"] != expected or result["weighted_sum"] != p + q:
                raise AssertionError(f"{case['id']} has incorrect bit marginals: {result}")
        yield result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int, nargs="?")
    parser.add_argument("width", type=int, nargs="?")
    parser.add_argument("--fixtures", action="store_true")
    parser.add_argument("--full-width", action="store_true", help="include all divisors and subtract the trivial pairs")
    args = parser.parse_args()
    if args.fixtures and args.n is None and args.width is None and not args.full_width:
        for result in run_fixtures():
            print(json.dumps(result))
    elif not args.fixtures and args.n is not None and not (args.width and args.full_width):
        print(json.dumps(discover(args.n, args.width, full_width=args.full_width)))
    else:
        parser.error("pass either --fixtures or a product with optional input bit width")
