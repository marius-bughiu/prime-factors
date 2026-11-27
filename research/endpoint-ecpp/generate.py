"""Emit closed Lean primality proofs from the two archived PARI ECPP matrices."""

import argparse
import json
from pathlib import Path

# Each entry lists (prime factor of n - 1, multiplicity, Pocklington witness).
# The terminal subjects of the ECPP matrices are keys in this table.
POCKLINGTON = {
    11: [(2, 1, 2), (5, 1, 2)],
    13: [(2, 2, 2), (3, 1, 2)],
    19: [(2, 1, 2), (3, 2, 2)],
    23: [(2, 1, 5), (11, 1, 2)],
    29: [(2, 2, 2), (7, 1, 2)],
    53: [(2, 2, 2), (13, 1, 2)],
    71: [(2, 1, 7), (5, 1, 2), (7, 1, 2)],
    79: [(2, 1, 3), (3, 1, 2), (13, 1, 2)],
    233: [(2, 3, 3), (29, 1, 2)],
    661: [(2, 2, 2), (3, 1, 2), (5, 1, 2), (11, 1, 2)],
    2131: [(2, 1, 2), (3, 1, 2), (5, 1, 2), (71, 1, 2)],
    3079: [(2, 1, 3), (3, 4, 2), (19, 1, 2)],
    85331: [(2, 1, 2), (5, 1, 2), (7, 1, 2), (23, 1, 2), (53, 1, 2)],
    225941: [(2, 2, 2), (5, 1, 2), (11, 1, 2), (13, 1, 2), (79, 1, 2)],
    1355647: [(2, 1, 3), (3, 1, 2), (225941, 1, 2)],
    931711559: [(2, 1, 7), (71, 1, 2), (2131, 1, 2), (3079, 1, 2)],
    11591317473247: [(2, 1, 3), (3, 2, 3), (7, 2, 2), (233, 1, 2), (661, 1, 2), (85331, 1, 2)],
    7578431878942039: [(2, 1, 3), (3, 1, 3), (1355647, 1, 2), (931711559, 1, 2)],
    90941182547304469: [(2, 2, 2), (3, 1, 11), (7578431878942039, 1, 2)],
}


def pocklington_literal(n):
    if n in (2, 3, 5, 7):
        return f"(.small {n})"
    factors = []
    for prime, exponent, witness in POCKLINGTON[n]:
        # The upstream constructor stores the positive exponent minus one.
        child = pocklington_literal(prime)
        factors.append(f"({witness},{exponent - 1},{child})")
    return f"(.pock {n} [{', '.join(factors)}])"


def add(n, a, left, right, inverses):
    """Add affine points and append the inverse for each nontrivial division."""
    if left is None:
        return right
    if right is None:
        return left

    x, y = left
    u, v = right
    if x == u:
        if (y + v) % n == 0:
            return None
        if y != v:
            raise ValueError("Incompatible points with equal x coordinates")
        denominator, numerator = 2 * y, 3 * x * x + a
    else:
        denominator, numerator = u - x, v - y

    inverse = pow(denominator, -1, n)
    inverses.append(inverse)
    slope = numerator * inverse % n
    new_x = (slope * slope - x - u) % n
    return new_x, (slope * (x - new_x) - y) % n


def multiply(n, a, point, scalar):
    """Match the upstream scalar checker's high-to-low binary schedule."""
    result = None
    inverses = []
    for bit in bin(scalar)[2:]:
        result = add(n, a, result, result, inverses)
        if bit == "1":
            result = add(n, a, result, point, inverses)
    return result, inverses


def inverse_definitions(index, inverses):
    """Split large lists into definitions of at most 32 new constructors."""
    definitions = []
    tail = "[]"
    for stop in range(len(inverses), 0, -32):
        name = f"ws_{index}_{stop}"
        chunk = inverses[max(0, stop - 32):stop]
        body = " :: ".join([*map(str, chunk), tail])
        definitions.append(f"private def {name} : List Nat := {body}")
        tail = name
    return definitions, tail


def proof_source(rows, offset):
    if rows[0][0] != 2**1024 - offset:
        raise ValueError("Certificate subject differs from the requested prime")

    proofs = []
    child = None
    for index in reversed(range(len(rows))):
        n, trace, cofactor, a, (x, y) = rows[index]
        a %= n
        b = (y * y - x**3 - a * x) % n
        q, remainder = divmod(n + 1 - trace, cofactor)
        if remainder or not 1 < q < n:
            raise ValueError(f"Invalid auxiliary order at row {index}")

        if child is None:
            proofs.append(
                f"private theorem endpoint : Nat.Prime {q} := "
                f"Hex.Nat.natPrime_of_checkPrimeAt (c := {pocklington_literal(q)}) (by rfl)\n"
            )
            child = "endpoint"
        elif q != rows[index + 1][0]:
            raise ValueError(f"Broken chain at row {index}")

        point, _ = multiply(n, a, (x % n, y % n), cofactor)
        if point is None:
            raise ValueError(f"Auxiliary point is infinity at row {index}")
        xq, yq = point
        result, inverses = multiply(n, a, point, q)
        if result is not None:
            raise ValueError(f"Auxiliary order check failed at row {index}")

        discr_inverse = pow(4 * a**3 + 27 * b * b, -1, n)
        definitions, tail = inverse_definitions(index, inverses)
        proofs.extend(definitions)
        proofs.append(
            f"private theorem row{index} : Nat.Prime {n} :=\n"
            f"  Hex.ECPP.natPrime_of_step (a := {a}) (b := {b})\n"
            f"    (x := {xq}) (y := {yq}) (discrInv := {discr_inverse})\n"
            f"    (inverses := {tail}) {child} (by rfl)\n"
        )
        child = f"row{index}"

    theorem = f"endpointPrime{offset}"
    proofs.extend([
        f"theorem {theorem} : Nat.Prime (2^1024 - {offset}) := row0",
        f"#print axioms {theorem}",
    ])
    options = (
        "import HexECPPTheory.Soundness\n"
        "set_option maxRecDepth 65536\n"
        "set_option maxHeartbeats 0\n"
        "set_option exponentiation.threshold 1024\n"
    )
    return options + "\n".join(proofs) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="directory for the two generated .lean files")
    output = parser.parse_args().output
    output.mkdir(parents=True, exist_ok=True)
    inputs = Path(__file__).resolve().parent
    for offset in (105, 179):
        rows = json.loads((inputs / f"offset-{offset}.json").read_text())
        path = output / f"Endpoint{offset}.lean"
        path.write_text(proof_source(rows, offset))
        print(f"{path} ({len(rows)} elliptic steps)")


if __name__ == "__main__":
    main()
