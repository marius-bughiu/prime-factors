#!/usr/bin/env python3
"""Try small bases for a gcd split. See docs/research.md for the guarantee."""

import argparse
import json
import math
import time
from typing import Optional


def search(n: int, max_base: Optional[int] = None) -> dict:
    """Search all bases in [2, max_base], reporting the first proper divisor."""
    if n < 2:
        raise ValueError("n must be at least 2")
    if max_base is not None and max_base < 1:
        raise ValueError("max_base must be positive")
    started = time.perf_counter()
    # ln(n) < bit_length(n), so this integer bound covers the analytic window.
    limit = min(n - 1, n.bit_length() ** 2 if max_base is None else max_base)
    report = {"n": str(n), "max_base": limit, "bases_tested": 0, "status": "exhausted"}
    for base in range(2, limit + 1):
        report["bases_tested"] += 1
        factor = math.gcd(base, n)
        if factor > 1:
            kind = "base_gcd"
        else:
            residue = pow(base, n - 1, n)
            factor = math.gcd(residue - 1, n)
            if factor == 1 or factor == n:
                continue
            report["residue"] = str(residue)
            kind = "power_gcd"
        report.update(
            status="split",
            factor=str(factor),
            cofactor=str(n // factor),
            witness_base=base,
            witness_kind=kind,
        )
        break
    report["search_seconds"] = time.perf_counter() - started
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int, help="decimal integer to split")
    parser.add_argument("--max-base", type=int, help="inclusive last base (default: bit length squared)")
    args = parser.parse_args()
    try:
        report = search(args.n, args.max_base)
    except ValueError as error:
        parser.error(str(error))
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
