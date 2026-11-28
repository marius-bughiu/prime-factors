"""Replay fixed quartic readings on the repository's published controls.

    python3 -m experiments.quartic_readings --case quartic-later-midpoint-2048
"""

import argparse
import json
from math import gcd, isqrt
from pathlib import Path

from experiments.complementary_quartic_strips import recognize_y
from experiments.quartic_product_strips import recognize

FIXTURE = Path(__file__).resolve().parents[1] / "benchmarks" / "quartic-readings.json"
DENOMINATORS = (1, 725, 1517)
BRANCHES = (("x", recognize), ("y", recognize_y))


def read_product(n):
    """Try every branch using only n. Report proper factor pairs in reading order."""
    if n < 2:
        raise ValueError("The input must be at least two.")
    hits = []
    gcd_checks = 0
    for d in DENOMINATORS:
        scaled = d**4 * n
        for branch, recognize_scaled in BRANCHES:
            raw = recognize_scaled(scaled)
            if raw is None:
                continue
            gcd_checks += 2
            p, q = sorted(gcd(n, value) for value in raw)
            if p > 1 and q > 1 and p * q == n:
                hits.append((d, branch, (p, q)))
    return hits, gcd_checks


def verify_case(case):
    n = int(case["n"])
    hits, gcd_checks = read_product(n)
    locations = [[d, branch] for d, branch, _ in hits]
    if locations != case["hits"]:
        raise ValueError(f"{case['id']}: unexpected reading locations {locations}")
    factors = [str(k) for k in hits[0][2]] if hits else []
    if factors != case["factors"] or any(pair != hits[0][2] for _, _, pair in hits):
        raise ValueError(f"{case['id']}: factor mismatch")
    rank = None
    if hits:
        p, q = hits[0][2]
        if not (p % 2 == q % 2 == 1 and p*q == n):
            raise ValueError(f"{case['id']}: expected two odd factors")
        rank = str((p + q) // 2 - isqrt(n - 1))
    if rank != case["fermat_rank"]:
        raise ValueError(f"{case['id']}: expected Fermat rank {case['fermat_rank']}, got {rank}")
    # Each existing branch calls fourth_root twice; each fourth root uses two isqrts.
    branch_reads = len(BRANCHES) * len(DENOMINATORS)
    first_scale = hits[0][0] if hits else None
    return {
        "id": case["id"],
        "bits": n.bit_length(),
        "hits": locations,
        "factors": factors,
        "remaining": [] if hits else [str(n)],
        "fermat_rank": rank,
        "branch_reads": branch_reads,
        "recognizer_isqrts": 4 * branch_reads,
        "projection_gcds": gcd_checks,
        "isqrts_through_first_successful_scale": (
            4 * len(BRANCHES) * (DENOMINATORS.index(first_scale) + 1) if hits else None
        ),
    }


def main():
    cases = json.loads(FIXTURE.read_text())
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", choices=[case["id"] for case in cases], help="replay one control")
    args = parser.parse_args()
    for case in cases:
        if args.case is None or case["id"] == args.case:
            print(json.dumps(verify_case(case)))


if __name__ == "__main__":
    main()
