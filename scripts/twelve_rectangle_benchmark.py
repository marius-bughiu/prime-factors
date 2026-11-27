"""Check the rectangle schedules and certify the chosen schedule's actual split."""
from time import perf_counter

from experiments.short_pascal_row import interval
from experiments.twelve_rectangle import search
from scripts.factor import verify_file


def rectangle_case(case, proof, agree, certify_split):
    n = int(case["n"])
    height, width = case["baby_count"], case["giant_count"]
    first = interval(n)[0] | 1
    modes = ("squares", "twelve", "expanded_twelve")
    runs = {}
    for mode in modes:
        before = perf_counter()
        divisor, counters, source, witness = search(n, height, width, mode)
        seconds = perf_counter()-before
        if divisor is not None and (not 1 < divisor < n or n % divisor):
            raise ValueError("invalid rectangle divisor")
        radius = height+2 if mode == "expanded_twelve" else height
        row = dict(**counters, source=source, divisor=str(divisor) if divisor else None,
                   witness=[str(z) for z in witness], seconds=seconds,
                   guaranteed_odd_candidates=2*radius*width, last_odd=str(first+4*radius*width-2))
        checks = case["checks"][mode]
        agree(dict(id=case["id"]+"."+mode, **checks), row, checks)
        runs[mode] = row
    primary = case.get("primary", "expanded_twelve")
    row = runs[primary]
    work = dict(primary=primary, first_odd=str(first), baby_count=height, giant_count=width, runs=runs)
    result = certify_split(case, proof, int(row["divisor"]) if row["divisor"] else None,
                           row["seconds"], "twelve_rectangle", work)
    if row["source"] in ("key difference", "branch") and primary != "squares":
        x, y = row["witness"][:2]
        divisor = row["divisor"]
        if row["source"] == "key difference":
            claim = (f"Nat.gcd {n} (den x * den y).natAbs = 1 ∧ "
                     f"Nat.gcd {n} (num x * den y - num y * den x).natAbs = {divisor}")
        else:
            i = int(row["witness"][2])
            claim = f"Nat.gcd {n} (imageDen x {i} * y - imageNum x {i}).natAbs = {divisor}"
        receipt = proof.with_name(proof.stem+"-gcd.lean")
        theorem = "PrimeFactors.Generated.Rectangle.gcd"
        receipt.write_text("import PrimeFactors.TwelveRectangle\n"
                           "open PrimeFactors.TwelveResidueCollision\n"
                           f"private def x : ℤ := {x}\nprivate def y : ℤ := {y}\n"
                           f"theorem {theorem} : {claim} := by decide +kernel\n#print axioms {theorem}\n")
        verify_file(receipt, theorem)
        result["rectangle_witness"] = f"proofs/{receipt.name}"
    return result
