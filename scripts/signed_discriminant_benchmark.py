"""Run fixed discriminant schedules and certify the public winning torus power."""

from time import perf_counter

from experiments.signed_discriminant_menu import MODES, compare, jacobi, prime_powers, slope
from scripts.factor import verify_file


def power_receipt(n, row, smooth, path):
    d, stage = row["winner"], row["checkpoint"]
    divisor = int(row["divisor"])
    t = slope(n, d)
    sign = jacobi(d, n)
    inverse = pow((t*t-d) % n, -1, n)
    u = ((t*t+d)*inverse % n, 2*t*inverse % n)
    factors = []
    for degree in prime_powers(smooth):
        if stage == 0:
            break
        factors.append(degree)
        if degree == stage:
            break
    exponent = n-sign
    for degree in factors:
        exponent *= degree
    lines = ["import PrimeFactors.JacobiSeparation", "import Mathlib.Tactic.NormNum.LegendreSymbol",
             "namespace PrimeFactors.Generated.SignedDiscriminant", f"private abbrev n : ℕ := {n}",
             f"private abbrev D : ZMod n := {d}",
             f"private abbrev u : (ZMod n) × (ZMod n) := ({u[0]},{u[1]})",
             "private theorem z0 : quadraticPower D u 0 = (1,0) := by rw [quadraticPower]; rfl"]
    a, b, degree = 1, 0, 0
    for i, bit in enumerate(bin(exponent)[2:]):
        previous_degree = degree
        point = f"(({a},{b}) : (ZMod n) × (ZMod n))"
        square = f"(quadraticProduct D {point} {point})"
        degree = 2*degree + int(bit)
        a, b = (a*a+d*b*b) % n, (2*a*b) % n
        if bit == "1":
            a, b = (a*u[0]+d*b*u[1]) % n, (a*u[1]+b*u[0]) % n
        expression = square if bit == "0" else f"quadraticProduct D {square} u"
        choice = "if_pos" if bit == "0" else "if_neg"
        lines.extend([f"private theorem z{i+1} : quadraticPower D u {degree} = ({a},{b}) := by",
                      f"  calc quadraticPower D u {degree} = {expression} := by",
                      f"         rw [quadraticPower, dif_neg (by decide : ¬{degree}=0),"
                      f" show {degree}/2={previous_degree} by decide, z{i}, {choice} (by decide)]",
                      f"       _ = ({a},{b}) := by decide +kernel"])
    # The numeric gcd is the public one. Checking the signed exponent uses
    # the Jacobi symbol over N, without asking for either hidden Legendre sign.
    prefix = " * ".join(str(v) for v in factors) or "1"
    start = "n-1" if sign == 1 else "n+1"
    lines += ["theorem checked :",
              f"    jacobiSym {d} n = ({sign} : ℤ) ∧",
              f"    (({t}^2-D)*{inverse} : ZMod n) = 1 ∧",
              f"    u = ((({t}^2+D)*{inverse} : ZMod n), (2*{t}*{inverse} : ZMod n)) ∧",
              f"    (2*(quadraticPower D u (({start})*({prefix}))).1-2).val.gcd n = {divisor} ∧",
              f"    Nat.Prime {divisor} ∧ Nat.Prime {n//divisor} ∧ {divisor}*{n//divisor}=n := by",
              "  refine ⟨by norm_num [n], by decide +kernel, by decide +kernel, ?_,"
              " by norm_num1, by norm_num1, rfl⟩",
              f"  change (2*(quadraticPower D u {exponent}).1-2).val.gcd n = {divisor}",
              f"  rw [z{exponent.bit_length()}]", "  decide +kernel",
              "#print axioms checked", "end PrimeFactors.Generated.SignedDiscriminant"]
    path.write_text("\n".join(lines) + "\n")
    begin = perf_counter()
    verify_file(path, "PrimeFactors.Generated.SignedDiscriminant.checked")
    return dict(proof=f"proofs/{path.name}", seconds=perf_counter()-begin)


def signed_discriminant_case(case, proof, agree, certify_split):
    n = int(case["n"])
    begin = perf_counter()
    reports = compare(n, budget=case["trial_cap"], smooth=case["smooth_bound"])
    total_search_seconds = perf_counter() - begin
    for mode, check in case["checks"].items():
        agree(dict(id=case["id"], **check), reports[mode], check)
    successful = next((mode for mode in MODES if reports[mode]["divisor"]), None)
    agree(case, {"certified_method": successful}, ["certified_method"])
    divisor = int(reports[successful]["divisor"]) if successful else None
    work = dict(trial_cap=case["trial_cap"], smooth_bound=case["smooth_bound"], modes=reports,
                primary_outcome=reports["menu"]["outcome"], certified_method=successful,
                total_search_seconds=total_search_seconds)
    result = certify_split(case, proof, divisor, total_search_seconds, "signed_discriminant_menu", work)
    if "receipt_mode" in case:
        mode = case["receipt_mode"]
        result["signed_discriminant_receipt"] = power_receipt(
            n, reports[mode], case["smooth_bound"], proof.with_name(f"{proof.stem}-{mode}-power.lean"))
    return result
