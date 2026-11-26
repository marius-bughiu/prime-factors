"""Compare public translated coefficients, their normalized derivative, and Gaussian traces."""

from math import comb, gcd
from time import perf_counter

from experiments import quartic_trace, translated_hasse
from scripts.factor import verify_file


THEOREM = "PrimeFactors.Generated.hasseReadout"


def derivative_search(n, max_index):
    if n < 3 or n % 4 != 3 or max_index < 0:
        raise ValueError("expected N = 3 mod 4 and a nonnegative index budget")
    index = (n - 1) // 2
    column = (n + 1) // 4
    work = dict(index=str(index), column=str(column), max_index=max_index, binomials=0,
                coefficient_gcds=0, coefficient_bits=0, residue=None, gcd=None)
    if index > max_index:
        return None, dict(work, outcome="index_limit")
    value = comb(index, column)
    residue = value % n
    divisor = gcd(n, residue)
    factor = divisor if 1 < divisor < n else None
    work.update(binomials=1, coefficient_gcds=1, coefficient_bits=value.bit_length(),
                residue=residue, gcd=divisor, outcome="coefficient_divisor" if factor else "no_split")
    return factor, work


def gaussian_search(n, max_positions, max_selector):
    # The complete integer sum has magnitude at most N. The evaluator's
    # signed residues recover it exactly at the chosen precision.
    bits = n.bit_length()
    raw = quartic_trace.search(n, max_positions, max_selector, bits=bits)
    previous_factor = raw.pop("factor")
    work = dict(raw, signed_traces=None, direction=None, normalization_gcds=0)
    if work["residues"] is None:
        return previous_factor, work
    modulus = 1 << (bits + 2)
    first, twisted = (r if 2*r < modulus else r - modulus for r in work["residues"])
    common = gcd(first, twisted)
    work.update(signed_traces=[first, twisted], normalization_gcds=1)
    if common:
        a, b = abs(first) // common, abs(twisted) // common
        work["direction"] = [a, b]
        factor = a*a + b*b
        if 1 < factor < n and n % factor == 0:
            return factor, dict(work, outcome="trace_divisor")
    return None, dict(work, outcome="no_split")


SHIFT_FORMULA = """private theorem readExplicit (n : ℕ) (c : ℤ) :
    let h := (n-1)/2
    reading n c = ∑ j ∈ Finset.range (h+1),
      (((j+2*h).choose (2*h) : ℕ) : ℤ) *
      (if 2 ∣ h+j then (-1 : ℤ)^(h-(h+j)/2) * (h.choose ((h+j)/2) : ℤ) else 0) * c^j := by
  dsimp only
  let h := (n-1)/2
  change value h c = _
  rw [← shift_eval, eval_eq_sum_range' (Nat.lt_succ_of_le (shift_degree h))]
  apply Finset.sum_congr rfl
  intro j _
  rw [shiftPoly, hasseDeriv_coeff, show j+2*h=h+(h+j) by omega, cubic_coeff]
"""


def _join_claims(claims, proofs):
    if len(claims) == 1:
        return f"theorem {THEOREM} : {claims[0]} := {proofs[0]}\n"
    return (f"theorem {THEOREM} :\n    " + " ∧\n    ".join(claims) +
            " :=\n  ⟨" + ",\n   ".join(proofs) + "⟩\n")


def _arithmetic_source(n, mode, w):
    claims, proofs = [], []
    settings = "set_option maxRecDepth 8192\n"
    if mode == "shifted":
        prefix = ("import PrimeFactors.TranslatedHasse\n"
                  "open Polynomial PrimeFactors.TranslatedHasse\n" + settings + SHIFT_FORMULA)
        for reading in w["readings"]:
            c, residue, divisor = (reading[key] for key in ("shift", "residue", "gcd"))
            claims.extend((f"reading {n} ({c}) % {n} = {residue}", f"Nat.gcd {n} {residue} = {divisor}"))
            proofs.extend(("by rw [readExplicit, Nat.choose_eq_fast_choose]; decide +kernel",
                           "by decide +kernel"))
    elif mode == "derivative":
        prefix = ("import PrimeFactors.HasseBinomialDerivative\n"
                  "open PrimeFactors.HasseBinomialDerivative\n" + settings)
        claims.extend((f"entry {n} % {n} = {w['residue']}", f"Nat.gcd {n} {w['residue']} = {w['gcd']}"))
        proofs.extend(("by rw [entry, Nat.choose_eq_fast_choose]; decide +kernel", "by decide +kernel"))
    else:
        prefix = ("import PrimeFactors.GaussianTraceRecovery\nimport Mathlib.Tactic.NormNum.LegendreSymbol\n"
                  "open PrimeFactors\n" + settings)
        first, twisted = w["signed_traces"]
        for selector, residue in ((1, first), (w["selector"], twisted)):
            term = f"jacobiSym ((x : ℤ)*((x : ℤ)^2-({selector}))) {n}"
            claims.append(f"QuarticTrace.complete {n} ({selector}) = ({residue})")
            proofs.append(f"""by
      unfold QuarticTrace.complete
      change ∑ x : Fin {n}, jacobiSym (x.val * ((x.val : ℤ)^2-({selector}))) {n} = ({residue})
      rw [Fin.sum_univ_eq_sum_range (fun x : ℕ => {term})]
      norm_num [Finset.sum_range_succ]""")
        a, b = w["direction"]
        claims.append(f"GaussianTraceRecovery.direction ({first}) ({twisted}) = {a*a+b*b}")
        proofs.append("by decide +kernel")
    return prefix + "\n" + _join_claims(claims, proofs) + f"\n#print axioms {THEOREM}\n"


def hasse_case(case, proof, agree, certify_split):
    n = int(case["n"])
    mode = case["mode"]
    start = perf_counter()
    if mode == "shifted":
        factor, work = translated_hasse.search(n, shifts=case["shifts"], max_index=case["max_index"])
    elif mode == "derivative":
        factor, work = derivative_search(n, case["max_index"])
    elif mode == "gaussian":
        factor, work = gaussian_search(n, case["max_positions"], case["max_selector"])
    else:
        raise ValueError(f"unknown coefficient mode {mode}")
    elapsed = perf_counter() - start
    agree(dict(id=case["id"], **case["checks"]), work, case["checks"])
    work["mode"] = mode
    result = certify_split(case, proof, factor, elapsed, "hasse", work)
    if case.get("certify_readings"):
        relation = proof.with_name(f"{proof.stem}-reading.lean")
        relation.write_text(_arithmetic_source(n, mode, work))
        start = perf_counter()
        verify_file(relation, THEOREM)
        result["coefficient_proof"] = dict(proof=f"proofs/{relation.name}", theorem=THEOREM,
                                           verification_seconds=perf_counter()-start)
    return result
