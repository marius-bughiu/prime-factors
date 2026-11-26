"""Replay the selected gcd and certify its entire nested-exponent search range."""

from time import perf_counter

from experiments.square_root_power_chain import search
from scripts.factor import verify_file


THEOREM = "PrimeFactors.Generated.powerChain"


def receipt_source(n, work):
    """Build a kernel-checkable modular proof from the input and measured endpoint."""
    n = int(n)
    base = int(work["base"])
    first = int(work["initial_exponent"])
    height = int(work["height"])
    if work["mode"] == "powers-of-two":
        parameters = "first = 1 ∧ 2^(2*height) ≤ input ∧ input < 2^(2*height+2)"
    elif work["mode"] == "product-minus-one":
        parameters = "first % 2 = 1 ∧ first*2^height+1 = input"
    else:
        raise ValueError("unknown exponent chain")

    header = f"""import PrimeFactors.PowerChainReceipt

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 8192

namespace PrimeFactors.Generated

open LastPowerGCD PowerChainReceipt

private abbrev input : ℕ := {n}
private abbrev base : ℕ := {base}
private abbrev first : ℕ := {first}
private abbrev height : ℕ := {height}

private theorem base_spec : base = input.sqrt :=
  Nat.eq_sqrt'.mpr (by decide +kernel)
"""

    def power_fact(name, index, residue):
        exponent = first << index
        return f"""
private theorem {name} : (base : ZMod input)^(first*2^{index}) = {residue} := by
  change ({base} : ZMod {n})^{exponent} = {residue}
  reduce_mod_char
"""

    whole = work["first_whole"]
    no_split = "∀ i ≤ height, ¬ proper input (reading input input.sqrt (first*2^i))"
    if whole == 0:
        extra = power_fact("full", 0, 1)
        statement = no_split
        derivation = """intro i _
  apply empty_of_first_one (e := fun j => first*2^j) (input.sqrt : ℤ)
    (fun j => doubling first 0 j (Nat.zero_le j))
  rw [← base_spec]
  simpa only [Int.cast_natCast] using full"""
    else:
        index = int(work["checked_index"])
        residue = int(work["checked_residue"])
        gcd_value = int(work["checked_gcd"])
        if whole is not None and whole != index + 1:
            raise ValueError("the first whole value must immediately follow the checked index")
        if whole is None and index != height:
            raise ValueError("a chain without a whole value must reach its horizon")
        extra = power_fact("reduced", index, residue)
        extra += f"""
private theorem checked : reading input input.sqrt (first*2^{index}) = {gcd_value} :=
  endpoint (Nat.eq_sqrt'.mp base_spec) reduced (by decide +kernel)
"""
        statement = f"reading input input.sqrt (first*2^{index}) = {gcd_value}"
        derivation = "exact checked"
        if whole is not None:
            extra += power_fact("full", whole, 1)
            extra += f"""
private theorem whole_reading : reading input input.sqrt (first*2^{whole}) = input := by
  apply (whole_iff ..).mpr
  rw [← base_spec]
  simpa only [Int.cast_natCast] using full
"""
            statement += f" ∧ reading input input.sqrt (first*2^{whole}) = input"
            derivation = "exact ⟨checked, whole_reading⟩"
        if gcd_value == 1 and whole is None:
            statement += " ∧ ∀ i ≤ height, reading input input.sqrt (first*2^i) = 1"
            derivation = "exact ⟨checked, no_split_at_horizon checked⟩"
        elif gcd_value == 1:
            statement = f"({statement}) ∧ ({no_split})"
            derivation = f"""refine ⟨⟨checked, whole_reading⟩, ?_⟩
  intro i bound hit
  have equiv := selected (n := input) (by decide) (input.sqrt : ℤ)
    (fun j => first*2^j) (doubling first) (k := {index}) (H := height) (by decide)
  have active : ((input.sqrt : ℤ) : ZMod input)^(first*2^{index}) ≠ 1 := by
    rw [← base_spec, Int.cast_natCast, reduced]
    decide +kernel
  have bad := (equiv active (Or.inr ((whole_iff ..).mp whole_reading))).mp ⟨i, bound, hit⟩
  rw [checked] at bad
  exact (Nat.lt_irrefl 1) bad.1"""

    return header + extra + f"""
theorem powerChain : ({parameters}) ∧ base = input.sqrt ∧ ({statement}) := by
  refine ⟨by decide +kernel, base_spec, ?_⟩
  {derivation}

#print axioms powerChain

end PrimeFactors.Generated
"""


def power_chain_case(case, proof, agree, certify_split):
    start = perf_counter()
    factor, work = search(int(case["n"]), case["mode"])
    elapsed = perf_counter() - start
    if factor is not None:
        work["outcome"] = "proper_gcd"
    elif work["first_whole"] is None:
        work["outcome"] = "terminal_unit"
    else:
        work["outcome"] = "whole_without_split"
    agree(dict(id=case["id"], **case["checks"]), work, case["checks"])
    result = certify_split(case, proof, factor, elapsed, "power_chain", work)
    receipt = proof.with_name(f"{proof.stem}-chain.lean") if factor is not None else proof
    receipt.write_text(receipt_source(case["n"], work))
    start = perf_counter()
    verify_file(receipt, THEOREM)
    result["power_chain_proof"] = dict(
        proof=f"proofs/{receipt.name}", theorem=THEOREM, verification_seconds=perf_counter() - start
    )
    return result
