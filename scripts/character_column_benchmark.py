"""Replay the bounded character search and certify the selected column's exact gcd."""
from time import perf_counter

from experiments.character_divisor_column import DISCRIMINANTS, search
from scripts.factor import render_certificate, verify_file


COLUMN_LEMMA = """
namespace PrimeFactors.Generated

/-- The same signed, wheel-filtered integers between the two inclusive bounds. -/
private noncomputable def scannedColumn (lo hi period : ℕ) (d sign : ℤ) : ℕ :=
  FixedDivisorSignatures.column (Finset.Icc lo hi)
    (fun x => decide (x.Coprime period ∧ jacobiSym d x=sign))

private theorem columnBit {p lo hi period : ℕ} (prime : p.Prime) (lower : lo≤p)
    (upper : p≤hi) (positive : 0<lo) (short : hi<2*p) (d sign : ℤ) :
    p ∣ scannedColumn lo hi period d sign ↔ p.Coprime period ∧ jacobiSym d p=sign := by
  have unique (x : ℕ) (inside : x ∈ Finset.Icc lo hi) (divides : p ∣ x) : x=p := by
    obtain ⟨left,right⟩ := Finset.mem_Icc.mp inside
    exact Nat.eq_of_dvd_of_lt_two_mul (by omega) divides (by omega)
  simpa only [scannedColumn, decide_eq_true_eq] using
    FixedDivisorSignatures.column_dvd prime (Finset.mem_Icc.mpr ⟨lower,upper⟩) unique
      (fun x : ℕ => decide (x.Coprime period ∧ jacobiSym d x=sign))

private theorem scanned_gcd {n p q lo hi period : ℕ} {d sign : ℤ}
    (pair : p*q=n) (pp : p.Prime) (qp : q.Prime) (positive : 0<lo)
    (pl : lo≤p) (pu : p≤hi) (ql : lo≤q) (qu : q≤hi)
    (shortP : hi<2*p) (shortQ : hi<2*q) (cop : p.Coprime period)
    (selected : jacobiSym d p=sign) (other : jacobiSym d q≠sign) :
    (scannedColumn lo hi period d sign).gcd n=p := by
  have hit := (columnBit pp pl pu positive shortP d sign).mpr ⟨cop,selected⟩
  have miss : ¬q ∣ scannedColumn lo hi period d sign :=
    fun h => other ((columnBit qp ql qu positive shortQ d sign).mp h).2
  rw [←pair,Nat.gcd_comm,Nat.mul_comm p q]
  exact Nat.gcd_mul_of_coprime_of_dvd (qp.coprime_iff_not_dvd.mpr miss) hit
"""


def column_receipt(n, run, factor):
    other = n//factor
    pair = sorted([factor,other])
    low, high = int(run['lower']), int(run['upper'])
    period, symbol, sign = run['period'], f"({run['d']})", f"({run['sign']})"
    base = 1 << ((n.bit_length()-1)//2)
    if run['mode'] == 'clipped':
        endpoints = f'{low} = max {base} (({n}-1)/(2*{base}-1)+1) ∧ {high} = min (2*{base}-1) ({n}/{base})'
    else:
        endpoints = f'{low} = {base} ∧ {high} = 2*{base}-1'
    return ('import PrimeFactors.CharacterDivisorColumn\n'
            'import Mathlib.Tactic.NormNum.LegendreSymbol\n' + render_certificate(n, pair)
            + COLUMN_LEMMA + f"""
theorem character_factorization :
    ExactFactorization {n} {pair} ∧ jacobiSym {symbol} {n} = -1 ∧
    (jacobiSym {symbol} {factor} = {sign} ∧ {low}≤{factor} ∧ {factor}≤{high}) ∧
    ({base}=2^(Nat.log2 {n}/2) ∧ {period}=Nat.lcm {run['wheel']} (4*({symbol}:ℤ).natAbs) ∧ {endpoints}) ∧
    Nat.gcd {int(run['product'])} {n} = {factor} ∧
    Nat.gcd (scannedColumn {low} {high} {period} {symbol} {sign}) {n} = {factor} := by
  have selected : jacobiSym {symbol} {factor} = {sign} := by norm_num
  refine ⟨factorization, ?_, ⟨selected,by decide,by decide⟩, ?_, by decide +kernel, ?_⟩
  · norm_num
  · have bits : Nat.log2 {n} = {n.bit_length()-1} := Nat.eq_of_le_of_lt_succ
      ((Nat.le_log2 (by decide : {n} ≠ 0)).mpr (by decide +kernel))
      ((Nat.log2_lt (by decide : {n} ≠ 0)).mpr (by decide +kernel))
    rw [bits]
    decide +kernel
  · exact scanned_gcd (p:={factor}) (q:={other}) (by decide +kernel)
      prime_{factor} prime_{other} (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel) selected (by norm_num)

#print axioms character_factorization
end PrimeFactors.Generated
""")


def character_column_case(case, proof, agree, certify_split):
    n = int(case['n'])
    start = perf_counter()
    run = search(n, wheel=case['wheel'], clip=case['clip'], max_work=case['max_work'],
                 discriminants=case.get('discriminants',DISCRIMINANTS))
    elapsed = perf_counter()-start
    factor = run.pop('factor')
    run['wheel'] = case['wheel']
    run['found_divisor'] = str(factor) if factor is not None else None
    agree(dict(id=case['id'], **case['checks']),run,case['checks'])
    if run['outcome'] != 'column_gcd':
        return certify_split(case,proof,factor,elapsed,'character_column',run)

    result = certify_split(case,proof,None,elapsed,'character_column',run)
    start = perf_counter()
    proof.write_text(column_receipt(n,run,factor))
    check = perf_counter()
    verify_file(proof,'PrimeFactors.Generated.character_factorization')
    result.update(factors=list(map(str,sorted((factor,n//factor)))), remaining=[], status='complete',
                  verified=True, verification_seconds=perf_counter()-check, certificate_seconds=perf_counter()-start)
    run['column_verified'] = True
    return result
