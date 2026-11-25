import PrimeFactors.CenteredBinomialDivisorWindow
import PrimeFactors.BinomialWindowCertificate

namespace PrimeFactors.CenteredBinomialCertificate

open Polynomial Finset CenteredBinomialDivisorWindow

/-- Exact coordinate maximum on the integer interval from -R through R for R>0. -/
noncomputable def weight (r i : ℕ) := if i=0 then 1 else Nat.fast_choose (r+i-1) i

theorem abs_le_weight {r : ℕ} {x : ℤ} (i : ℕ) (near : |x|≤(r:ℤ)) :
    |signedChoose x i|≤(weight r i:ℤ) := by
  by_cases zero : i=0
  · subst i
    simp [signedChoose, weight]
  · have ax : x.natAbs≤r := by exact_mod_cast ((Int.natCast_natAbs x).trans_le near)
    rw [weight,if_neg zero,←Nat.choose_eq_fast_choose]
    unfold signedChoose
    split_ifs
    · rw [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,abs_of_nonneg (Int.natCast_nonneg _)]
      exact_mod_cast Nat.choose_le_choose i (show x.natAbs+i-1≤r+i-1 by omega)
    · rw [abs_of_nonneg (Int.natCast_nonneg _)]
      exact_mod_cast Nat.choose_le_choose i (show x.natAbs≤r+i-1 by omega)

noncomputable def height {k : ℕ} (v : Fin (k+1) → ℤ) (r : ℕ) := ∑ i, |v i| * (weight r i.val:ℤ)

theorem excludes {k n first r depth modulus : ℕ} {v w : Fin (k+1) → ℤ} {t h : ℤ}
    (hn : n%2=1) (oddFirst : first%2=1) (anchor : (n:ℤ)∣(first+2*r:ℕ)+2*t)
    (gcd : n.Coprime k.factorial) (samples : BinomialWindowCertificate.sampleChecks v w)
    (jets : HigherWindowCertificate.jetChecks w n depth t) (measured : height v r=h)
    (small : h<(first:ℤ)^depth) (hm : 0<modulus) (miss : HigherWindowCertificate.rootChecks w modulus)
    (d : ℕ) (lo : first≤d) (hi : d≤first+4*r) : ¬d∣n := by
  intro hd
  have odd := Nat.odd_iff.mpr hn
  have unit : IsCoprime (2:ℤ) (n:ℤ) := (Nat.coprime_two_left.mpr odd).isCoprime
  obtain ⟨q,hq⟩ := hd
  have dz : (d:ℤ)∣(n:ℤ) := by exact_mod_cast (show d∣n from ⟨q,hq⟩)
  obtain ⟨a,ha⟩ := (Nat.odd_mul.mp (hq ▸ odd)).1
  let x := ((d:ℤ)-(first+2*r:ℕ))/2
  have pos : (d:ℤ)=(first+2*r:ℕ)+2*x := by dsimp only [x]; omega
  have near : |x|≤(r:ℤ) := by rw [abs_le]; dsimp only [x]; omega
  have convert := BinomialWindowCertificate.same_polynomial samples
  have translated : HigherDivisorWindow.Jets depth n t (BinomialDivisorWindow.cleared k v) := by
    intro j
    rw [convert,HigherDivisorWindow.jet_coeff]
    exact jets j
  have dvd := HigherDivisorWindow.dvd_eval_of_jets translated dz
    (QuarticDivisorWindow.progression_offset unit anchor dz pos)
  rw [eval_cleared] at dvd
  have hit : (d:ℤ)^depth ∣ value v x := (gcd.isCoprime.of_isCoprime_of_dvd_left dz).pow_left.dvd_of_dvd_mul_left dvd
  have bound : |value v x| ≤ height v r := by
    apply (abs_sum_le_sum_abs ..).trans
    apply sum_le_sum
    intro i _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_le_weight i.val near) (abs_nonneg _)
  apply HigherWindowCertificate.no_integer_root hm miss x
  rw [←convert,eval_cleared,Int.eq_zero_of_abs_lt_dvd hit (bound.trans_lt
    (measured.trans_lt (small.trans_le (pow_le_pow_left₀ (Int.natCast_nonneg _) (by exact_mod_cast lo) _)))),mul_zero]

end PrimeFactors.CenteredBinomialCertificate
