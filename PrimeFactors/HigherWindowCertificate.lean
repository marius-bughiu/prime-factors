import PrimeFactors.HigherDivisorWindow

namespace PrimeFactors.HigherWindowCertificate

open Polynomial

/-- Test the integer Taylor coefficients directly from the supplied row. -/
def jetChecks {r : ℕ} (v : Fin r → ℤ) (n depth : ℕ) (t : ℤ) : Prop :=
  ∀ j : Fin depth, (n:ℤ)^(depth-j.val) ∣
    ∑ i, v i * (i.val.choose j.val : ℤ) * t^(i.val-j.val)

/-- Every residue is checked with the actual signed coefficients. -/
def rootChecks {r : ℕ} (v : Fin r → ℤ) (m : ℕ) : Prop :=
  ∀ k : Fin m, (∑ i, v i*(k.val:ℤ)^i.val) % (m:ℤ) ≠ 0

private theorem no_integer_root {r m : ℕ} {v : Fin r → ℤ} (hm : 0 < m)
    (checked : rootChecks v m) (x : ℤ) : (ofFn r v).eval x ≠ 0 := by
  intro hz
  have mp : 0 < (m:ℤ) := by exact_mod_cast hm
  let y := x % (m:ℤ)
  have y0 : 0 ≤ y := Int.emod_nonneg _ mp.ne'
  have ym : y < m := Int.emod_lt_of_pos _ mp
  let k : Fin m := ⟨y.toNat, by omega⟩
  have cast : (k.val:ℤ) = y := Int.toNat_of_nonneg y0
  have fail := checked k
  rw [cast, ← HigherDivisorWindow.eval_coeff] at fail
  apply fail
  have eq : x ≡ y [ZMOD (m:ℤ)] := (Int.mod_modEq x (m:ℤ)).symm
  have diff := (Int.modEq_iff_dvd.mp eq).trans (Polynomial.sub_dvd_eval_sub y x (ofFn r v))
  rw [hz, sub_zero] at diff
  exact Int.emod_eq_zero_of_dvd diff

/-- A checked row and finite modular root table exclude all natural divisors in
the closed interval. The offset is signed and a divisor can lie on either side of c. -/
theorem excludes {r n c W L U depth m : ℕ} {v : Fin r → ℤ} {t H : ℤ}
    (hn : n%2=1) (hc : c%2=1) (anchor : (n:ℤ) ∣ (c:ℤ)+2*t)
    (jets : jetChecks v n depth t) (measured : HigherDivisorWindow.height v W = H)
    (small : H < (L:ℤ)^depth) (left : c≤L+2*W) (right : U≤c+2*W)
    (hm : 0<m) (miss : rootChecks v m) (d : ℕ) (lo : L≤d) (hi : d≤U) : ¬ d∣n := by
  intro hd
  have odd := Nat.odd_iff.mpr hn
  have unit : IsCoprime (2:ℤ) (n:ℤ) := by exact_mod_cast (Nat.coprime_two_left.mpr odd).isCoprime
  obtain ⟨q,hq⟩ := hd
  obtain ⟨k,hk⟩ := (Nat.odd_mul.mp (hq ▸ odd)).1
  have dz : (d:ℤ) ∣ (n:ℤ) := by exact_mod_cast (show d∣n from ⟨q,hq⟩)
  let x := ((d:ℤ)-c)/2
  have pos : (d:ℤ)=(c:ℤ)+2*x := by dsimp [x]; omega
  have near : |x|≤(W:ℤ) := abs_le.mpr (by omega)
  have translated : HigherDivisorWindow.Jets depth n t (ofFn r v) := by
    intro j
    rw [HigherDivisorWindow.jet_coeff]
    exact jets j
  have bound := pow_le_pow_left₀ (Int.natCast_nonneg L) (by exact_mod_cast lo : (L:ℤ)≤d) depth
  apply no_integer_root hm miss x
  exact HigherDivisorWindow.root_of_divisor translated dz
    (QuarticDivisorWindow.progression_offset unit anchor dz pos) near (measured ▸ small.trans_le bound)

end PrimeFactors.HigherWindowCertificate
