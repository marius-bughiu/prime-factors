import PrimeFactors.FactorEndingSeparation
import PrimeFactors.LocalMidpointLanes

/-! Witnesses at the last insufficient precision for distinguishing two
unordered factor endings of an odd product. The sums agree even in ℤ. -/

namespace PrimeFactors.FactorEndingCollisions

open FactorEndingSeparation

/-- Two distinct unordered pairs modulo `2^k` can give the same integer
sum and both realize the given product modulo `2^e`. -/
def Collision (N k e : ℕ) : Prop :=
  ∃ a b c d : ℤ, a*b ≡ (N:ℤ) [ZMOD (2:ℤ)^e] ∧ c*d ≡ (N:ℤ) [ZMOD (2:ℤ)^e] ∧
    a+b=c+d ∧ ¬a ≡ c [ZMOD (2:ℤ)^k] ∧ ¬a ≡ d [ZMOD (2:ℤ)^k]

theorem Collision.not_separates {N k e : ℕ} (h : Collision N k e) : ¬Separates N k e := by
  obtain ⟨a,b,c,d,ab,cd,sum,ac,ad⟩ := h
  intro sep
  exact (sep a b c d ab cd (by rw [sum])).elim ac ad

private theorem half_nonzero (t : ℕ) : ¬ (2:ℤ)^(t+1) ∣ (2:ℤ)^t := by
  intro h
  have h' : (2:ℕ)^(t+1) ∣ 2^t := by exact_mod_cast h
  have := (Nat.pow_dvd_pow_iff_le_right (by decide : 1<(2:ℕ))).mp h'
  omega

private theorem shift_ne (x : ℤ) (t : ℕ) :
    ¬x+2^t ≡ x [ZMOD (2:ℤ)^(t+1)] := by
  intro eq
  exact half_nonzero t (by simpa using Int.modEq_iff_dvd.mp eq.symm)

/-- Shift one factor up by half the suffix modulus and the other down by
the same amount. Only the product changes. -/
private theorem shift {N t e : ℕ} (x y : ℤ)
    (prod : x*y ≡ (N:ℤ) [ZMOD (2:ℤ)^e])
    (change : (2:ℤ)^e ∣ 2^t*(x-y+2^t))
    (other : ¬x+2^t ≡ y [ZMOD (2:ℤ)^(t+1)]) : Collision N (t+1) e := by
  refine ⟨x+2^t,y-2^t,x,y,?_,prod,by ring,shift_ne x t,other⟩
  apply Int.ModEq.trans _ prod
  apply Int.modEq_iff_dvd.mpr
  convert change using 1
  ring

private theorem nonsquare {N t j : ℕ} (lt : j<t)
    (low : (N:ℤ) ≡ 1+2^j [ZMOD (2:ℤ)^(j+1)]) : Collision N (t+1) (t+j) := by
  have width : (2:ℤ)^(j+1) ∣ 2^t := pow_dvd_pow 2 (by omega)
  have near : (2:ℤ)^j ∣ 1-(N:ℤ) := by
    obtain ⟨m,hm⟩ := Int.modEq_iff_dvd.mp low
    refine ⟨2*m-1,?_⟩
    rw [pow_succ] at hm
    linear_combination hm
  apply shift 1 (N:ℤ) (by simp)
  · rw [pow_add]
    exact mul_dvd_mul_left _ (dvd_add near (pow_dvd_pow 2 lt.le))
  · intro same
    have reduced := (same.of_dvd (pow_dvd_pow (2:ℤ) (by omega : j+1≤t+1))).trans low
    have eq : (2:ℤ)^(j+1) ∣ 2^j-2^t := by simpa using Int.modEq_iff_dvd.mp reduced
    exact half_nonzero j (by simpa using dvd_add eq width)

/-- For products ending in 3 modulo 4, k bits can conceal the half-width shift. -/
theorem three {N k : ℕ} (hk : 4≤k) (hn : N%4=3) : Collision N k k := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k≠0 by omega)
  apply nonsquare (j:=1) (by omega)
  exact_mod_cast Int.natCast_modEq_iff.mpr (show N ≡ 3 [MOD 4] from hn)

/-- For products ending in 5 modulo 8 the same shift is invisible up to k+1 bits. -/
theorem five {N k : ℕ} (hk : 4≤k) (hn : N%8=5) : Collision N k (k+1) := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k≠0 by omega)
  apply nonsquare (j:=2) (by omega)
  exact_mod_cast Int.natCast_modEq_iff.mpr (show N ≡ 5 [MOD 8] from hn)

/-- A square root r gives two distinct singleton suffix orbits. The pairs
(r,r) and (r+h,r−h), h=2^(k−1), have products differing by exactly h². -/
theorem one {N k : ℕ} (hk : 4≤k) (hn : N%8=1) : Collision N k (2*k-2) := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k≠0 by omega)
  rw [show 2*(t+1)-2=t+t by omega]
  have base := Int.modEq_iff_dvd.mp (Int.natCast_modEq_iff.mpr (show 1 ≡ N [MOD 8] from hn.symm))
  obtain ⟨r,_,root⟩ := LocalMidpointLanes.lift_eight (D:=(N:ℤ)) (by exact_mod_cast base) (t+t)
  apply shift r r _ _ (shift_ne r t)
  · apply Int.modEq_iff_dvd.mpr
    simpa [pow_two] using (pow_dvd_pow (2:ℤ) (by omega : t+t≤t+t+3)).trans root
  · simp [pow_add]

/-- At one bit below the sufficient precision, every odd product admits
two different suffix orbits with the same sum. -/
theorem predecessor {N k : ℕ} (hk : 4≤k) (odd : Odd N) : Collision N k (depth N k-1) := by
  unfold depth
  split_ifs with h₃ h₅
  · simpa using three hk h₃
  · simpa using five hk h₅
  · rw [show 2*k-1-1=2*k-2 by omega]
    obtain ⟨u,hu⟩ := odd
    exact one hk (by omega)

/-- Exact least precision in the modular model, including every lower and
higher exponent. -/
theorem separates_iff {N k e : ℕ} (hk : 4≤k) (odd : Odd N) :
    Separates N k e ↔ depth N k≤e := by
  constructor
  · intro h
    by_contra! short
    exact (predecessor hk odd).not_separates (mono h (by omega))
  · exact mono (at_depth hk odd)

end PrimeFactors.FactorEndingCollisions
