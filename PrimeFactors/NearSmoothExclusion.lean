import PrimeFactors.NearSmoothSumPopulation
import PrimeFactors.SmoothCenterSpacing

/-! Cover all smooth-center sum bands with public exclusions of smaller
divisors. Each boundary is checked by integer products without computing a
square root in the certificate. -/

namespace PrimeFactors.NearSmoothExclusion

open SmoothSumSelector NearSmoothSumPopulation

set_option exponentiation.threshold 4096

def smallest (n : ℕ) : ℕ := max (2^1023) ((n-1)/(2^1024-1)+1)

noncomputable def viable (n e : ℕ) : List ℕ := (List.range 647).filter fun b =>
  let c := SmoothCenterSpacing.fastCenter b
  let l := smallest n
  decide (4*n ≤ (c+e)^2 ∧ l*(c-e) ≤ l^2+n)

private theorem lower_bound {p q : ℕ} (lo : 2^1023≤p) (hi : q<2^1024) :
    smallest (p*q) ≤ p := by
  apply max_le lo
  have cap : 0<(2:ℕ)^1024-1 := by decide +kernel
  have big := Nat.mul_le_mul_left p (show q≤2^1024-1 by omega)
  have product : 0<p*q ∨ q=0 := by
    by_cases h : q=0
    · exact Or.inr h
    · exact Or.inl (Nat.mul_pos (by omega) (by omega))
  rcases product with pos|rfl
  · exact (Nat.div_lt_iff_lt_mul cap).mpr (by omega)
  · simp; omega

/-- If z is below both factors, the hyperbola gives an upper sum bound. -/
private theorem below_both {p q z : ℕ} (zp : z≤p) (zq : z≤q) :
    z*(p+q) ≤ z^2+p*q := by
  obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le zp
  obtain ⟨v,rfl⟩ := Nat.exists_eq_add_of_le zq
  nlinarith only [Nat.zero_le (u*v)]

private theorem between {p q z : ℕ} (pz : p≤z) (zq : z≤q) :
    z^2+p*q ≤ z*(p+q) := by
  obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le pz
  obtain ⟨v,rfl⟩ := Nat.exists_eq_add_of_le zq
  nlinarith only [Nat.zero_le (u*v)]

theorem viable_mem {p q b e : ℕ} (ord : p≤q) (lo : 2^1023≤p) (hi : q<2^1024)
    (hb : b<647) (lower : candidate b ≤ p+q+e) (upper : p+q ≤ candidate b+e) :
    b ∈ viable (p*q) e := by
  let l := smallest (p*q)
  have lp : l≤p := lower_bound lo hi
  have low := (Nat.mul_le_mul_left l (show candidate b-e≤p+q by omega)).trans
    (below_both lp (lp.trans ord))
  have discr := Nat.pow_le_pow_left upper 2
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le ord
  have high : 4*(p*q) ≤ (p+q)^2 := by rw [hd]; nlinarith only [Nat.zero_le (d^2)]
  apply List.mem_filter.mpr
  refine ⟨List.mem_range.mpr hb,?_⟩
  simpa only [SmoothCenterSpacing.fast_correct hb,decide_eq_true_eq] using And.intro (high.trans discr) low

/-- These inequalities check that every smaller factor with this sum lies
inside the measured divisor interval. Factor-width clipping is permitted. -/
def Covers (n c e l u : ℕ) : Prop :=
  (l≤2^1023 ∨ (l-1)*(2^1024-1)<n ∨
      (l-1)^2≤n ∧ (l-1)*(c+e)<(l-1)^2+n) ∧
  (n<(u+1)^2 ∨ (u+1)^2+n < (u+1)*(c-e))

noncomputable instance (n c e l u : ℕ) : Decidable (Covers n c e l u) := by unfold Covers; infer_instance

theorem in_window {p q c e l u : ℕ} (ord : p≤q) (lo : 2^1023≤p) (hi : q<2^1024)
    (lower : c≤p+q+e) (upper : p+q≤c+e) (checked : Covers (p*q) c e l u) :
    l≤p ∧ p≤u := by
  obtain ⟨left,right⟩ := checked
  constructor
  · by_contra! fail
    have pz : p≤l-1 := by omega
    rcases left with h|h|⟨low,high⟩
    · omega
    · exact (not_lt_of_ge (Nat.mul_le_mul pz (by omega : q≤2^1024-1))) h
    · have zq : l-1≤q := by
        apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
        exact low.trans (by rw [pow_two]; exact Nat.mul_le_mul_right q ord)
      exact (not_lt_of_ge ((between pz zq).trans (Nat.mul_le_mul_left _ upper))) high
  · by_contra! fail
    have zp : u+1≤p := by omega
    rcases right with h|h
    · exact (not_lt_of_ge (by simpa only [pow_two] using Nat.mul_le_mul zp (zp.trans ord))) h
    · have cap := (Nat.mul_le_mul_left (u+1) (show c-e≤p+q by omega)).trans
          (below_both zp (zp.trans ord))
      exact (not_lt_of_ge cap) h

/-- A certificate supplies an exclusion only at geometrically viable
exponents. Each excluded interval covers the entire sum band. -/
theorem excludes {n t : ℕ} (rows : ∀ b∈viable n (2*t), ∃ l u,
    Covers n (candidate b) (2*t) l u ∧ ∀ d, l≤d → d≤u → ¬d∣n)
    {p q : ℕ} (eq : p*q=n) (ord : p≤q) (lo : 2^1023≤p) (hi : q<2^1024) :
    ¬Near (p+q) t := by
  subst n
  rintro ⟨b,hb,upper,lower⟩
  obtain ⟨l,u,cov,absent⟩ := rows b (viable_mem ord lo hi hb lower upper)
  obtain ⟨pl,pu⟩ := in_window ord lo hi lower upper cov
  exact absent p pl pu (dvd_mul_right p q)

end PrimeFactors.NearSmoothExclusion
