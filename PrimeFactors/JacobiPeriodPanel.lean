import PrimeFactors.JacobiPeriodCount
import Mathlib.Algebra.Order.Field.Basic

/-! Reusing two unit bases for every proposed period at stride (N−1)/2.
Count ordered pairs with replacement, so the probability statement assumes
independent uniform sampling from the units. -/

namespace PrimeFactors.JacobiPeriodPanel

open Finset JacobiPeriodCount

/-- Both fixed bases pass the public power test at multiplier t. -/
def Passes {G : Type*} [Group G] (z : G × G) (D t : ℕ) : Prop :=
  z.1^(D*t)=1 ∧ z.2^(D*t)=1

/-- A wrong answer at any multiplier is witnessed at a maximal proper divisor
of R, even when the original multiplier exceeds R. -/
theorem false_pass_iff {G : Type*} [Group G] (z : G × G) {D R : ℕ}
    (pos : 0<R) (full : Passes z D R) :
    (∃ t, ¬ R ∣ t ∧ Passes z D t) ↔
      ∃ l ∈ R.primeFactors, Passes z D (R/l) := by
  let m := (orderOf (z.1^D)).lcm (orderOf (z.2^D))
  have test (t) : Passes z D t ↔ m ∣ t := by
    simp only [m,Passes,Nat.lcm_dvd_iff,orderOf_dvd_iff_pow_eq_one,←pow_mul]
  have divides := (test R).mp full
  constructor
  · rintro ⟨t,wrong,ok⟩
    obtain ⟨v,hv⟩ := divides
    have vne : v≠1 := by
      intro eq
      rw [eq,mul_one] at hv
      exact wrong (hv ▸ (test t).mp ok)
    obtain ⟨l,prime,k,hk⟩ := Nat.exists_prime_and_dvd vne
    have factor : l ∣ R := ⟨m*k, by rw [hv,hk]; ring⟩
    refine ⟨l,Nat.mem_primeFactors.mpr ⟨prime,factor,pos.ne'⟩,(test _).mpr ?_⟩
    apply (Nat.dvd_div_iff_mul_dvd factor).mpr
    exact ⟨k,by rw [hv,hk]; ring⟩
  · rintro ⟨l,hl,ok⟩
    obtain ⟨prime,ld,_⟩ := Nat.mem_primeFactors.mp hl
    have dp := Nat.div_pos (Nat.le_of_dvd pos ld) prime.pos
    exact ⟨R/l,Nat.not_dvd_of_pos_of_lt dp (Nat.div_lt_self pos prime.one_lt),ok⟩

/-- The finite sum of reciprocal prime squares over the divisors of any R
is strictly below one half. -/
theorem prime_square_budget (R : ℕ) : (∑ l ∈ R.primeFactors, 1/(l:ℚ)^2) < 1/2 := by
  let odds := (range R).image fun i => 2*i+3
  have subset : R.primeFactors ⊆ insert 2 odds := by
    intro l hl
    obtain ⟨prime,factor,nz⟩ := Nat.mem_primeFactors.mp hl
    by_cases two : l=2
    · exact mem_insert.mpr (Or.inl two)
    obtain ⟨a,ha⟩ := prime.odd_of_ne_two two
    have bound := Nat.le_of_dvd (Nat.pos_of_ne_zero nz) factor
    have := prime.two_le
    exact mem_insert.mpr (Or.inr (mem_image.mpr ⟨a-1,mem_range.mpr (by omega),by omega⟩))
  have noTwo : 2 ∉ odds := by
    rintro h
    obtain ⟨a,_,ha⟩ := mem_image.mp h
    omega
  have telescopes (k : ℕ) :
      (∑ i ∈ range k, 1/(4*((i:ℚ)+1)*(i+2))) = 1/4 - 1/(4*((k:ℚ)+1)) := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [sum_range_succ,ih]
      push_cast
      have a : (k:ℚ)+1 ≠ 0 := by positivity
      have b : (k:ℚ)+2 ≠ 0 := by positivity
      rw [show (k:ℚ)+1+1=k+2 by ring]
      field_simp
      ring
  calc
    _ ≤ ∑ l ∈ insert 2 odds, 1/(l:ℚ)^2 :=
      sum_le_sum_of_subset_of_nonneg subset (fun l _ _ => one_div_nonneg.mpr (sq_nonneg _))
    _ = 1/4 + ∑ i ∈ range R, 1/(2*(i:ℚ)+3)^2 := by
      rw [sum_insert noTwo,show odds=(range R).image (fun i => 2*i+3) from rfl,
        sum_image (fun x _ y _ h => (by omega : x=y))]
      push_cast
      norm_num
    _ ≤ 1/4 + ∑ i ∈ range R, 1/(4*((i:ℚ)+1)*(i+2)) := by
      apply add_le_add_left
      apply sum_le_sum
      intro i _
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    _ < _ := by
      rw [telescopes]
      have h : 0 < 1/(4*((R:ℚ)+1)) := one_div_pos.mpr (by positivity)
      linarith

/-- Unit pairs that pass one of the critical wrong multipliers. -/
noncomputable def badPanels (N R : ℕ) [NeZero N] :
    Finset ((ZMod N)ˣ × (ZMod N)ˣ) :=
  R.primeFactors.biUnion fun l =>
    let S := univ.filter fun x : (ZMod N)ˣ => x^((N-1)*(R/l))=1
    S ×ˢ S

theorem mem_badPanels {N R : ℕ} [NeZero N] (z : (ZMod N)ˣ × (ZMod N)ˣ)
    (pos : 0<R) (full : Passes z (N-1) R) :
    z ∈ badPanels N R ↔ ∃ t, ¬ R ∣ t ∧ Passes z (N-1) t := by
  rw [false_pass_iff z pos full]
  simp [badPanels,Passes]

private theorem residual_pos {p q : ℕ} (pp : p.Prime) (qp : q.Prime) :
    0 < residualProduct p q := by
  let g := (p-1).gcd (q-1)
  have hp := Nat.sub_pos_of_lt pp.one_lt
  have hq := Nat.sub_pos_of_lt qp.one_lt
  have hg : 0<g := Nat.gcd_pos_of_pos_left _ hp
  exact Nat.mul_pos (Nat.div_pos (Nat.le_of_dvd hp (Nat.gcd_dvd_left ..)) hg)
    (Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_right ..)) hg)

/-- Every unit passes the minimum R. -/
theorem full_pass {p q : ℕ} [NeZero (p*q)] (pp : p.Prime) (qp : q.Prime)
    (ne : p≠q) (x : (ZMod (p*q))ˣ) :
    x^((p*q-1)*residualProduct p q)=1 := by
  have h := exact_fraction pp qp ne (residualProduct p q)
  rw [Nat.gcd_self] at h
  have size := Nat.eq_of_mul_eq_mul_right (residual_pos pp qp) h
  change (univ.filter _).card = _ at size
  rw [←ZMod.card_units_eq_totient,←card_univ] at size
  exact card_filter_eq_iff.mp size x (mem_univ _)

/-- Outside the counted set, the same pair correctly tests all multipliers at once. -/
theorem faithful_iff {p q : ℕ} [NeZero (p*q)] (pp : p.Prime) (qp : q.Prime)
    (ne : p≠q) (z : (ZMod (p*q))ˣ × (ZMod (p*q))ˣ) :
    z ∉ badPanels (p*q) (residualProduct p q) ↔
      ∀ t, Passes z (p*q-1) t ↔ residualProduct p q ∣ t := by
  have full : Passes z (p*q-1) (residualProduct p q) :=
    ⟨full_pass pp qp ne _,full_pass pp qp ne _⟩
  rw [mem_badPanels z (residual_pos pp qp) full]
  constructor
  · intro good t
    constructor
    · intro passed
      by_contra wrong
      exact good ⟨t,wrong,passed⟩
    · rintro ⟨k,rfl⟩
      simp only [Passes,←Nat.mul_assoc,pow_mul,full.1,full.2,one_pow,and_self]
  · rintro test ⟨t,wrong,passed⟩
    exact wrong ((test t).mp passed)

/-- Fewer than half of all ordered unit pairs accept even one wrong multiplier.
The same two bases can therefore be retained for any number of guesses. -/
theorem fewer_than_half {p q : ℕ} [NeZero (p*q)] (pp : p.Prime) (qp : q.Prime)
    (ne : p≠q) :
    2 * (badPanels (p*q) (residualProduct p q)).card < (p*q).totient^2 := by
  let R := residualProduct p q
  let U := (p*q).totient
  have rpos : 0<R := residual_pos pp qp
  have upos : 0<U := Nat.totient_pos.mpr (NeZero.pos _)
  have each (l : ℕ) (hl : l ∈ R.primeFactors) :
      (passing (p*q) (R/l):ℚ)^2 = (U:ℚ)^2 * (1/(l:ℚ)^2) := by
    obtain ⟨prime,ld,_⟩ := Nat.mem_primeFactors.mp hl
    have h := exact_fraction pp qp ne (R/l)
    change passing (p*q) (R/l) * R = U * R.gcd (R/l) at h
    rw [Nat.gcd_eq_right (Nat.div_dvd_of_dvd ld)] at h
    have dp := Nat.div_pos (Nat.le_of_dvd rpos ld) prime.pos
    have prod := Nat.mul_div_cancel' ld
    have size : passing (p*q) (R/l) * l = U := by
      apply Nat.eq_of_mul_eq_mul_right dp
      rw [mul_assoc,prod,h]
    have castSize : (passing (p*q) (R/l):ℚ) * l = U := by exact_mod_cast size
    have nz : (l:ℚ) ≠ 0 := by exact_mod_cast prime.ne_zero
    rw [←castSize]
    field_simp
    ring
  have union : (badPanels (p*q) R).card ≤ ∑ l ∈ R.primeFactors, passing (p*q) (R/l)^2 := by
    unfold badPanels
    apply card_biUnion_le.trans_eq
    apply sum_congr rfl
    intro l _
    rw [card_product,pow_two]
    rfl
  have bounds : ((badPanels (p*q) R).card:ℚ) ≤
      ∑ l ∈ R.primeFactors, (passing (p*q) (R/l):ℚ)^2 := by exact_mod_cast union
  rw [sum_congr rfl each,←mul_sum] at bounds
  have half := mul_lt_mul_of_pos_left (prime_square_budget R) (show (0:ℚ)<(U:ℚ)^2 by positivity)
  have result : 2*((badPanels (p*q) R).card:ℚ) < (U:ℚ)^2 := by linarith
  exact_mod_cast result

/-- At 221 each of 4 and 5 accepts its own early multiplier, but together
they test every multiplier correctly. -/
theorem control_221 :
    let x := ZMod.unitOfCoprime 4 (by decide : Nat.Coprime 4 221)
    let y := ZMod.unitOfCoprime 5 (by decide : Nat.Coprime 5 221)
    x^(220*3)=1 ∧ y^(220*4)=1 ∧ (∀ t, Passes (x,y) 220 t ↔ 12 ∣ t) := by
  let x := ZMod.unitOfCoprime 4 (by decide : Nat.Coprime 4 221)
  let y := ZMod.unitOfCoprime 5 (by decide : Nat.Coprime 5 221)
  change x^(220*3)=1 ∧ y^(220*4)=1 ∧ (∀ t, Passes (x,y) 220 t ↔ 12 ∣ t)
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  apply (faithful_iff (p:=13) (q:=17) (by decide) (by decide) (by decide) (x,y)).mp
  intro bad
  change (x,y) ∈ badPanels 221 12 at bad
  have full : Passes (x,y) 220 12 := ⟨by decide +kernel,by decide +kernel⟩
  obtain ⟨l,hl,passing⟩ := (false_pass_iff (x,y) (by decide : 0<12) full).mp
    ((mem_badPanels (x,y) (by decide : 0<12) full).mp bad)
  obtain ⟨lp,ld,_⟩ := Nat.mem_primeFactors.mp hl
  have small := Nat.le_of_dvd (by decide : 0<12) ld
  have two_three : l=2 ∨ l=3 := by interval_cases l <;> norm_num at lp ld ⊢
  rcases two_three with rfl | rfl
  · exact (by decide +kernel : y^(220*(12/2))≠1) passing.2
  · exact (by decide +kernel : x^(220*(12/3))≠1) passing.1

end PrimeFactors.JacobiPeriodPanel
