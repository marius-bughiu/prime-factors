import PrimeFactors.CircleMarkBinomialFibers
import PrimeFactors.CircleMarkJacobiMask

/-! The total for a power minus a constant has a divisor gap, even when its
degree is unrestricted. This rules out replacing the full prefix mask by a
single such polynomial in the same midpoint readout. -/
namespace PrimeFactors.CircleMarkBinomialMask

open Finset Polynomial CircleMarkBinomialFibers CircleMarkJacobiMask CircleMarkMidcutReadout
open scoped Classical

noncomputable def binomial (e : ℕ) (c : ℤ) : Polynomial ℤ := X^e-C c

/-- Only the difference of the two signed fibers contributes locally. -/
theorem local_difference (r : ℕ) [Fact r.Prime] (odd : r≠2) (e : ℕ) (c : ℤ) :
    localSum r (binomial e c) =
      -(((fiber r e (c:ZMod r) 1).card:ℤ)-((fiber r e (c:ZMod r) (-1)).card:ℤ)) := by
  rw [local_eq odd]
  congr 1
  unfold CircleMarkJacobiMask.rootSet fiber binomial
  rw [sum_filter]
  simp only [Polynomial.map_sub,Polynomial.map_pow,map_X,map_C,Int.coe_castRingHom,
    eval_sub,eval_pow,eval_X,eval_C,sub_eq_zero,Finset.card_filter,Nat.cast_sum,
    Nat.cast_ite,Nat.cast_one,Nat.cast_zero,←sum_sub_distrib]
  apply sum_congr rfl
  intro x _
  by_cases eqn : x^e=(c:ZMod r)
  · by_cases zero : x=0
    · simp [eqn,zero,quadraticChar_zero] at *
    · rcases quadraticChar_dichotomy zero with h|h <;> simp [eqn,h]
  · simp [eqn]

theorem local_divisor (r : ℕ) [Fact r.Prime] (odd : r≠2) (e : ℕ) (c : ℤ) :
    localSum r (binomial e c)=0 ∨ (localSum r (binomial e c)).natAbs ∣ (r-1)/2 := by
  rw [local_difference r odd]
  simpa only [neg_eq_zero,Int.natAbs_neg] using difference_dvd r odd e (c:ZMod r)

/-- Every nonzero magnitude divides the product of the two half-periods.
Hence it equals that product or is at most half as large. -/
theorem gap {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (diff : p≠q)
    (op : p≠2) (oq : q≠2) (e : ℕ) (c : ℤ) :
    let a := (globalSum (p*q) (binomial e c)).natAbs
    let top := ((p-1)/2)*((q-1)/2)
    (a=0 ∨ a∣top) ∧ (a=top ∨ 2*a≤top) := by
  dsimp only
  rw [factorization diff,Int.natAbs_mul]
  let a := (localSum p (binomial e c)).natAbs*(localSum q (binomial e c)).natAbs
  let top := ((p-1)/2)*((q-1)/2)
  change (a=0 ∨ a∣top) ∧ (a=top ∨ 2*a≤top)
  have div : a=0 ∨ a∣top := by
    rcases local_divisor p op e c with h|h
    · left; simp [a,h]
    rcases local_divisor q oq e c with k|k
    · left; simp [a,k]
    exact Or.inr (Nat.mul_dvd_mul h k)
  refine ⟨div,?_⟩
  rcases div with z|⟨m,mul⟩
  · exact Or.inr (by omega)
  by_cases one : m=1
  · left; simpa [one] using mul.symm
  have P := hp.out.two_le
  have Q := hq.out.two_le
  have pos : 0<top := Nat.mul_pos (by omega) (by omega)
  have mp : 2≤m := by
    by_contra! lt
    have zm : m=0 := by omega
    have cut : top=0 := by simpa [zm] using mul
    omega
  right
  rw [mul,Nat.mul_comm a]
  exact Nat.mul_le_mul_right _ mp

private theorem half (r : ℕ) (odd : Odd r) : r=2*((r-1)/2)+1 := by
  obtain ⟨t,rt⟩ := odd
  omega

/-- The public cutoff lies strictly inside the gap on these balanced inputs.
The margins below also account for the rounding tolerance of the odd-prime decoder. -/
theorem location {p q : ℕ} (po : Odd p) (qo : Odd q) (order : p<q) (balance : q<2*p)
    (big : 11≤p) :
    cutoff (p*q)<(q-1)/2 ∧ cutoff (p*q)<2*((p-1)/2) ∧
      (q-1)/2+2≤2*cutoff (p*q) := by
  let u := (p-1)/2
  let v := (q-1)/2
  have P : p=2*u+1 := half p po
  have Q : q=2*v+1 := half q qo
  have small := Nat.mul_le_mul_right q (show p≤q-2 by omega)
  have qeq : q-2+2=q := by omega
  have upper : (p*q).sqrt<q-1 := Nat.sqrt_lt.mpr (by
    nlinarith only [small,qeq,show q-1+1=q by omega])
  have v5 : 5≤v := by omega
  have vv : 5*v≤v*v := Nat.mul_le_mul_right v v5
  have low := Nat.mul_le_mul_right q (show v+1≤p by omega)
  have lower : v+3 ≤ (p*q).sqrt := Nat.le_sqrt.mpr (by
    rw [Q] at low
    nlinarith only [low,vv,v5,Q])
  change (p*q).sqrt/2<v ∧ (p*q).sqrt/2<2*u ∧ v+2≤2*((p*q).sqrt/2)
  omega

/-- No exponent or constant attains even the tolerance needed to substitute
this sum directly into the nearest-odd-factor formula. -/
theorem outside_rounding {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (order : p<q) (balance : q<2*p) (big : 11≤p) (e : ℕ) (c : ℤ) :
    (cutoff (p*q):ℤ) <
      2*|globalSum (p*q) (binomial e c)-globalSum (p*q) (prefixMask (cutoff (p*q)))| := by
  have op : p≠2 := by omega
  have oq : q≠2 := by omega
  let u : ℤ := ((p-1)/2:ℕ)
  let v : ℤ := ((q-1)/2:ℕ)
  let k : ℤ := cutoff (p*q)
  let z := globalSum (p*q) (binomial e c)
  have bounds := location (hp.out.odd_of_ne_two op) (hq.out.odd_of_ne_two oq) order balance big
  have kv : k+1≤v := by dsimp only [k,v]; exact_mod_cast (show cutoff (p*q)+1≤(q-1)/2 from bounds.1)
  have ku : k<2*u := by dsimp only [k,u]; exact_mod_cast bounds.2.1
  have vk : v+2≤2*k := by dsimp only [v,k]; exact_mod_cast bounds.2.2
  have up : 0≤u := by dsimp only [u]; exact_mod_cast (Nat.zero_le ((p-1)/2))
  rw [midcut_sum order op oq]
  change k < 2*|z-k*u|
  have cases := (gap order.ne op oq e c).2
  change z.natAbs=_ ∨ 2*z.natAbs≤_ at cases
  rcases cases with h|h
  · have m : |z|=u*v := by rw [←Int.natCast_natAbs]; dsimp only [u,v]; exact_mod_cast h
    have mul := mul_le_mul_of_nonneg_left kv up
    rcases le_or_gt 0 z with pos|neg
    · rw [abs_of_nonneg pos] at m
      linarith only [m,mul,ku,le_abs_self (z-k*u)]
    · rw [abs_of_neg neg] at m
      have kn : 0≤k*u := mul_nonneg (Int.natCast_nonneg _) up
      linarith only [m,mul,ku,kn,neg_le_abs (z-k*u)]
  · have m : 2*|z|≤u*v := by rw [←Int.natCast_natAbs]; dsimp only [u,v]; exact_mod_cast h
    have mul := mul_le_mul_of_nonneg_left vk up
    linarith only [m,mul,ku,le_abs_self z,neg_le_abs (z-k*u)]

end PrimeFactors.CircleMarkBinomialMask
