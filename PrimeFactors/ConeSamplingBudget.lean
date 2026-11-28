import PrimeFactors.SquaredConeSum
import Mathlib.Algebra.Order.Ring.Pow

/-! Uniform samples of ordered triples modulo the square of a semiprime.
The raw count is close to a public fourth power. Its exact correction can
carry information even when independent uniform samples see only misses. -/

namespace PrimeFactors.ConeSamplingBudget

open Finset ThreeSquareCone

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- All lists of independent uniform draws have the same probability. -/
noncomputable def hits (S : Finset α) (b : ℕ) : Finset (Fin b → α) := by
  classical exact univ.filter (fun f => ∃ i, f i ∈ S)

theorem misses_card (S : Finset α) (b : ℕ) :
    (hits S b)ᶜ.card = (Fintype.card α-S.card)^b := by
  classical
  have miss (f : Fin b → α) : f∈(hits S b)ᶜ ↔ ∀ i, f i∈Sᶜ := by simp [hits]
  let e : ↥(hits S b)ᶜ ≃ (Fin b → ↥Sᶜ) :=
    { toFun := fun f i => ⟨f.val i,(miss _).mp f.property i⟩
      invFun := fun g => ⟨fun i => (g i).val,(miss _).mpr (fun i => (g i).property)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Fintype.card_coe,Fintype.card_congr e,Fintype.card_fun,Fintype.card_coe,
    Fintype.card_fin,Finset.card_compl]

noncomputable def hitProbability (S : Finset α) (b : ℕ) : ℚ :=
  ((hits S b).card : ℚ)/(Fintype.card α : ℚ)^b

/-- Probability of observing the first hit by the stated budget. -/
theorem exact_hits [Nonempty α] (S : Finset α) (b : ℕ) :
    hitProbability S b = 1-(1-(S.card:ℚ)/(Fintype.card α:ℚ))^b := by
  classical
  have h := card_add_card_compl (hits S b)
  rw [misses_card,Fintype.card_fun,Fintype.card_fin] at h
  have c : (0:ℚ)<Fintype.card α := by exact_mod_cast Fintype.card_pos
  have z : ((hits S b).card:ℚ)+((Fintype.card α:ℚ)-S.card)^b=(Fintype.card α:ℚ)^b := by
    have cast := congrArg (fun t : ℕ => (t:ℚ)) h
    simpa only [Nat.cast_add,Nat.cast_pow,Nat.cast_sub (card_le_univ S)] using cast
  rw [hitProbability,div_eq_iff (pow_pos c b).ne']
  rw [show 1-(S.card:ℚ)/(Fintype.card α:ℚ)=((Fintype.card α:ℚ)-S.card)/Fintype.card α by
    field_simp,div_pow,sub_mul,one_mul,div_mul_cancel₀ _ (pow_pos c b).ne']
  linarith

/-- The union bound on seeing at least one hit among independent probes. -/
theorem hit_bound [Nonempty α] (S : Finset α) (b : ℕ) :
    hitProbability S b ≤ b*((S.card:ℚ)/Fintype.card α) := by
  rw [exact_hits]
  have c : (0:ℚ)<Fintype.card α := by exact_mod_cast Fintype.card_pos
  have f : (S.card:ℚ)/Fintype.card α ≤ 1 := by
    rw [div_le_one c]; exact_mod_cast card_le_univ S
  have bern := one_add_mul_sub_le_pow (R := ℚ)
    (a := 1-(S.card:ℚ)/Fintype.card α) (by linarith) b
  linarith

/-- The usual empirical count estimate, formed solely from the fraction of
positive indicators among the draws. -/
noncomputable def estimate {b : ℕ} (S : Finset α) (f : Fin b → α) : ℚ :=
  (((univ.filter fun i => f i ∈ S).card : ℚ)*Fintype.card α)/b

theorem relative_success_subset (S : Finset α) (b : ℕ) :
    (univ.filter fun f : Fin b → α => |estimate S f-S.card| < S.card) ⊆ hits S b := by
  classical
  intro f h
  by_contra hm
  have miss : ∀ i, f i ∉ S := by simpa [hits] using hm
  have empty : (univ.filter fun i => f i∈S)=∅ := by ext i; simp [miss i]
  simpa [estimate,empty] using (mem_filter.mp h).2

abbrev Triple (n : ℕ) := SemiprimeThreeSquareCone.Triple (n^2)
noncomputable abbrev cone (n : ℕ) [NeZero n] := points (ZMod (n^2)) 0

theorem ambient (n : ℕ) [NeZero n] : Fintype.card (Triple n)=n^6 := by
  simp only [Triple,SemiprimeThreeSquareCone.Triple,Fintype.card_prod,ZMod.card]
  ring

private def localCount (p : ℕ) := (p^2-1)*p^2+p^3

private theorem bounds {p : ℕ} (o : 2<p) :
    p^4<localCount p ∧ localCount p<p^3*(p+1) := by
  have hp : 1≤p^2 := Nat.one_le_pow _ _ (by omega)
  dsimp [localCount]
  zify [hp] at *
  constructor
  · nlinarith [mul_pos (show (0:ℤ)<p^2 by positivity) (show (0:ℤ)<p-1 by omega)]
  · nlinarith [show (0:ℤ)<p^2 by positivity]

private theorem formula {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (lt : p<q) (odd : 2<p) :
    (cone (p*q)).card=localCount p*localCount q := by
  change SquaredConeSum.count _=_
  have hp : 1≤p^2 := pow_pos (Fact.out : p.Prime).pos _
  have hq : 1≤q^2 := pow_pos (Fact.out : q.Prime).pos _
  apply Int.ofNat_inj.mp
  rw [SquaredConeSum.factored lt.ne odd.ne' (odd.trans lt).ne']
  dsimp [localCount]
  push_cast [Nat.cast_sub hp,Nat.cast_sub hq]
  ring

/-- Even with no samples, the public estimate N⁴ has relative error less
than 3/p, measured against N⁴ itself, where p is the smaller prime. -/
theorem public_estimate {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (lt : p<q) (odd : 2<p) :
    (p*q)^4 < (cone (p*q)).card ∧
    p*((cone (p*q)).card-(p*q)^4)<3*(p*q)^4 := by
  rw [formula lt odd]
  obtain ⟨pl,pu⟩ := bounds odd
  obtain ⟨ql,qu⟩ := bounds (odd.trans lt)
  have low : (p*q)^4<localCount p*localCount q := by
    rw [mul_pow]; exact Nat.mul_lt_mul_of_lt_of_lt pl ql
  have high : localCount p*localCount q < (p*q)^3*(p*q+p+q+1) := by
    convert Nat.mul_lt_mul_of_lt_of_lt pu qu using 1; ring
  refine ⟨low,?_⟩
  have gap : localCount p*localCount q-(p*q)^4 < (p*q)^3*(p+q+1) := by
    rw [Nat.sub_lt_iff_lt_add low.le]
    convert high using 1; ring
  have sizes : p*(p+q+1) ≤ 3*(p*q) := by
    nlinarith [Nat.mul_le_mul_left p (show p+1≤2*q by omega)]
  calc
    p*(localCount p*localCount q-(p*q)^4) < p*((p*q)^3*(p+q+1)) :=
      Nat.mul_lt_mul_of_pos_left gap (by omega)
    _ = (p*q)^3*(p*(p+q+1)) := by ring
    _ ≤ (p*q)^3*(3*(p*q)) := Nat.mul_le_mul_left _ sizes
    _ = 3*(p*q)^4 := by ring

private theorem upper {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (lt : p<q) (odd : 2<p) :
    (cone (p*q)).card < 2*(p*q)^4 := by
  obtain ⟨low,close⟩ := public_estimate lt odd
  have sm : (cone (p*q)).card-(p*q)^4 < (p*q)^4 := by
    exact Nat.lt_of_mul_lt_mul_left (close.trans_le (Nat.mul_le_mul_right _ (by omega : 3≤p)))
  omega

/-- For B positive probes the chance of even one hit is strictly less than
2B/N². An empirical count with relative error below one requires a hit. -/
theorem cone_hit_bound {p q b : ℕ} [Fact p.Prime] [Fact q.Prime]
    (lt : p<q) (odd : 2<p) (bp : 0<b) :
    hitProbability (cone (p*q)) b < 2*b/((p*q:ℕ):ℚ)^2 := by
  have npos : 0<((p*q:ℕ):ℚ) := by exact_mod_cast Nat.mul_pos (by omega : 0<p) (by omega : 0<q)
  have ub : ((cone (p*q)).card:ℚ)<2*((p*q:ℕ):ℚ)^4 := by exact_mod_cast upper lt odd
  apply (hit_bound _ b).trans_lt
  rw [ambient,Nat.cast_pow]
  calc
    _ < (b:ℚ)*(2*((p*q:ℕ):ℚ)^4/((p*q:ℕ):ℚ)^6) :=
      mul_lt_mul_of_pos_left (div_lt_div_of_pos_right ub (by positivity)) (by exact_mod_cast bp)
    _ = _ := by
      generalize ((p*q:ℕ):ℚ)=x at npos ⊢
      field_simp [npos.ne']; ring

/-- The first positive empirical estimate is T/b. If it is at least
twice the truth, every transcript incurs at least 100% relative error. -/
theorem coarse_estimate {b : ℕ} (S : Finset α) (f : Fin b → α) (bp : 0<b)
    (step : 2*S.card*b ≤ Fintype.card α) :
    (S.card:ℚ) ≤ |estimate S f-S.card| := by
  let h := (univ.filter fun i => f i∈S).card
  change (S.card:ℚ) ≤ |(h:ℚ)*(Fintype.card α:ℚ)/b-S.card|
  by_cases z : h=0
  · simp [z]
  have pos : (0:ℚ)<b := by exact_mod_cast bp
  have jump : 2*(S.card:ℚ) ≤ (h:ℚ)*(Fintype.card α:ℚ)/b := by
    rw [le_div_iff₀ pos]
    exact_mod_cast step.trans (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero z))
  exact le_trans (by linarith : (S.card:ℚ) ≤ (h:ℚ)*(Fintype.card α:ℚ)/b-S.card)
    (le_abs_self _)

/-- Up through N²/4 positive probes, the empirical estimator returns either
zero or a count at least twice the truth. This bound holds for every list. -/
theorem cone_estimate_error {p q b : ℕ} [Fact p.Prime] [Fact q.Prime] (lt : p<q)
    (odd : 2<p) (bp : 0<b) (budget : 4*b≤(p*q)^2) (f : Fin b → Triple (p*q)) :
    ((cone (p*q)).card:ℚ) ≤ |estimate (cone (p*q)) f-(cone (p*q)).card| := by
  apply coarse_estimate _ _ bp
  rw [ambient]
  calc
    2*(cone (p*q)).card*b ≤ 2*(2*(p*q)^4)*b :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (upper lt odd).le)
    _ = (p*q)^4*(4*b) := by ring
    _ ≤ (p*q)^4*(p*q)^2 := Nat.mul_le_mul_left _ budget
    _ = _ := by ring

/-- At N=15 one uniform triple is a hit with probability 319/50625. -/
theorem fifteen : hitProbability (cone 15) 1=319/50625 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have c : (cone 15).card=71775 := by
    exact (formula (p:=3) (q:=5) (by decide) (by decide)).trans (by decide)
  rw [exact_hits,ambient,c]
  norm_num

end PrimeFactors.ConeSamplingBudget
