import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace PrimeFactors.DivisorSecondMoment
set_option exponentiation.threshold 2048
open Finset

/-- Number of ordered positive (k+1)-tuples with product at most X. -/
noncomputable def tuples : ℕ → ℕ → ℕ
  | 0, X => X
  | k+1, X => ∑ a ∈ Icc 1 X, tuples k (X/a)

private theorem blocks {f g : ℕ → ℕ} (j : ℕ)
    (row : ∀ i<j, (∑ a ∈ Ico (2^i) (2^(i+1)), f a) ≤ g i) :
    (∑ a ∈ Ico 1 (2^j), f a) ≤ ∑ i ∈ range j, g i := by
  induction j with
  | zero => simp
  | succ j ih =>
    have base : 1≤(2:ℕ)^j := Nat.one_le_pow _ _ (by decide)
    rw [← sum_Ico_consecutive f base (by rw [pow_succ]; omega),sum_range_succ]
    exact Nat.add_le_add (ih (fun i hi => row i (by omega))) (row j (by omega))

/-- The nonempty dyadic bins for k coordinates have sum of their indices at most b.
Their number is the displayed binomial coefficient; every bin costs at most X. -/
theorem tuples_bound (k b X : ℕ) (cap : X≤2^b) :
    tuples k X ≤ X*(b+k).choose k := by
  induction k generalizing b X with
  | zero => simp [tuples]
  | succ k ih =>
    let f (a : ℕ) := tuples k (X/a)
    have bp : 0<(2:ℕ)^b := by positivity
    have cut : X<2^(b+1) := cap.trans_lt (by rw [pow_succ]; omega)
    have subset : Icc 1 X ⊆ Ico 1 (2^(b+1)) := fun a ha =>
      mem_Ico.mpr ⟨(mem_Icc.mp ha).1,(mem_Icc.mp ha).2.trans_lt cut⟩
    have row (i : ℕ) (hi : i<b+1) :
        (∑ a ∈ Ico (2^i) (2^(i+1)), f a) ≤ X*(b-i+k).choose k := by
      let B := (2:ℕ)^i
      have bp : 0<B := by positivity
      have span : 2^b=B*2^(b-i) := by rw [←pow_add,Nat.add_sub_of_le (by omega : i≤b)]
      have terms := sum_le_sum (s:=Ico (2^i) (2^(i+1))) (fun a ha => by
        have lower : B≤a := (mem_Ico.mp ha).1
        have div := Nat.div_le_div_left (a:=X) lower bp
        have reduced : X/B≤2^(b-i) := Nat.div_le_of_le_mul' (cap.trans_eq span)
        exact (ih (b-i) (X/a) (div.trans reduced)).trans
          (Nat.mul_le_mul_right ((b-i+k).choose k) div))
      have width : 2^(i+1)-2^i=B := by rw [pow_succ]; dsimp [B]; omega
      simp only [sum_const,Nat.card_Ico,width,nsmul_eq_mul,Nat.cast_id] at terms
      exact terms.trans ((by rw [←Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (Nat.mul_div_le X B)) :
        B*(X/B*(b-i+k).choose k) ≤ X*(b-i+k).choose k)
    change (∑ a ∈ Icc 1 X, f a) ≤ _
    calc
      _ ≤ ∑ a ∈ Ico 1 (2^(b+1)), f a :=
        sum_le_sum_of_subset_of_nonneg subset (fun _ _ _ => Nat.zero_le _)
      _ ≤ _ := blocks (b+1) row
      _ = X*(b+(k+1)).choose (k+1) := by
        rw [←Finset.mul_sum]
        have ref := sum_range_reflect (fun i => (i+k).choose k) (b+1)
        simp only [Nat.add_sub_cancel] at ref
        rw [ref,Nat.sum_range_add_choose,Nat.add_assoc]

private abbrev Quad := Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ

private noncomputable def box (X : ℕ) : Finset Quad :=
  (Icc 1 X).sigma fun a => (Icc 1 (X/a)).sigma fun b =>
    (Icc 1 (X/a/b)).sigma fun c => Icc 1 (X/a/b/c)

private theorem in_box {a b c d X : ℕ} (ap : 0<a) (bp : 0<b) (cp : 0<c)
    (dp : 0<d) (bound : a*b*c*d≤X) : (⟨a,b,c,d⟩ : Quad) ∈ box X := by
  have q₁ : b*(c*d)≤X/a := (Nat.le_div_iff_mul_le ap).mpr (by simpa only [Nat.mul_assoc,
    Nat.mul_comm,Nat.mul_left_comm] using bound)
  have q₂ : c*d≤X/a/b := (Nat.le_div_iff_mul_le bp).mpr (by simpa only [Nat.mul_comm b] using q₁)
  have q₃ : d≤X/a/b/c := (Nat.le_div_iff_mul_le cp).mpr (by simpa only [Nat.mul_comm c] using q₂)
  have ax : a≤X := (Nat.le_mul_of_pos_right a (Nat.mul_pos bp (Nat.mul_pos cp dp))).trans
    (by simpa only [Nat.mul_assoc] using bound)
  exact mem_sigma.mpr ⟨mem_Icc.mpr ⟨ap,ax⟩,mem_sigma.mpr
    ⟨mem_Icc.mpr ⟨bp,(Nat.le_mul_of_pos_right b (Nat.mul_pos cp dp)).trans q₁⟩,mem_sigma.mpr
    ⟨mem_Icc.mpr ⟨cp,(Nat.le_mul_of_pos_right c dp).trans q₂⟩,mem_Icc.mpr ⟨dp,q₃⟩⟩⟩⟩

private abbrev Row := Σ _ : ℕ, ℕ × ℕ

private def encode (z : Row) : Quad :=
  let a := z.2.1
  let b := z.2.2
  let g := a.gcd b
  ⟨g,a/g,b/g,z.1/(a.lcm b)⟩

private def decode (v : Quad) : Row :=
  ⟨v.1*v.2.1*v.2.2.1*v.2.2.2,v.1*v.2.1,v.1*v.2.2.1⟩

private theorem encoding {n a b : ℕ} (ha : a∈n.divisors) (hb : b∈n.divisors) :
    let v := encode ⟨n,a,b⟩
    decode v=⟨n,a,b⟩ ∧ 0<v.1 ∧ 0<v.2.1 ∧ 0<v.2.2.1 ∧ 0<v.2.2.2 := by
  let g := a.gcd b
  let l := a.lcm b
  have ap := Nat.pos_of_mem_divisors ha
  have bp := Nat.pos_of_mem_divisors hb
  have np := Nat.pos_of_ne_zero (Nat.mem_divisors.mp ha).2
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ ap
  have lp : 0<l := Nat.lcm_pos ap bp
  have gu : g*(a/g)=a := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have gv : g*(b/g)=b := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  have ln : l∣n := Nat.lcm_dvd (Nat.dvd_of_mem_divisors ha) (Nat.dvd_of_mem_divisors hb)
  have lcm : g*(a/g)*(b/g)=l := by
    apply Nat.eq_of_mul_eq_mul_left gp
    calc g*(g*(a/g)*(b/g)) = (g*(a/g))*(g*(b/g)) := by ring
         _ = _ := by rw [gu,gv]; exact (Nat.gcd_mul_lcm a b).symm
  have recover : g*(a/g)*(b/g)*(n/l)=n := by rw [lcm,Nat.mul_div_cancel' ln]
  exact ⟨by change (⟨g*(a/g)*(b/g)*(n/l),g*(a/g),g*(b/g)⟩ : Row) = _; rw [recover,gu,gv],
    gp,Nat.div_pos (Nat.le_of_dvd ap (Nat.gcd_dvd_left ..)) gp,
    Nat.div_pos (Nat.le_of_dvd bp (Nat.gcd_dvd_right ..)) gp,
    Nat.div_pos (Nat.le_of_dvd np ln) lp⟩

/-- Map each pair of divisors a,b of n to the four positive factors
gcd(a,b), a/gcd(a,b), b/gcd(a,b), n/lcm(a,b). Their product is n. -/
theorem second_moment_le_tuples (X : ℕ) :
    (∑ n ∈ Icc 1 X, n.divisors.card^2) ≤ tuples 3 X := by
  let rows := (Icc 1 X).sigma (fun n => n.divisors ×ˢ n.divisors)
  have left : rows.card=∑ n ∈ Icc 1 X, n.divisors.card^2 := by simp [rows,card_sigma,pow_two]
  have right : (box X).card=tuples 3 X := by simp [box,tuples,card_sigma,Nat.card_Icc]
  rw [←left,←right]
  apply card_le_card_of_injOn encode
  · rintro ⟨n,a,b⟩ hr
    obtain ⟨hn,t⟩ := mem_sigma.mp hr
    obtain ⟨ha,hb⟩ := mem_product.mp t
    obtain ⟨recov,hg,hu,hv,hw⟩ := encoding ha hb
    apply in_box hg hu hv hw
    exact (congrArg Sigma.fst recov).le.trans (mem_Icc.mp hn).2
  · intro z hz z' hz' same
    have leftInv {w : Row} (mem : w∈rows) : decode (encode w)=w := by
      rcases w with ⟨n,a,b⟩
      obtain ⟨ha,hb⟩ := mem_product.mp (mem_sigma.mp mem).2
      exact (encoding ha hb).1
    exact (leftInv hz).symm.trans ((congrArg decode same).trans (leftInv hz'))

/-- Explicit bound for any cutoff below a prescribed power of two. -/
theorem binomial (b X : ℕ) (cap : X≤2^b) :
    (∑ n ∈ Icc 1 X, n.divisors.card^2) ≤ X*(b+3).choose 3 :=
  (second_moment_le_tuples X).trans (tuples_bound 3 b X cap)

private theorem choose_three (b : ℕ) :
    6*(b+3).choose 3=(b+3)*(b+2)*(b+1) := by
  have eq := Nat.descFactorial_eq_factorial_mul_choose (b+3) 3
  simpa [Nat.descFactorial_succ,Nat.factorial_succ,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using eq.symm

/-- A convenient power-only form of the divisor second-moment bound. -/
theorem dyadic (b : ℕ) :
    (∑ n ∈ Icc 1 (2^b), n.divisors.card^2) ≤ 2^b*(b+1)^3 := by
  apply (binomial b (2^b) le_rfl).trans
  apply Nat.mul_le_mul_left
  have h := choose_three b
  nlinarith [Nat.zero_le (b^3),Nat.zero_le (b^2)]

/-- The exact bin count for the cutoff 2^1023. -/
theorem target_bin_count :
    (∑ n ∈ Icc 1 (2^1023), n.divisors.card^2) ≤ 2^1023*179481600 := by
  have count := choose_three 1023
  have eq : (1023+3).choose 3 = 179481600 := by omega
  simpa only [eq] using binomial 1023 (2^1023) le_rfl

/-- The bin count costs fewer than 28 additional bits at this cutoff. -/
theorem target_sharp :
    (∑ n ∈ Icc 1 (2^1023), n.divisors.card^2) < 2^1051 := by
  exact target_bin_count.trans_lt (by decide +kernel)

theorem target :
    (∑ n ∈ Icc 1 (2^1023), n.divisors.card^2) ≤ 2^1053 :=
  target_sharp.le.trans (Nat.pow_le_pow_right (by decide) (by decide))

end PrimeFactors.DivisorSecondMoment
