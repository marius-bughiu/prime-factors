import PrimeFactors.PrimitiveIntervalMoment

/-! What readings at several triangular cutoffs identify when their common
bias is constant or affine in the cutoff. The readings are supplied. -/
namespace PrimeFactors.PrimitiveIntervalCutoffTrend

open Finset PrimitiveIntervalMoment

/-- Both prime layers lie below the upper endpoint, allowing the last layer
to have zero weight. All coordinates of the box are below the smaller prime. -/
def Admissible (p q b : ℕ) : Prop := b < p ∧ q ≤ 2*b+1

theorem admissible_iff {p q b : ℕ} (pos : 0 < p) :
    Admissible p q b ↔ b ∈ Icc (q/2) (p-1) := by
  rw [Admissible,mem_Icc]
  omega

theorem admissible_count {p q : ℕ} (pos : 0 < p) :
    (Icc (q/2) (p-1)).card = p-q/2 := by rw [Nat.card_Icc]; omega

/-- Product-only certificates for bounds on the factors certify the whole
indicated interval of cutoffs. -/
theorem certified_interval {p q P Q b : ℕ} (lower : P ≤ p) (upper : q ≤ Q)
    (lo : Q/2 ≤ b) (hi : b < P) : Admissible p q b :=
  ⟨hi.trans_le lower,by omega⟩

/-- Testing the single possible next smaller factor suffices to certify
two public cutoffs whenever that integer does not divide the product. -/
theorem next_cutoff {p q : ℕ} (pos : 0 < p) (balanced : q < 2*p)
    (miss : ¬(cutoff (p*q)+1) ∣ p*q) :
    Admissible p q (cutoff (p*q)) ∧ Admissible p q (cutoff (p*q)+1) := by
  obtain ⟨lo,hi⟩ := cutoff_bounds pos balanced
  have ne : cutoff (p*q)+1 ≠ p := fun h => miss ((dvd_of_eq h).trans (dvd_mul_right ..))
  exact ⟨⟨lo,hi⟩,⟨by omega,by omega⟩⟩

set_option exponentiation.threshold 4096 in
set_option maxRecDepth 8192 in
/-- For 1024-bit primes, five fixed adjacent cutoffs are admissible for
every pair. The lower dyadic endpoint is two modulo six. -/
theorem five_full_width {p q b : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p < q)
    (lower : 2^1023 ≤ p) (upper : q < 2^1024)
    (lo : 2^1023-2 ≤ b) (hi : b ≤ 2^1023+2) : Admissible p q b := by
  let a : ℕ := 2^1023
  change a ≤ p at lower
  change a-2 ≤ b at lo
  change b ≤ a+2 at hi
  have bound : q < 2*a := by
    change q < 2*2^1023
    rwa [mul_comm,←pow_succ]
  have large : 3 < a := by decide +kernel
  have residue : a%6=2 := by decide +kernel
  have oddP := Nat.odd_iff.mp (pp.odd_of_ne_two (by omega))
  have oddQ := Nat.odd_iff.mp (qp.odd_of_ne_two (by omega))
  have p3 : ¬3 ∣ p := fun h => by
    have eq := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pp).mp h
    omega
  have q3 : ¬3 ∣ q := fun h => by
    have eq := (Nat.prime_dvd_prime_iff_eq Nat.prime_three qp).mp h
    omega
  exact ⟨by omega,by omega⟩

/-- Balance alone can leave just a single cutoff, including at genuine
distinct odd primes. -/
theorem singleton91 : cutoff 91 = 6 ∧ ∀ b, Admissible 7 13 b ↔ b=6 := by
  refine ⟨by decide +kernel,fun b => ?_⟩
  unfold Admissible
  omega

/-- The finite character aggregate agrees with its integer quadratic at
each admissible cutoff. -/
theorem aggregate_at {p q b : ℕ} [Fact p.Prime] [Fact q.Prime] (ord : p < q)
    (valid : Admissible p q b) :
    aggregate p q b = ((value (p*q) b (p+q) : ℤ):ℂ) := by
  obtain ⟨lo,hi⟩ := valid
  rw [aggregate_layers ord lo]
  unfold value
  push_cast [Nat.cast_sub hi,Nat.cast_sub (ord.le.trans hi),
    Nat.cast_sub (Fact.out : p.Prime).one_le,Nat.cast_sub (Fact.out : q.Prime).one_le]
  ring

theorem difference (n b h s : ℤ) :
    value n (b+h) s-value n b s = h*(2*b+h+4-2*s) := by unfold value; ring

/-- At two different admissible cutoffs an arbitrary common additive bias
cancels. Exactly one candidate factor sum fits the resulting difference. -/
theorem common_bias_identifies {p q b h : ℕ} [Fact p.Prime] [Fact q.Prime] (ord : p < q)
    (first : Admissible p q b) (second : Admissible p q (b+h)) (gap : 0 < h)
    {u w c : ℤ} (read₁ : aggregate p q b+(c:ℂ)=(u:ℂ))
    (read₂ : aggregate p q (b+h)+(c:ℂ)=(w:ℂ)) (t : ℤ) :
    w-u=(h:ℤ)*(2*b+h+4-2*t) ↔ t=(p:ℤ)+q := by
  rw [aggregate_at ord first] at read₁
  rw [aggregate_at ord second] at read₂
  have a : value (p*q) b (p+q)+c=u := by exact_mod_cast read₁
  have d : value (p*q) (b+h) (p+q)+c=w := by exact_mod_cast read₂
  have measured : w-u=(h:ℤ)*(2*b+h+4-2*((p:ℤ)+q)) := by
    rw [←a,←d]
    linarith only [difference ((p:ℤ)*q) b h ((p:ℤ)+q)]
  rw [measured,mul_right_inj' (show (h:ℤ)≠0 by omega)]
  omega

/-- Changing the proposed sum changes only the constant and linear
coefficients in the cutoff. This is a polynomial identity for candidate sums. -/
theorem affine_relabel (n b s t slope offset : ℤ) :
    value n b s+slope*b+offset =
      value n b t+(slope+2*(t-s))*b+(offset-(t-s)*(s+t-2)) := by
  unfold value
  ring

/-- On the entire admissible interval, every candidate-sum polynomial
fits the same genuine readings after refitting the unknown slope and offset.
The alternate t here is a proposed sum, with no factorization hypothesis. -/
theorem admissible_affine_ambiguity {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (ord : p < q)
    (slope offset t : ℤ) : ∃ m c : ℤ, ∀ b : ℕ, Admissible p q b →
      aggregate p q b + ((slope*b+offset:ℤ):ℂ) = ((value (p*q) b t+m*b+c : ℤ):ℂ) := by
  refine ⟨slope+2*(t-((p:ℤ)+q)),offset-(t-((p:ℤ)+q))*((p:ℤ)+q+t-2),?_⟩
  intro b valid
  rw [aggregate_at ord valid]
  have eq := affine_relabel ((p:ℤ)*q) b ((p:ℤ)+q) t slope offset
  have z := congrArg (fun x : ℤ => (x:ℂ)) eq
  push_cast at z ⊢
  linear_combination z

/-- Before either prime layer enters, the true finite aggregate is B². -/
theorem before_layers {p q b : ℕ} [Fact p.Prime] [Fact q.Prime] (ord : p < q)
    (early : 2*b+1 ≤ p) : aggregate p q b=(b:ℂ)^2 := by
  rw [aggregate_layers ord (by omega),Nat.sub_eq_zero_of_le early,
    Nat.sub_eq_zero_of_le (early.trans ord.le)]
  simp

/-- If the same affine bias holds at early cutoffs 0 and 1, two supplied
reference readings determine it everywhere. Subtracting it at the public
cutoff gives the true sum through the existing exact decoder. -/
theorem calibrate {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (ord : p < q)
    (balanced : q < 2*p) (large : 3 ≤ p) {slope offset z₀ z₁ v : ℤ}
    (read₀ : aggregate p q 0 + (offset:ℂ) = (z₀:ℂ))
    (read₁ : aggregate p q 1 + ((slope+offset:ℤ):ℂ) = (z₁:ℂ))
    (read : aggregate p q (cutoff (p*q)) + ((slope*cutoff (p*q)+offset:ℤ):ℂ) = (v:ℂ)) :
    recover (p*q) (cutoff (p*q)) (v-(z₁-z₀-1)*cutoff (p*q)-z₀) = p+q := by
  rw [before_layers ord (by omega)] at read₀ read₁
  norm_num at read₀ read₁
  have zero : offset=z₀ := by exact_mod_cast read₀
  have one : 1+(slope+offset)=z₁ := by exact_mod_cast read₁
  have m : z₁-z₀-1=slope := by omega
  rw [m,←zero]
  apply recover_from_aggregate ord balanced
  push_cast at read ⊢
  linear_combination read

/-- Both supplied readings at 143 are shifted up by 1,000. Their difference
is still the change in the genuine totals, which forces the sum to be 24. -/
theorem biased_control143 :
    aggregate 11 13 7+1000=(985:ℂ) ∧ aggregate 11 13 8+1000=(956:ℂ) ∧
    ∀ s : ℤ, 956-985=2*7+1+4-2*s ↔ s=24 := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  rw [aggregate_at (by decide : 11 < 13) (b:=7) (by decide +kernel : 7<11 ∧ 13≤2*7+1),
    aggregate_at (by decide : 11 < 13) (b:=8) (by decide +kernel : 8<11 ∧ 13≤2*8+1)]
  norm_num [value]
  omega

end PrimeFactors.PrimitiveIntervalCutoffTrend
