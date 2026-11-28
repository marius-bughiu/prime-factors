import PrimeFactors.PrimeSquareUniformFloor
import PrimeFactors.GuessTableOverlap

/-! Pairwise minimum of the multiplicities of two attainable sums at the
first power of an odd prime. A low-weight sum can be present, but only two
such sums occur for a square unit product. -/
namespace PrimeFactors.FirstPowerGuessOverlap

open Finset CoprimeGuessTables PrimeSquareSumWeights PrimeSquareExpectedRank PrimeSquareUniformFloor
open scoped Classical
open private PrimeFactors.CombinedSumWeights.weight_first from PrimeFactors.CombinedSumWeights
open private PrimeFactors.PrimeSquareExpectedRank.class_formula PrimeFactors.PrimeSquareExpectedRank.pairs_formula
  from PrimeFactors.PrimeSquareExpectedRank
open private PrimeFactors.PrimeSquareUniformFloor.numerator_le from PrimeFactors.PrimeSquareUniformFloor
open private PrimeFactors.JointSumGuessFloor.sum_labels from PrimeFactors.JointSumGuessFloor

private theorem two_weights {p n : ℕ} [Fact p.Prime] (s : Labels p n) :
    weight n s.val=1 ∨ weight n s.val=2 := by
  obtain ⟨x,y,mul,add⟩ := s.property
  have positive := (positive_iff s.val).mpr s.property
  have roots : ∀ z : ZMod p, z*(s.val-z)=n → z=x ∨ z=y := by
    intro z h
    have zero : (z-x)*(z-y)=0 := by linear_combination -h + mul - z*add
    simpa only [sub_eq_zero] using mul_eq_zero.mp zero
  have cap : weight n s.val≤2 := by
    rw [PrimeFactors.CombinedSumWeights.weight_first,Nat.card_eq_fintype_card,Fintype.card_subtype]
    calc
      _ ≤ ({x,y} : Finset (ZMod p)).card := card_le_card (fun z hz =>
        by simpa only [mem_insert,mem_singleton] using roots z (mem_filter.mp hz).2)
      _ ≤ _ := card_le_two
  omega

/-- For weights one or two the overlap sum is exactly A²+(T−A)², where A
is the number of labels and T is their total weight. -/
theorem one_two {α : Type*} [Fintype α] (w : α→ℕ) (h : ∀ x, w x=1 ∨ w x=2) :
    (∑ x,∑ y,(min (w x) (w y):ℝ)) =
      (Fintype.card α:ℝ)^2+((∑ x,(w x:ℝ))-Fintype.card α)^2 := by
  have kernel (x y : α) : (min (w x) (w y):ℝ)=1+((w x:ℝ)-1)*((w y:ℝ)-1) := by
    rcases h x with hx|hx <;> rcases h y with hy|hy <;> rw [hx,hy] <;> norm_num
  simp_rw [kernel,sum_add_distrib,←mul_sum,←sum_mul,sum_const,card_univ,nsmul_eq_mul,mul_one,sum_sub_distrib]
  simp only [sum_const,card_univ,nsmul_eq_mul,mul_one]
  ring

/-- Unnormalized first-power overlap bound. The factor on the left uses
the same explicit coefficient as the prime-square uniform floor. -/
theorem lower {p n : ℕ} [Fact p.Prime] (odd : p≠2) (unit : ¬p∣n) :
    ((numerator p:ℝ)/pairs p)*(Fintype.card (Labels p n):ℝ)*Nat.card (Pairs n p) ≤
      ∑ x : Labels p n,∑ y : Labels p n,(min (weight n x.val) (weight n y.val):ℝ) := by
  have hp := (Fact.out : p.Prime)
  have nz : (n:ZMod p)≠0 := (ZMod.natCast_zmod_eq_zero_iff_dvd n p).mp.mt unit
  have cardinal : Fintype.card (Labels p n)=(factorSumResidues p n).card := by
    exact Nat.card_eq_fintype_card.symm.trans (card_admissibleSum_eq p n nz)
  have T : (Nat.card (Pairs n p):ℝ)=(p:ℝ)-1 := by
    rw [total (isUnit_iff_ne_zero.mpr nz),Nat.totient_prime hp,Nat.cast_sub hp.one_le,Nat.cast_one]
  have mass : (∑ x : Labels p n,(weight n x.val:ℝ))=(p:ℝ)-1 := by
    rw [←Nat.cast_sum,PrimeFactors.JointSumGuessFloor.sum_labels,T]
  rw [one_two (fun s : Labels p n => weight n s.val) two_weights,mass,T]
  obtain ⟨k,eq⟩ := hp.odd_of_ne_two odd
  by_cases sq : IsSquare (n:ZMod p)
  · rw [card_factorSumResidues_of_square p odd n nz sq] at cardinal
    have A : (Fintype.card (Labels p n):ℝ)=((p:ℝ)+1)/2 := by
      have : 2*Fintype.card (Labels p n)=p+1 := by omega
      linarith only [show (2:ℝ)*Fintype.card (Labels p n)=(p:ℝ)+1 by exact_mod_cast this]
    rw [A]
    by_cases three : p=3
    · rw [three]
      norm_num [numerator,pairs]
    · have pr : (3:ℝ)≤p := by exact_mod_cast (by have := hp.two_le; omega : 3≤p)
      have num : (numerator p:ℝ)=(p:ℝ)^2-3*p+4 := by
        rw [numerator,if_neg three,Nat.cast_mul]
        have form : (classes p:ℝ)=((p:ℝ)^2-3*p+4)/2 := by
          exact_mod_cast PrimeFactors.PrimeSquareExpectedRank.class_formula odd
        rw [form]
        ring
      have den : (pairs p:ℝ)=p*((p:ℝ)-1) := by
        exact_mod_cast PrimeFactors.PrimeSquareExpectedRank.pairs_formula (p:=p)
      rw [num,den]
      have pp : (0:ℝ)<p := by linarith only [pr]
      have low : (0:ℝ)<p-1 := by linarith only [pr]
      have simplify (x : ℝ) : x/((p:ℝ)*(p-1))*((p+1)/2)*(p-1)=x*(p+1)/(2*p) := by
        field_simp [pp.ne',low.ne']
        ring
      rw [simplify,div_le_iff₀ (mul_pos (by norm_num) pp)]
      nlinarith only [pr]
  · rw [card_factorSumResidues_of_nonsquare p n nz sq] at cardinal
    have A : (Fintype.card (Labels p n):ℝ)=((p:ℝ)-1)/2 := by
      have : 2*Fintype.card (Labels p n)+1=p := by omega
      linarith only [show (2:ℝ)*Fintype.card (Labels p n)+1=p by exact_mod_cast this]
    have pos : (0:ℝ)<pairs p := by exact_mod_cast Nat.mul_pos hp.pos (Nat.sub_pos_of_lt hp.one_lt)
    have frac : (numerator p:ℝ)/pairs p≤1 := (div_le_one pos).mpr (by
      exact_mod_cast PrimeFactors.PrimeSquareUniformFloor.numerator_le odd)
    have pr : 0≤(p:ℝ)-1 := sub_nonneg.mpr (by exact_mod_cast hp.one_le)
    have trivial := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right frac (Nat.cast_nonneg (Fintype.card (Labels p n)))) pr
    rw [A] at trivial ⊢
    nlinarith only [trivial]

/-- The first-power estimate uses the same normalization as the CRT product law. -/
theorem share {p n : ℕ} [Fact p.Prime] (odd : p≠2) (unit : ¬p∣n) :
    GuessTableOverlap.Share (fun s : Labels p n => weight n s.val) ((numerator p:ℝ)/pairs p) := by
  unfold GuessTableOverlap.Share GuessTableOverlap.tableMass GuessTableOverlap.overlap
  rw [←Nat.cast_sum,PrimeFactors.JointSumGuessFloor.sum_labels]
  exact lower odd unit

end PrimeFactors.FirstPowerGuessOverlap
