import PrimeFactors.CircleMarkMidcutSampling
import Mathlib.Data.Fintype.Perm

/-! Finite-population correction for the empirical mean. A uniform permutation
of the population fills a fixed set of distinct sample positions. -/
namespace PrimeFactors.CircleMarkMidcutWithoutReplacement

open Finset
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- Mean square error of the usual average with distinct, uniformly sampled entries. -/
noncomputable def distinctError (r : α → ℚ) (μ : ℚ) (S : Finset α) : ℚ :=
  𝔼 σ : Equiv.Perm α, ((∑ i∈S, r (σ i))/(S.card:ℚ)-μ)^2

private theorem single (f : α → ℚ) (i : α) : (𝔼 σ : Equiv.Perm α, f (σ i))=𝔼 j, f j := by
  have swap (j : α) : (𝔼 σ : Equiv.Perm α, f (σ i))=𝔼 σ : Equiv.Perm α, f (σ j) := by
    apply Fintype.expect_equiv (Equiv.mulRight (Equiv.swap i j))
    intro σ
    simp [Equiv.Perm.mul_apply]
  calc
    _ = 𝔼 j : α, 𝔼 σ : Equiv.Perm α, f (σ j) := by simp_rw [←swap]; rw [Fintype.expect_const]
    _ = 𝔼 σ : Equiv.Perm α, 𝔼 j, f (σ j) := expect_comm ..
    _ = _ := by
      have each (σ : Equiv.Perm α) : (𝔼 j, f (σ j))=𝔼 j, f j :=
        Fintype.expect_equiv σ _ _ (fun _ => rfl)
      simp_rw [each,Fintype.expect_const]

private noncomputable def cross (f : α → ℚ) (i j : α) : ℚ :=
  𝔼 σ : Equiv.Perm α, f (σ i)*f (σ j)

private theorem diagonal (f : α → ℚ) (i : α) : cross f i i = 𝔼 x, (f x)^2 := by
  calc _ = 𝔼 σ : Equiv.Perm α, (f (σ i))^2 := by simp only [cross,sq]
       _ = _ := single (fun x => (f x)^2) i

private theorem off_diagonal (f : α → ℚ) (zero : ∑ x, f x = 0)
    (big : 1 < Fintype.card α) {i j : α} (ne : i≠j) :
    cross f i j = -(𝔼 x, (f x)^2)/((Fintype.card α:ℚ)-1) := by
  have same (k : α) (hk : i≠k) : cross f i k = cross f i j := by
    unfold cross
    apply Fintype.expect_equiv (Equiv.mulRight (Equiv.swap k j))
    intro σ
    simp [Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hk ne]
  have row : (∑ k, cross f i k) = 0 := by
    unfold cross
    rw [←expect_sum_comm]
    simp_rw [←mul_sum]
    simp [Equiv.sum_comp,zero]
  have erased := sum_erase_add univ (cross f i) (mem_univ i)
  have tally : (∑ k∈univ.erase i, cross f i k) = ((Fintype.card α:ℚ)-1)*cross f i j := by
    calc _ = ∑ _k∈univ.erase i, cross f i j := sum_congr rfl fun k km => same k (ne_of_mem_erase km).symm
         _ = _ := by simp [Nat.cast_sub (by omega : 1≤Fintype.card α)]
  rw [tally,diagonal,row] at erased
  apply (eq_div_iff (sub_ne_zero.mpr (by exact_mod_cast big.ne' : (Fintype.card α:ℚ)≠1))).mpr
  linarith

/-- Variance of an ordinary empirical mean under simple random sampling without
replacement. The set S fixes the number of distinct positions in the permutation. -/
theorem correction (r : α → ℚ) {μ : ℚ} (mean : (𝔼 x, r x)=μ) (S : Finset α)
    (pos : 0 < S.card) (big : 1 < Fintype.card α) :
    distinctError r μ S =
      (𝔼 x, (r x-μ)^2)*((Fintype.card α:ℚ)-S.card)/((S.card:ℚ)*(Fintype.card α-1)) := by
  let f (x : α) := r x-μ
  let V : ℚ := 𝔼 x, (f x)^2
  let N : ℚ := Fintype.card α
  let J : ℚ := S.card
  have jpos : 0<J := by dsimp [J]; exact_mod_cast pos
  have np : 1<N := by dsimp [N]; exact_mod_cast big
  have centered : (𝔼 x, f x)=0 := by simp [f,expect_sub_distrib,Fintype.expect_const,mean]
  have zero : ∑ x, f x = 0 := by
    rw [Fintype.expect_eq_sum_div_card,div_eq_zero_iff] at centered
    exact centered.resolve_right (by exact_mod_cast (by omega : Fintype.card α≠0))
  have oneRow (i : α) (hi : i∈S) : ∑ j∈S, cross f i j = V+(J-1)*(-V/(N-1)) := by
    rw [←sum_erase_add _ _ hi,diagonal]
    have er : ∑ j∈S.erase i, cross f i j = ∑ _j∈S.erase i, -V/(N-1) :=
      sum_congr rfl fun j jm => off_diagonal f zero big (ne_of_mem_erase jm).symm
    rw [er,sum_const,nsmul_eq_mul,card_erase_of_mem hi,Nat.cast_sub pos,Nat.cast_one]
    change (J-1)*_+V=_
    ring
  have total : (𝔼 σ : Equiv.Perm α, (∑ i∈S, f (σ i))^2) = J*(V+(J-1)*(-V/(N-1))) := by
    simp_rw [sq,sum_mul,mul_sum]
    rw [expect_sum_comm]
    calc _ = ∑ i∈S, ∑ j∈S, cross f i j := sum_congr rfl fun i _ => expect_sum_comm ..
         _ = ∑ _i∈S, (V+(J-1)*(-V/(N-1))) := sum_congr rfl oneRow
         _ = _ := by rw [sum_const,nsmul_eq_mul]
  have move (σ : Equiv.Perm α) : (∑ i∈S, r (σ i))/(S.card:ℚ)-μ =
      (∑ i∈S, f (σ i))/J := by
    simp only [f,sum_sub_distrib,sum_const,nsmul_eq_mul,J]
    field_simp [show (S.card:ℚ)≠0 by exact_mod_cast pos.ne']
  unfold distinctError
  simp_rw [move,div_pow]
  rw [←expect_div,total]
  change _ = V*(N-J)/(J*(N-1))
  field_simp [jpos.ne', (sub_pos.mpr np).ne']
  ring

/-- A single-draw variance exceeding the population size forces any empirical
mean with mean square error below one to use strictly more than half the entries. -/
theorem more_than_half (r : α → ℚ) {μ : ℚ} (mean : (𝔼 x, r x)=μ) (S : Finset α)
    (pos : 0<S.card) (big : 1<Fintype.card α)
    (variance : (Fintype.card α:ℚ)<𝔼 x, (r x-μ)^2)
    (precise : distinctError r μ S < 1) : Fintype.card α < 2*S.card := by
  rw [correction r mean S pos big] at precise
  have jp : (0:ℚ)<S.card := by exact_mod_cast pos
  have np : (1:ℚ)<Fintype.card α := by exact_mod_cast big
  have lt := (div_lt_iff₀ (mul_pos jp (sub_pos.mpr np))).mp precise
  by_contra! few
  have gap : (S.card:ℚ) ≤ (Fintype.card α:ℚ)-S.card := by
    have h : 2*(S.card:ℚ)≤Fintype.card α := by exact_mod_cast few
    linarith
  have scale := mul_le_mul_of_nonneg_left gap (show 0≤𝔼 x, (r x-μ)^2 by linarith)
  have singleDraw := mul_lt_mul_of_pos_right variance jp
  nlinarith only [lt,scale,singleDraw,jp]

open CircleMarkMidcutSampling

private theorem population_size {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] :
    1 < Fintype.card (ZMod (p*q)) := by
  rw [ZMod.card]
  exact hp.out.one_lt.trans_le (Nat.le_mul_of_pos_right _ hq.out.pos)

/-- Exact mean square error of the signed midpoint estimate from distinct residues. -/
theorem midpoint_error {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) (S : Finset (ZMod (p*q))) (pos : 0<S.card) :
    distinctError (estimate (p*q)) p S =
      variance (p*q) p * (((p*q:ℕ):ℚ)-S.card)/((S.card:ℚ)*(((p*q:ℕ):ℚ)-1)) := by
  rw [correction _ (unbiased order op oq) S pos population_size, ZMod.card,
    single_variance order op oq]

/-- RMS error below one still requires more than half the entire residue
population when the sample contains no repeats. -/
theorem midpoint_more_than_half {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) (S : Finset (ZMod (p*q))) (pos : 0<S.card)
    (accuracy : Real.sqrt (distinctError (estimate (p*q)) p S : ℝ) < 1) :
    p*q < 2*S.card := by
  have lt := (Real.sqrt_lt' (by norm_num : (0:ℝ)<1)).mp accuracy
  norm_num at lt
  have bound := more_than_half (estimate (p*q)) (unbiased order op oq) S pos population_size
    (by rw [ZMod.card,single_variance order op oq]; exact variance_gt_product order op oq)
    (by exact_mod_cast lt)
  simpa only [ZMod.card] using bound

end PrimeFactors.CircleMarkMidcutWithoutReplacement
