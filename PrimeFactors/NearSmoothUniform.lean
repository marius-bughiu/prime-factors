import PrimeFactors.NearSmoothSumWindows

/-! Uniform count of the seven-row windows at absolute sum tolerance at most
2^435. The least feasible center is the only one that can fail the gap test. -/

namespace PrimeFactors.NearSmoothUniform

open Finset Polynomial SmoothSumSelector NearSmoothSumWindows
open SmoothCenterSpacing (X)

set_option exponentiation.threshold 5000

private theorem exp_three (a b : ℕ) : (2^a*3^b).factorization 3=b := by
  simp [Nat.factorization_mul (pow_ne_zero a (by decide : 2≠0))
    (pow_ne_zero b (by decide : 3≠0)),Nat.factorization_pow,Nat.prime_two.factorization,
    Nat.prime_three.factorization,Finsupp.smul_apply]

theorem exponent_injective : Function.Injective candidate := by
  intro a b same
  exact (exp_three _ _).symm.trans ((congrArg (fun n : ℕ => n.factorization 3) same).trans
    (exp_three _ _))

private theorem kept {n E b : ℕ} (keepB : b∈menu n E) : b<647 ∧
    n≤(sumHi b E/2)^2 ∧ sumLo b E*X<n+X^2 := by
  obtain ⟨hb,h⟩ := mem_filter.mp keepB
  have idx := mem_range.mp hb
  exact ⟨idx,by simpa only [NearSmoothSumWindows.keep,SmoothCenterSpacing.fast_correct idx,decide_eq_true_eq,sumHi,sumLo,SmoothCenterSpacing.X] using h⟩

private theorem extended_square {u n s : ℕ} (pos : 0<u) (low : u^2≤2*n) (high : n≤u^2)
    (slope : s*u≤n+u^2) : 2*s^2≤9*n := by
  have sq := Nat.pow_le_pow_left slope 2
  have comp : 2*(n+u^2)^2 ≤ 9*n*u^2 := by
    zify at low high ⊢
    have a : (0:ℤ)≤2*n-(u:ℤ)^2 := by linarith only [low]
    have b : (0:ℤ)≤2*(u:ℤ)^2-n := by nlinarith only [high,sq_nonneg (u:ℤ)]
    nlinarith only [mul_nonneg a b]
  apply Nat.le_of_mul_le_mul_right (c:=u^2) _ (Nat.pow_pos pos)
  nlinarith only [sq,comp]

private theorem keep_possible {n E b : ℕ} (large : 2^2047≤n) (h : b∈menu n E) :
    SmoothCenterSpacing.possible n E (candidate b) := by
  obtain ⟨_,reach,cap⟩ := kept h
  have clip : sumHi b E ≤ candidate b+E := min_le_left ..
  have clip2 : sumHi b E ≤ 2*X := by
    exact (min_le_right ..).trans_eq (by decide +kernel)
  have midpoint : 2*(sumHi b E/2) ≤ candidate b+E := by omega
  have top : n≤X^2 := reach.trans (Nat.pow_le_pow_left (by omega : sumHi b E/2≤X) 2)
  have low : X^2≤2*n := (by decide +kernel : X^2≤2*2^2047).trans (Nat.mul_le_mul_left 2 large)
  refine ⟨?_,extended_square (by decide +kernel : 0<X) low top cap.le⟩
  have square := Nat.pow_le_pow_left midpoint 2
  nlinarith only [reach,square]

/-- At most 56 active exponents for every sufficiently large input with this
tolerance. This count already holds for the wider, cheaper first-stage menu. -/
theorem menu_card {n E : ℕ} (large : 2^2047≤n) (small : E≤2^435) :
    (menu n E).card ≤ 56 := by
  rw [←card_image_of_injective (menu n E) exponent_injective]
  apply SmoothCenterSpacing.balanced_card n E (small.trans (by decide +kernel))
  intro c hc
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hc
  exact ⟨SmoothCenterSpacing.candidate_mem (kept hb).1,keep_possible large hb⟩

theorem active_card {n E : ℕ} (large : 2^2047≤n) (small : E≤2^435) :
    (active n E).card≤56 := (card_le_card (filter_subset ..)).trans (menu_card large small)

private theorem shifted_gap {v A K G n : ℕ} (start : 4*n≤v^2) (space : v+K≤2*A)
    (scale : 2*G^2≤v*K) : n+G^2≤A^2 := by
  have grow := Nat.pow_le_pow_left space 2
  nlinarith only [start,scale,grow,Nat.zero_le (K^2)]

/-- A smaller feasible center forces a half-gap of at least 2^1018 at the
left midpoint of the later band, before inspecting a single hidden factor. -/
theorem gap_of_smaller {n E a b : ℕ} (small : E≤2^435)
    (older : a∈menu n E) (idx : b<647) (lt : candidate a<candidate b) :
    n+(2^1018)^2 ≤ (leftHalf n (sumLo b E))^2 := by
  obtain ⟨ha,reach,_⟩ := kept older
  have sep := SmoothCenterSpacing.separation (SmoothCenterSpacing.candidate_mem ha)
    (SmoothCenterSpacing.candidate_mem idx) lt
  have smallSum : 977*(2^1014+2*E)≤X := by
    have num : 977*(2^1014+2*2^435)≤X := by decide +kernel
    omega
  have moved : candidate a+E+2^1014 ≤ candidate b-E := by omega
  have span : sumLo b E ≤ 2*leftHalf n (sumLo b E) := by
    have up := le_max_left ((sumLo b E+1)/2) (ceilSqrt n)
    change _ ≤ 2*max _ _
    omega
  have floor := (candidate_bounds ha).1
  have cost : 2*(2^1018)^2 ≤ (candidate a+E)*2^1014 := by
    have easy : 2*(2^1018)^2 ≤ 2^1024*2^1014 := by decide +kernel
    exact easy.trans (Nat.mul_le_mul_right _ (floor.trans (Nat.le_add_right ..)))
  have hi : sumHi a E ≤ candidate a+E := min_le_left ..
  have upper : 2*(sumHi a E/2)≤candidate a+E := by omega
  have square := Nat.pow_le_pow_left upper 2
  exact shifted_gap (v:=candidate a+E) (K:=2^1014) (by nlinarith only [reach,square])
    (moved.trans span) cost

/-- The public half-gap check may fail on at most one active exponent. -/
noncomputable def bad (n E : ℕ) : Finset ℕ := (active n E).filter fun b =>
  (leftHalf n (sumLo b E))^2 < n+(2^1018)^2

theorem bad_card (n E : ℕ) (small : E≤2^435) : (bad n E).card≤1 := by
  apply card_le_one.mpr
  intro a ha b hb
  obtain ⟨ha,failA⟩ := mem_filter.mp ha
  obtain ⟨hb,failB⟩ := mem_filter.mp hb
  have ma := (mem_filter.mp ha).1
  have mb := (mem_filter.mp hb).1
  rcases lt_trichotomy (candidate a) (candidate b) with ab|eq|ba
  · exact False.elim ((not_lt_of_ge (gap_of_smaller small ma (kept mb).1 ab)) failB)
  · exact exponent_injective eq
  · exact False.elim ((not_lt_of_ge (gap_of_smaller small mb (kept ma).1 ba)) failA)

/-- Every active band outside the one possible exception fits one equation. -/
theorem regular_fit {n E b : ℕ} (small : E≤2^435) (member : b∈active n E)
    (regular : b∉bad n E) : upper n (sumHi b E)-lower n (sumLo b E)≤4*radius := by
  have order := (mem_filter.mp member).2.1
  apply tolerances _ _ _ order
  right; left
  refine ⟨small,?_⟩
  have h : ¬(leftHalf n (sumLo b E))^2<n+(2^1018)^2 :=
    fun h => regular (mem_filter.mpr ⟨member,h⟩)
  omega

/-- Cardinal bound for the endpoint width actually tested. A failing lower
gap test may still pass this directed endpoint test. -/
theorem unfit_card (n E : ℕ) (small : E≤2^435) :
    ((active n E).filter fun b => 4*radius<upper n (sumHi b E)-lower n (sumLo b E)).card≤1 := by
  apply (card_le_card ?_).trans (bad_card n E small)
  intro b h
  obtain ⟨member,too⟩ := mem_filter.mp h
  by_contra no
  exact (not_lt_of_ge (regular_fit small member no)) too

/-- One nonzero polynomial with at most six integer roots covers all the
promised factors in any active band outside the public exceptional set. -/
theorem regular_equation {n E b : ℕ} (large : 2^2047≤n) (cop : n.Coprime 45360)
    (odd : Odd n) (small : E≤2^435) (member : b∈active n E) (regular : b∉bad n E) :
    ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤6 ∧ ∀ p q : ℕ,
      p*q=n → p≤q → p≤2^1024 → sumLo b E≤p+q → p+q≤sumHi b E →
      ∃ x : ℤ, (q:ℤ)=(center n (sumLo b E) (sumHi b E):ℤ)+2*x ∧
        |x|≤(windowRadius n (sumLo b E) (sumHi b E):ℤ) ∧ F.eval x=0 :=
  one_window large cop odd (regular_fit small member regular)

end PrimeFactors.NearSmoothUniform
