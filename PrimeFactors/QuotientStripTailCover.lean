import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

namespace PrimeFactors.QuotientStripTailCover

/-- Every rational label between the first upper endpoint and the last lower
endpoint belongs to some interval, as soon as consecutive intervals overlap
in the direction of travel. Monotonicity of the endpoints is unnecessary. -/
theorem chain_cover {α : Type*} [LinearOrder α] (lo hi : ℕ → α) (n : ℕ) (z : α)
    (start : z ≤ hi 0) (finish : lo n ≤ z) (adj : ∀ i < n, lo i ≤ hi (i+1)) :
    ∃ i ≤ n, lo i ≤ z ∧ z ≤ hi i := by
  induction n with
  | zero => exact ⟨0, Nat.le_refl _, finish, start⟩
  | succ n ih =>
    by_cases inPrev : lo n ≤ z
    · obtain ⟨i,hin,hz⟩ := ih inPrev fun j hj => adj j (by omega)
      exact ⟨i,by omega,hz⟩
    · exact ⟨n+1, Nat.le_refl _, finish, (le_of_not_ge inPrev).trans (adj n (by omega))⟩

/-- If the total covered range is more than 24K wide, K different labels
in any prescribed residue class mod 24 must be processed. These labels also
give distinct integer discriminants when the range stays positive. -/
theorem many_distinct_labels (lo hi : ℕ → ℚ) (n K : ℕ) (base : ℚ) (c N : ℤ)
    (pos : 0<base) (last : lo n ≤ base) (room : base+24*(K:ℚ) ≤ hi 0)
    (adj : ∀ i < n, lo i ≤ hi (i+1)) :
    ∃ z : Fin K → ℤ, Function.Injective (fun j => (z j)^2-4*N) ∧
      ∀ j, z j ≡ c [ZMOD 24] ∧ base ≤ (z j:ℚ) ∧
        ∃ i ≤ n, lo i ≤ (z j:ℚ) ∧ (z j:ℚ) ≤ hi i := by
  let t : ℤ := ⌈(base-(c:ℚ))/24⌉
  let z (j : Fin K) : ℤ := c+24*(t+(j:ℕ))
  have lower := Int.le_ceil ((base-(c:ℚ))/24)
  have upper := Int.ceil_lt_add_one ((base-(c:ℚ))/24)
  change _ ≤ (t:ℚ) at lower
  change (t:ℚ) < _ at upper
  have bounds (j : Fin K) : base ≤ (z j:ℚ) ∧ (z j:ℚ) ≤ hi 0 := by
    have jp : 0 ≤ ((j:ℕ):ℚ) := by positivity
    have jk : ((j:ℕ):ℚ)+1 ≤ (K:ℚ) := by exact_mod_cast (show (j:ℕ)+1≤K from j.isLt)
    dsimp only [z]; push_cast
    constructor <;> linarith
  refine ⟨z, ?_, ?_⟩
  · intro j k eqn
    have jpos : 0 < z j := by exact_mod_cast pos.trans_le (bounds j).1
    have kpos : 0 < z k := by exact_mod_cast pos.trans_le (bounds k).1
    have sqs : z j ^ 2 = z k ^ 2 := sub_left_inj.mp eqn
    have same := ((sq_eq_sq_iff_abs_eq_abs _ _).mp sqs)
    rw [abs_of_pos jpos,abs_of_pos kpos] at same
    dsimp only [z] at same
    apply Fin.ext
    omega
  · intro j
    refine ⟨?_,(bounds j).1,chain_cover lo hi n _ (bounds j).2 (last.trans (bounds j).1) adj⟩
    rw [Int.modEq_iff_dvd]
    exact ⟨-(t+(j:ℕ)), by dsimp only [z]; ring⟩

end PrimeFactors.QuotientStripTailCover
