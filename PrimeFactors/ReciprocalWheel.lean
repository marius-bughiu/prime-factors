import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace PrimeFactors.ReciprocalWheel

/-- The reciprocal pairing on the group of units modulo a wheel. -/
def partner {G : Type*} [CommGroup G] (n r : G) : G := n / r

theorem partner_partner {G : Type*} [CommGroup G] (n r : G) :
    partner n (partner n r) = r := div_div_cancel n r

theorem product_iff_partner {G : Type*} [CommGroup G] (n r s : G) :
    r * s = n ↔ s = partner n r := by
  constructor
  · rintro rfl
    simp [partner]
  · rintro rfl
    simp [partner]

/-- A rectangle contains every admissible pair in its two lanes after only
the block and modular constraint have been imposed. -/
def Covers {α β : Type*} (A : Finset α) (B : Finset β) (X : Finset α) (Y : Finset β) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, x ∈ X ∨ y ∈ Y

theorem covers_iff {α β : Type*} (A X : Finset α) (B Y : Finset β) :
    Covers A B X Y ↔ A ⊆ X ∨ B ⊆ Y := by
  constructor
  · intro h
    by_cases a : A ⊆ X
    · exact Or.inl a
    · obtain ⟨x,xa,xout⟩ := Finset.not_subset.mp a
      exact Or.inr (fun y yb => (h x xa y yb).resolve_left xout)
  · rintro (h | h) x xa y yb
    · exact Or.inl (h xa)
    · exact Or.inr (h yb)

/-- Index the columns by their unique companion residue. Per-component
minima add, and the cover attaining their sum is explicit. -/
theorem optimal {ι α β : Type*} [Fintype ι] (A : ι → Finset α) (B : ι → Finset β) :
    (∃ (X : ι → Finset α) (Y : ι → Finset β), (∀ i, Covers (A i) (B i) (X i) (Y i)) ∧
      (∑ i : ι, ((X i).card+(Y i).card))=∑ i : ι, min (A i).card (B i).card) ∧
    (∀ (X : ι → Finset α) (Y : ι → Finset β), (∀ i, Covers (A i) (B i) (X i) (Y i)) →
      (∑ i : ι, min (A i).card (B i).card) ≤ ∑ i : ι, ((X i).card+(Y i).card)) := by
  classical
  constructor
  · let X (i : ι) := if (A i).card ≤ (B i).card then A i else ∅
    let Y (i : ι) := if (A i).card ≤ (B i).card then ∅ else B i
    refine ⟨X,Y,?_,?_⟩
    · intro i
      rw [covers_iff]
      by_cases h : (A i).card ≤ (B i).card <;> simp [X,Y,h]
    · apply Finset.sum_congr rfl
      intro i _
      by_cases h : (A i).card ≤ (B i).card
      · simp [X,Y,h,min_eq_left h]
      · simp [X,Y,h,min_eq_right (le_of_not_ge h)]
  · intro X Y valid
    apply Finset.sum_le_sum
    intro i _
    rcases (covers_iff _ _ _ _).mp (valid i) with h | h
    · exact (min_le_left _ _).trans <| (Finset.card_le_card h).trans (Nat.le_add_right _ _)
    · exact (min_le_right _ _).trans <| (Finset.card_le_card h).trans (Nat.le_add_left _ _)

/-- Number of elements of one residue class on a half-open integer interval,
expressed as the difference of its final and initial quotient indices. -/
def lane (start len W r : ℤ) : ℤ := (start-1-r+len)/W-(start-1-r)/W

/-- A residue progression visits exactly the integer indices in this interval. -/
theorem lane_index {W : ℤ} (pos : 0 < W) (start len r j : ℤ) :
    (start ≤ r + W*j ∧ r + W*j < start+len) ↔
    (start-1-r)/W < j ∧ j ≤ (start-1-r+len)/W := by
  rw [Int.ediv_lt_iff_lt_mul pos, Int.le_ediv_iff_mul_le pos, mul_comm j W]
  omega

theorem lane_card (start len W r : ℤ) :
    (Finset.Ioc ((start-1-r)/W) ((start-1-r+len)/W)).card =
      (lane start len W r).toNat := Int.card_Ioc _ _

theorem lane_bounds (start len r : ℤ) {W : ℤ} (pos : 0<W) :
    len/W ≤ lane start len W r ∧ lane start len W r ≤ (len-1)/W+1 := by
  let k := start-1-r
  have eqn : k+len=(k%W+len)+W*(k/W) := by linarith [Int.emod_add_ediv k W]
  have norm : lane start len W r=(k%W+len)/W := by
    change (k+len)/W-k/W=_
    rw [eqn,Int.add_mul_ediv_left _ _ pos.ne']
    ring
  rw [norm]
  constructor
  · apply Int.ediv_le_ediv pos
    linarith [Int.emod_nonneg k pos.ne']
  · have h : k%W+len ≤ (len-1)+W*1 := by linarith [Int.emod_lt_of_pos k pos]
    simpa only [Int.add_mul_ediv_left _ _ pos.ne'] using Int.ediv_le_ediv pos h

/-- Enlarging the upper interval by at least W-1 makes every upper lane
at least as large as every lower lane. -/
theorem no_saving {W h k : ℤ} (pos : 0<W) (long : h+W-1 ≤ k)
    (s t r u : ℤ) : lane s h W r ≤ lane t k W u := by
  have hi := (lane_bounds s h r pos).2
  have lo := (lane_bounds t k u pos).1
  have bound : (h-1)+W*1 ≤ k := by linarith
  have mid := Int.ediv_le_ediv pos bound
  rw [Int.add_mul_ediv_left _ _ pos.ne'] at mid
  linarith

/-- With at least h-1 upper sites a directed class can save at most one
site, regardless of its two phases or the modular inverse permutation. -/
theorem one_per_class {W h k : ℤ} (pos : 0<W) (long : h-1 ≤ k)
    (s t r u : ℤ) : lane s h W r ≤ min (lane s h W r) (lane t k W u)+1 := by
  have hi := (lane_bounds s h r pos).2
  have lo := (lane_bounds t k u pos).1
  have mid := Int.ediv_le_ediv pos long
  omega

/-- Exact expansion of the real companion span. Its rounded integer
interval still contains at least b-a+w sites at this threshold. -/
theorem companion_length {a b N w : ℤ} (ap : 0<a) (ab : a ≤ b)
    (gain : w*a*b ≤ (b-a)*(N-a*b)) :
    b-a+w ≤ ⌊(N:ℝ)/a⌋-⌈(N:ℝ)/b⌉+1 := by
  have ar : (0:ℝ)<a := by exact_mod_cast ap
  have br : (0:ℝ)<b := by exact_mod_cast ap.trans_le ab
  have exp : (b:ℝ)-a+w ≤ (N:ℝ)/a-(N:ℝ)/b := by
    apply le_of_mul_le_mul_right (a := (a:ℝ)*b) _ (mul_pos ar br)
    have gr : (w:ℝ)*a*b ≤ ((b:ℝ)-a)*(N-a*b) := by exact_mod_cast gain
    field_simp
    nlinarith
  have h : (b:ℝ)-a+w < (⌊(N:ℝ)/a⌋:ℝ)-(⌈(N:ℝ)/b⌉:ℝ)+2 := by
    linarith [Int.lt_floor_add_one ((N:ℝ)/a),Int.ceil_lt_add_one ((N:ℝ)/b)]
  have hz : b-a+w < ⌊(N:ℝ)/a⌋-⌈(N:ℝ)/b⌉+2 := by exact_mod_cast h
  omega

/-- A threshold involving just lower endpoints suffices for no saving. -/
theorem span_sufficient {a b N W : ℤ} (ap : 0<a) (ab : a≤b) (below : b^2≤N)
    (wide : W*a≤(b-a)^2) : W*a*b ≤ (b-a)*(N-a*b) := by
  have h₁ := mul_le_mul_of_nonneg_right wide (ap.trans_le ab).le
  have h₂ := mul_le_mul_of_nonneg_left below (sub_nonneg.mpr ab)
  nlinarith only [h₁,h₂]

/-- A wide smaller-factor block permits no improvement from any choice of
its partner lane, including choices made separately for every residue. -/
theorem whole_lower_cheapest {a b N W : ℤ} (wp : 0<W) (ap : 0<a) (ab : a≤b)
    (below : b^2≤N) (wide : W*a≤(b-a)^2) (r s : ℤ) :
    lane a (b-a+1) W r ≤ lane ⌈(N:ℝ)/b⌉ (⌊(N:ℝ)/a⌋-⌈(N:ℝ)/b⌉+1) W s := by
  apply no_saving wp
  have k := companion_length ap ab (span_sufficient ap ab below wide)
  omega

/-- At 2,048 bits even a wheel of size 2^1020 is too small to change any
class count in favor of its companion on the entire balanced band. Here
a is the rounded lower endpoint and b the rounded upper endpoint. -/
theorem full_width {a b N : ℤ} (large : 2^1023≤a) (bp : 0≤b)
    (lower : 2*(a-1)^2≤N) (upper : N<(b+1)^2) : 2^1020*a≤(b-a)^2 := by
  have ha : 96≤a := (by norm_num : (96:ℤ)≤2^1023).trans large
  have growth : 7*(a-1)<5*(b+1) := by
    apply (sq_lt_sq₀ (by linarith) (by linarith)).mp
    nlinarith only [lower,upper,sq_nonneg (a-1)]
  have span : 3*a≤8*(b-a) := by omega
  have squared := pow_le_pow_left₀ (by linarith : 0≤3*a) span 2
  have base : 64*2^1020 ≤ 9*a := by
    linarith only [large,show (64:ℤ)*2^1020 ≤ 9*2^1023 by norm_num]
  have scaled := mul_le_mul_of_nonneg_right base (by linarith : 0≤a)
  nlinarith only [scaled,squared]

/-- Per-lane savings add to at most the number of explicitly represented
box-class pairs. This is independent of the residue pairing. -/
theorem total_saving {ι κ : Type*} [Fintype ι] [Fintype κ]
    (l h : ι → κ → ℤ) (bound : ∀ i j, l i j ≤ min (l i j) (h i j)+1) :
    (∑ i, ∑ j, l i j) - (∑ i, ∑ j, min (l i j) (h i j)) ≤
      (Fintype.card ι : ℤ)*(Fintype.card κ : ℤ) := by
  simp_rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ _i : ι, ∑ _j : κ, (1:ℤ) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      linarith only [bound i j]
    _ = _ := by simp [nsmul_eq_mul]

/-- The additive cost surrogate with explicit residue and box enumeration
cannot beat the original square-root count using this pruning alone. -/
theorem cost_barrier {f k old kept : ℝ} (fp : 0≤f) (kp : 0≤k) (op : 0≤old)
    (sp : 0≤kept) (saving : old-kept≤f*k) :
    2*Real.sqrt old ≤ f+k+2*Real.sqrt kept := by
  have sk := Real.sqrt_nonneg kept
  have so' := Real.sqrt_nonneg old
  apply (sq_le_sq₀ (by linarith) (by linarith)).mp
  nlinarith [sq_nonneg (f-k), Real.sq_sqrt sp, Real.sq_sqrt op,
    mul_nonneg fp sk, mul_nonneg kp sk]

end PrimeFactors.ReciprocalWheel
