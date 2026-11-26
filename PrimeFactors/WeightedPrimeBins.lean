import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

/-! Bounds on the number of distinct primes in the intervals used to price
squarefree supports, obtained by counting admissible residues modulo a wheel. -/
namespace PrimeFactors.WeightedPrimeBins
open Finset

/-- Prefix count for a fixed set of allowable residues. -/
noncomputable def residueCount (W : ℕ) (R : Finset ℕ) (n : ℕ) : ℕ :=
  (n/W)*R.card+(R.filter (· < n%W)).card

private noncomputable def accepted (W : ℕ) (R : Finset ℕ) (n : ℕ) :=
  (range n).filter (fun a => a%W∈R)

/-- Counting complete periods and the final partial period is exact, including
at a multiple of the wheel modulus. -/
theorem prefix_exact {W : ℕ} (wp : 0<W) (R : Finset ℕ) (res : R ⊆ range W) (n : ℕ) :
    (accepted W R n).card=residueCount W R n := by
  let full := range (n/W) ×ˢ R
  let tail := {n/W} ×ˢ (R.filter (· < n%W))
  have disj : Disjoint full tail := by
    apply disjoint_left.mpr
    intro i hi ht
    have l := mem_range.mp (mem_product.mp hi).1
    have e := mem_singleton.mp (mem_product.mp ht).1
    omega
  have hq (a : ℕ) (ha : a<n) : a/W≤n/W := Nat.div_le_div_right ha.le
  have nq := Nat.div_add_mod n W
  have count : (accepted W R n).card=(full∪tail).card := by
    apply card_bij' (fun a _ => (a/W,a%W)) (fun i _ => W*i.1+i.2)
    · intro a ha
      obtain ⟨ha,hr⟩ := mem_filter.mp ha
      have lt := mem_range.mp ha
      rcases (hq a lt).lt_or_eq with below | eq
      · exact mem_union_left _ (mem_product.mpr ⟨mem_range.mpr below,hr⟩)
      · have aq := Nat.div_add_mod a W
        rw [eq] at aq
        exact mem_union_right _ (mem_product.mpr ⟨mem_singleton.mpr eq,mem_filter.mpr ⟨hr,by omega⟩⟩)
    · intro i hi
      rcases mem_union.mp hi with block | last
      · obtain ⟨hq,hr⟩ := mem_product.mp block
        have h := Nat.mul_le_mul_left W (mem_range.mp hq)
        rw [Nat.mul_succ] at h
        have below := mem_range.mp (res hr)
        exact mem_filter.mpr ⟨mem_range.mpr (by omega),by simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt below] using hr⟩
      · obtain ⟨hq,hr⟩ := mem_product.mp last
        have eq := mem_singleton.mp hq
        obtain ⟨hr,lt⟩ := mem_filter.mp hr
        have below := mem_range.mp (res hr)
        exact mem_filter.mpr ⟨mem_range.mpr (by rw [eq]; omega),by simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt below] using hr⟩
    · exact fun a _ => Nat.div_add_mod a W
    · intro i hi
      have hr : i.2∈R := (mem_union.mp hi).elim (fun h => (mem_product.mp h).2)
        (fun h => (mem_filter.mp (mem_product.mp h).2).1)
      have lt := mem_range.mp (res hr)
      exact Prod.ext (by simp [Nat.mul_add_div wp, Nat.div_eq_of_lt lt])
        (by simp [Nat.mul_add_mod,Nat.mod_eq_of_lt lt])
  rw [count,card_union_of_disjoint disj]
  simp [full,tail,residueCount]

/-- An interval sieve can use the difference of two prefix counts for any
residue set containing every candidate. No independence assumption enters. -/
theorem interval {W lo hi : ℕ} (wp : 0<W) (le : lo≤hi) (R S : Finset ℕ)
    (res : R ⊆ range W) (inside : ∀ a∈S, lo≤a ∧ a<hi ∧ a%W∈R) :
    S.card≤residueCount W R hi-residueCount W R lo := by
  have sub : S∪accepted W R lo ⊆ accepted W R hi := by
    intro a ha
    rcases mem_union.mp ha with aIn|early
    · obtain ⟨_,bound,ok⟩ := inside a aIn
      exact mem_filter.mpr ⟨mem_range.mpr bound,ok⟩
    · obtain ⟨b,ok⟩ := mem_filter.mp early
      exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp b).trans_le le),ok⟩
  have disj : Disjoint S (accepted W R lo) := by
    apply disjoint_left.mpr
    intro a h low
    exact (not_lt_of_ge (inside a h).1) (mem_range.mp (mem_filter.mp low).1)
  have h := card_le_card sub
  rw [card_union_of_disjoint disj,prefix_exact wp R res lo,prefix_exact wp R res hi] at h
  omega

/-- A prime larger than the wheel modulus occupies one of its coprime classes. -/
theorem prime_residue {W p : ℕ} (wp : 0<W) (prime : p.Prime) (large : W<p) :
    p%W∈(range W).filter (fun t => t.Coprime W) := by
  have cop := prime.coprime_iff_not_dvd.mpr (fun div => (not_le_of_gt large) (Nat.le_of_dvd wp div))
  exact mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ wp),by
    rw [Nat.coprime_iff_gcd_eq_one,←Nat.gcd_rec]
    exact cop.symm⟩

end PrimeFactors.WeightedPrimeBins
