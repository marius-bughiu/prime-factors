import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Spacing of products of sorted natural-number pairs with one fixed sum. -/

namespace PrimeFactors.FactorSumProductCell

open Finset

/-- Moving the smaller factor from p to r increases the product by an
explicit amount. This form also gives monotonicity over natural numbers. -/
theorem product_identity {p q r s : ℕ} (pr : p ≤ r) (rs : r ≤ s)
    (sum_eq : p+q = r+s) : p*q + (r-p)*(q-r) = r*s := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le pr
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le rs
  have eq : q = p+d+e+d := by omega
  subst q
  rw [show p+d-p = d by omega, show p+d+e+d-(p+d) = e+d by omega]
  ring

/-- The product difference is at least the square of the displacement of
the smaller factor, including equality of the two smaller factors. -/
theorem spacing {p q r s : ℕ} (pr : p ≤ r) (rs : r ≤ s) (sum_eq : p+q = r+s) :
    r*s-p*q = (r-p)*(q-r) ∧ (r-p)^2 ≤ r*s-p*q := by
  have h := product_identity pr rs sum_eq
  have diff : r*s-p*q = (r-p)*(q-r) := by omega
  rw [diff, pow_two]
  exact ⟨rfl, Nat.mul_le_mul_left _ (by omega)⟩

/-- Knowing the smaller entry and the sum reconstructs a sorted pair
uniquely, even without knowing the product. -/
theorem first_injective {A : Finset (ℕ×ℕ)} {S : ℕ}
    (sum_eq : ∀ z ∈ A, z.1+z.2=S) : (A : Set (ℕ×ℕ)).InjOn Prod.fst := by
  intro x hx y hy eq
  have hx' := sum_eq x hx
  have hy' := sum_eq y hy
  exact Prod.ext eq (by change x.1=y.1 at eq; omega)

/-- At most floor(sqrt(W−1))+1 sorted pairs of one sum can have their
products in an arbitrary interval [L,L+W). No primality is required. -/
theorem interval_card (A : Finset (ℕ×ℕ)) (S L W : ℕ)
    (sorted : ∀ z ∈ A, z.1≤z.2) (sum_eq : ∀ z ∈ A, z.1+z.2=S)
    (interval : ∀ z ∈ A, L≤z.1*z.2 ∧ z.1*z.2<L+W) :
    A.card ≤ (W-1).sqrt+1 := by
  obtain empty|nonempty := A.eq_empty_or_nonempty
  · simp [empty]
  obtain ⟨a, ha, least⟩ := A.exists_min_image Prod.fst nonempty
  let code (z : ℕ×ℕ) := z.1-a.1
  have into (z : ℕ×ℕ) (hz : z∈A) : code z ∈ range ((W-1).sqrt+1) := by
    have apart := (spacing (least z hz) (sorted z hz)
      ((sum_eq a ha).trans (sum_eq z hz).symm)).2
    have lo := (interval a ha).1
    have hi := (interval z hz).2
    apply mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.le_sqrt'.mpr (by dsimp [code]; omega))
  have inj : (A : Set (ℕ×ℕ)).InjOn code := by
    intro x hx y hy eq
    have lx := least x hx
    have ly := least y hy
    apply first_injective sum_eq hx hy
    change x.1-a.1 = y.1-a.1 at eq
    change a.1≤x.1 at lx
    change a.1≤y.1 at ly
    omega
  simpa only [card_range] using card_le_card_of_injOn code into inj

/-- The equally spaced product blocks used by a product-only predictor. -/
theorem card_bound (A : Finset (ℕ×ℕ)) (S b W : ℕ)
    (sorted : ∀ z ∈ A, z.1≤z.2) (sum_eq : ∀ z ∈ A, z.1+z.2=S)
    (block : ∀ z ∈ A, b*W≤z.1*z.2 ∧ z.1*z.2<(b+1)*W) :
    A.card ≤ W.sqrt+1 := by
  apply (interval_card A S (b*W) W sorted sum_eq (by simpa [Nat.add_mul] using block)).trans
  exact Nat.add_le_add_right (Nat.sqrt_le_sqrt (Nat.sub_le W 1)) 1

/-- The sharper bound is attained at every positive width by positive sorted
pairs in an aligned block. The smaller entries in this construction are all
the integers from W through W+floor(sqrt(W−1)). -/
theorem sharp (W : ℕ) (positive : 0<W) :
    ∃ (S b : ℕ) (A : Finset (ℕ×ℕ)), A.card = (W-1).sqrt+1 ∧
      ∀ z ∈ A, 0<z.1 ∧ z.1≤z.2 ∧ z.1+z.2=S ∧
        b*W≤z.1*z.2 ∧ z.1*z.2<(b+1)*W := by
  let k := (W-1).sqrt
  let pair (i : ℕ) : ℕ×ℕ := (W+i, W+2*k-i)
  refine ⟨2*(W+k), W+2*k, (range (k+1)).image pair, ?_, ?_⟩
  · have inj : Function.Injective pair := fun _ _ h => Nat.add_left_cancel (congrArg Prod.fst h)
    rw [card_image_of_injective _ inj, card_range]
  · intro z hz
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
    have small := mem_range.mp hi
    have order : W+i ≤ W+2*k-i := by omega
    have total : (W+i)+(W+2*k-i) = 2*(W+k) := by omega
    refine ⟨by change 0<W+i; omega, order, total, ?_⟩
    have lower := product_identity (Nat.le_add_right W i) order
      (p:=W) (q:=W+2*k) (by omega)
    have upper := product_identity (p:=W+i) (q:=W+2*k-i) (r:=W+k) (s:=W+k)
      (by omega) (by omega) (by omega)
    have top : (W+k)*(W+k) = (W+2*k)*W+k^2 := by ring
    have narrow : k^2<W := by
      have h := Nat.sqrt_le' (W-1)
      dsimp [k]
      omega
    rw [Nat.mul_comm W (W+2*k)] at lower
    rw [top] at upper
    change _≤(W+i)*(W+2*k-i) ∧ (W+i)*(W+2*k-i)<_
    rw [Nat.add_mul (W+2*k) 1 W,one_mul]
    omega

end PrimeFactors.FactorSumProductCell
