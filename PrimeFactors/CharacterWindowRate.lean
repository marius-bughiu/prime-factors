import PrimeFactors.CharacterWindowMoment

/-! Certify a common simultaneous-character rate on the entire physical factor
window by checking one inequality with the shortest and longest lane lengths. -/
namespace PrimeFactors.CharacterWindowRate
open Finset TwoCharacterWindow

/-- Number of candidate positions in the sixteen unit classes modulo 60. -/
noncomputable def positions (lo hi : ℕ) : ℕ := ∑ w ∈ wheel, rowLength lo hi w

/-- Number of positions surviving the whole supplied family of character tests. -/
noncomputable def passes {k : ℕ} (D : Fin k → ℕ) (lo hi : ℕ) : ℕ :=
  ∑ w ∈ wheel, (CharacterWindowMoment.hits D (rowStart lo w) 60 (rowLength lo hi w)).card

/-- Every smaller factor satisfying the public upper bound on the larger factor
is represented in a surviving row. The discriminant roots can be certified
directly on the input, before any factor is known. -/
theorem factors_located {k n p q B : ℕ} (D : Fin k → ℕ) (eq : n=p*q) (positive : 0<p)
    (ordered : p≤q) (bounded : q≤B) (wheelUnit : p.Coprime 60) (odd : Odd p)
    (three : ∀ i, D i%4=3) (cop : ∀ i, n.Coprime (D i))
    (root : ∀ i, IsSquare (-(D i : ZMod n))) :
    ∃ w∈wheel, ∃ j∈CharacterWindowMoment.hits D (rowStart (lower n B) w) 60
      (rowLength (lower n B) n.sqrt w), p=rowStart (lower n B) w+60*j := by
  obtain ⟨w, wh, j, inside, point⟩ := locate (lo:=lower n B) (hi:=n.sqrt) (f:=p)
    (by
      have qp : 0<q := positive.trans_le ordered
      have bp : 0<B := qp.trans_le bounded
      apply (Nat.div_lt_iff_lt_mul bp).mpr
      rw [eq]
      exact (Nat.sub_lt (Nat.mul_pos positive qp) (by decide)).trans_le (Nat.mul_le_mul_left p bounded))
    (by rw [eq]; exact Nat.le_sqrt.mpr (Nat.mul_le_mul_left p ordered)) wheelUnit
  have divisor : p∣n := eq ▸ dvd_mul_right p q
  exact ⟨w, wh, j, CharacterWindowMoment.divisor_mem D three cop root odd divisor point.symm inside, point⟩

/-- Aggregate the Pólya–Vinogradov/second-moment estimate. The minimum lane
length L and the ceiling L+1 suffice, so a concrete receipt only needs one
integer comparison for the whole wheel, independently of the number of moduli. -/
theorem window {k : ℕ} (D r : Fin k → ℕ) (lo hi L t H C₁ C₂ scale cap : ℕ)
    (pv : PublishedPV) (large : ∀ i, 100≤D i) (three : ∀ i, D i%4=3)
    (cop : Pairwise fun i j => (D i).Coprime (D j)) (stride : ∀ i, Nat.Coprime 60 (D i))
    (rad : ∀ i, D i≤(r i)^2) (bits : ∀ i, D i≤2^H)
    (one : 5220+347*H≤2220*C₁) (two : 5220+694*H≤2220*C₂)
    (nonempty : lo≤hi) (length : (hi-lo+1)/60=L) (positive : 0<t+k)
    (numeric : (scale:ℤ)*((((t:ℤ)^2+k)*(L+1)) + 2*t*C₁*(∑ i, (r i : ℤ)) +
      C₂*((∑ i, (r i:ℤ))^2 - ∑ i, (r i:ℤ)^2)) ≤ (cap:ℤ)*L*((t:ℤ)+k)^2) :
    scale*passes D lo hi ≤ cap*positions lo hi := by
  rw [passes,positions,Finset.mul_sum,Finset.mul_sum]
  apply sum_le_sum
  intro w _
  let l := rowLength lo hi w
  let hits := (CharacterWindowMoment.hits D (rowStart lo w) 60 l).card
  let A := ((t:ℤ)+k)^2
  let B := (t:ℤ)^2+k
  let E := 2*(t:ℤ)*C₁*(∑ i, (r i:ℤ)) + C₂*((∑ i, (r i:ℤ))^2 - ∑ i, (r i:ℤ)^2)
  have z := CharacterWindowMoment.jacobi_row_budget D r (rowStart lo w) 60 l t H C₁ C₂
    pv large three cop stride rad bits one two
  have row : (hits:ℤ)*A ≤ B*l+E := by simpa only [hits,A,B,E,add_assoc] using z
  have money : (scale:ℤ)*(B*(L+1)+E) ≤ (cap:ℤ)*L*A := by
    simpa only [A,B,E,add_assoc] using numeric
  have lens := lengths (r:=w) nonempty
  rw [length] at lens
  have zlo : (L:ℤ)≤l := by exact_mod_cast lens.1
  have zhi : (l:ℤ)≤L+1 := by exact_mod_cast lens.2
  have aPos : 0<A := by
    have pt : (0:ℤ)<(t:ℤ)+k := by exact_mod_cast positive
    exact sq_pos_of_pos pt
  have bPos : 0≤B := by dsimp [B]; positivity
  have result : ((scale:ℤ)*hits)*A ≤ ((cap:ℤ)*l)*A := calc
    _ = scale*((hits:ℤ)*A) := by ring
    _ ≤ scale*(B*l+E) := mul_le_mul_of_nonneg_left row (by positivity)
    _ ≤ scale*(B*(L+1)+E) := mul_le_mul_of_nonneg_left
      (add_le_add_right (mul_le_mul_of_nonneg_left zhi bPos) E) (by positivity)
    _ ≤ cap*L*A := money
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left zlo (by positivity)) aPos.le
  change scale*hits ≤ cap*l
  exact_mod_cast (le_of_mul_le_mul_right result aPos)

end PrimeFactors.CharacterWindowRate
