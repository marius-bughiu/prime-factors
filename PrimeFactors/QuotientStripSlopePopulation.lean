import PrimeFactors.CircleMarkPrimitiveDensity

/-!
# Many primitive directions in a short range of ratios

The integer change of coordinates below has determinant one. It puts an
entire positive square of primitive points between slopes 5/4 and 4/3.
The density estimate already proved for the primitive grid therefore
supplies many different directions in this range.
-/

namespace PrimeFactors.QuotientStripSlopePopulation

open Finset CircleMarkRationalFrequency

def direction (z : ℕ × ℕ) : ℕ × ℕ := (4*z.1+5*z.2, 3*z.1+4*z.2)

theorem inverse_coordinates (z : ℕ × ℕ) :
    4*(direction z).1-5*(direction z).2=z.1 ∧
    4*(direction z).2-3*(direction z).1=z.2 := by
  simp only [direction]
  omega

theorem direction_injective : Function.Injective direction := by
  intro x y h
  have hx := inverse_coordinates x
  rw [h] at hx
  have hy := inverse_coordinates y
  exact Prod.ext (hx.1.symm.trans hy.1) (hx.2.symm.trans hy.2)

theorem preserves_coprime {z : ℕ × ℕ} (cop : z.1.Coprime z.2) :
    (direction z).1.Coprime (direction z).2 := by
  let g := (direction z).1.gcd (direction z).2
  have a : g ∣ (direction z).1 := Nat.gcd_dvd_left _ _
  have b : g ∣ (direction z).2 := Nat.gcd_dvd_right _ _
  have back := inverse_coordinates z
  have i : g ∣ z.1 := back.1 ▸ Nat.dvd_sub (dvd_mul_of_dvd_right a 4) (dvd_mul_of_dvd_right b 5)
  have j : g ∣ z.2 := back.2 ▸ Nat.dvd_sub (dvd_mul_of_dvd_right b 4) (dvd_mul_of_dvd_right a 3)
  exact Nat.dvd_one.mp (cop ▸ Nat.dvd_gcd i j : g ∣ 1)

noncomputable def directions (B : ℕ) := (primitive B B).image direction

theorem size {B : ℕ} (big : 2^20≤B) : 601*(B*B)<1000*(directions B).card := by
  simpa only [directions, card_image_of_injective _ direction_injective] using
    CircleMarkPrimitiveDensity.large_rectangle big big

theorem properties {B : ℕ} {z : ℕ × ℕ} (mem : z ∈ directions B) :
    0<z.1 ∧ 7≤z.2 ∧ z.1≤9*B ∧ z.2≤7*B ∧ 5*z.2<4*z.1 ∧ 3*z.1≤4*z.2 ∧
    z.1.Coprime z.2 := by
  obtain ⟨w,hw,rfl⟩ := mem_image.mp mem
  obtain ⟨bounds,cop⟩ := mem_filter.mp hw
  have h := preserves_coprime cop
  change w ∈ Icc 1 B ×ˢ Icc 1 B at bounds
  simp only [mem_product,mem_Icc] at bounds
  simp only [direction] at h ⊢
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega,h⟩

theorem many_directions : 2^653 < (directions (2^327)).card := by
  have h := size (B:=2^327) (by decide +kernel)
  omega

/-- If two different blocks belong to each direction and each block has only
one owner, the counted population injects into the set of retained blocks. -/
theorem two_blocks {α : Type*} [DecidableEq α] (S : Finset (ℕ×ℕ)) (kept : Finset α)
    (owner : α → ℕ×ℕ) (hit : ∀ z ∈ S, ∃ a ∈ kept, ∃ b ∈ kept,
      a≠b ∧ owner a=z ∧ owner b=z) : 2*S.card ≤ kept.card := by
  classical
  have witnesses (z : ℕ×ℕ) (hz : z∈S) : 2 ≤ (kept.filter (fun a => owner a=z)).card := by
    obtain ⟨a,ha,b,hb,ab,h₁,h₂⟩ := hit z hz
    have sub : ({a,b}:Finset α) ⊆ kept.filter (fun x => owner x=z) := by
      intro x hx
      rcases (show x=a ∨ x=b by simpa only [mem_insert,mem_singleton] using hx) with rfl|rfl
      exacts [mem_filter.mpr ⟨ha,h₁⟩,mem_filter.mpr ⟨hb,h₂⟩]
    simpa [ab] using card_le_card sub
  calc
    _ = ∑ _z ∈ S, 2 := by simp [mul_comm]
    _ ≤ ∑ z ∈ S, (kept.filter (fun a => owner a=z)).card := sum_le_sum witnesses
    _ ≤ kept.card := by
      classical
      have disjoint : (S : Set (ℕ×ℕ)).PairwiseDisjoint (fun z => kept.filter (fun a => owner a=z)) := by
        intro a _ b _ ne
        exact disjoint_left.mpr fun _ ha hb => ne ((mem_filter.mp ha).2.symm.trans (mem_filter.mp hb).2)
      rw [← card_biUnion disjoint]
      exact card_le_card (by
        intro a ha
        obtain ⟨_,_,h⟩ := mem_biUnion.mp ha
        exact (mem_filter.mp h).1)

end PrimeFactors.QuotientStripSlopePopulation
