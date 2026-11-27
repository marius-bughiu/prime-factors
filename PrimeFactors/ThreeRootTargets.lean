import PrimeFactors.RootableSignSpan
import PrimeFactors.CharacterDivisorColumn
import Mathlib.Tactic.NormNum.LegendreSymbol

/-! Seven products of three generators suffice to choose three targets from
the public Jacobi signs. One of the chosen targets has a square root at both
unknown primes. -/
namespace PrimeFactors.ThreeRootTargets

open RootableSignSpan

private def masks : List (Mask 3) :=
  [![1,0,0], ![0,1,0], ![1,1,0], ![0,0,1], ![1,0,1], ![0,1,1], ![1,1,1]]

private def choose (f : Mask 3 → Bit) := (masks.filter fun v => f v == 0).take 3

private def pairing (a v : Mask 3) : Bit := a 0*v 0 + a 1*v 1 + a 2*v 2

private theorem finite_cover : ∀ a b : Mask 3,
    let m := choose (fun v => pairing a v + pairing b v)
    m.length = 3 ∧ ∃ v ∈ m, pairing a v = 0 ∧ pairing b v = 0 := by decide +kernel

private theorem pairing_eq (a v : Mask 3) : row a v = pairing a v := by
  rw [row_apply, Fin.sum_univ_three, pairing]

/-- Only the three Jacobi signs of the input are used when choosing the targets. -/
noncomputable def menu (N : ℕ) (g : Fin 3 → ℤ) : List ℤ :=
  (choose (publicRow N g)).map (word g)

theorem cover {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (g : Fin 3 → ℤ) (gp : ∀ i, (g i : ZMod p) ≠ 0) (gq : ∀ i, (g i : ZMod q) ≠ 0) :
    (menu (p*q) g).length = 3 ∧ ∃ d ∈ menu (p*q) g, IsSquare (d : ZMod (p*q)) := by
  let a := fun i => bit (legendreSym p (g i))
  let b := fun i => bit (legendreSym q (g i))
  have pub : (publicRow (p*q) g : Mask 3 → Bit) = fun v => pairing a v + pairing b v := by
    funext v
    rw [public_eq_add g gp gq, LinearMap.add_apply]
    exact congrArg₂ (·+·) (pairing_eq a v) (pairing_eq b v)
  obtain ⟨len,v,mem,left,right⟩ := finite_cover a b
  refine ⟨by simpa only [menu, List.length_map, pub] using len, word g v, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨v, by rwa [pub],rfl⟩
  · apply (rootable_iff cop g gp gq v).mpr
    exact ⟨(pairing_eq a v).trans left,(pairing_eq b v).trans right⟩

def signed : Fin 3 → ℤ := ![-1,2,3]
def positive : Fin 3 → ℤ := ![2,3,5]

private theorem sublist (N : ℕ) (g : Fin 3 → ℤ) :
    (menu N g).Sublist (masks.map (word g)) :=
  ((List.take_sublist ..).trans (List.filter_sublist ..)).map _

theorem signed_values (N : ℕ) : (menu N signed).Sublist [-1,2,-2,3,-3,6,-6] := by
  have e : masks.map (word signed) = [-1,2,-2,3,-3,6,-6] := by decide +kernel
  simpa only [← e] using sublist N signed

theorem positive_values (N : ℕ) : (menu N positive).Sublist [2,3,6,5,10,15,30] := by
  have e : masks.map (word positive) = [2,3,6,5,10,15,30] := by decide +kernel
  simpa only [← e] using sublist N positive

/-- For any two nonzero masks one local sign row can reject both. This holds
even after the total sign row has been fixed, since the other row is its sum
with this local row. -/
theorem two_can_miss : ∀ v w : Mask 3, v ≠ 0 → w ≠ 0 →
    ∃ x : Mask 3, row x v = 1 ∧ row x w = 1 := by
  simp only [pairing_eq]
  decide +kernel

/-- If a candidate is a nonsquare at an odd divisor of N, it has no root at N.
The small congruent representative makes the sign check inexpensive. -/
theorem reject {N p a : ℕ} (dv : p ∣ N) (op : Odd p) (oa : Odd a) {d : ℤ}
    (same : Nat.ModEq (4*d.natAbs) p a) (neg : jacobiSym d a = -1) :
    ¬ IsSquare (d : ZMod N) := by
  intro square
  have loc : IsSquare (d : ZMod p) := by
    simpa only [map_intCast] using IsSquare.map (ZMod.castHom dv (ZMod p)) square
  obtain ⟨z,hz⟩ := loc
  have hcast : (d : ZMod p) = ((z.valMinAbs^2 : ℤ) : ZMod p) := by
    push_cast
    simpa only [pow_two] using hz
  have pos : 0 ≤ jacobiSym d p := by
    rw [jacobiSym.mod_left' ((ZMod.intCast_eq_intCast_iff' _ _ _).mp hcast), jacobiSym.pow_left]
    exact sq_nonneg _
  rw [CharacterDivisorColumn.periodic op oa d same, neg] at pos
  omega

end PrimeFactors.ThreeRootTargets
