import PrimeFactors.WeightedMultiplierPoints
import PrimeFactors.WeightedMultiplierPopulation

/-! Count products in the same two rows when the product of the remainders
is a fixed multiple of a square. A third row can determine a short finite
list of these multiples. -/

namespace PrimeFactors.WeightedTripleFiber
open Finset WeightedMultiplierPopulation

/-- The data for a fixed square class. The height counts bits of the first
Pell coordinate. All labels, weights and the square class are fixed across
the set of possible products. -/
def InClass (r s A B m H n : ℕ) : Prop :=
  ∃ d e u : ℕ, A^2=d+4*r*n ∧ B^2=e+4*s*n ∧ d*e=m*u^2 ∧ s*d+r*e<2^H

theorem bound {r s A B m H : ℕ} (rp : 0<r) (sp : 0<s)
    (cp : 0<difference (r,s) A B) (S : Finset ℕ)
    (inside : ∀ n∈S, InClass r s A B m H n) :
    S.card ≤ 2*H*((difference (r,s) A B)^2).divisors.card := by
  classical
  obtain ⟨t,f,rad,free⟩ := Nat.sq_mul_squarefree (r*s*m)
  choose d e u first second square height using
    (fun n : S => inside n n.property)
  let point (n : S) := (s*d n+r*e n,2*f*u n)
  have recover (n : S) : (point n).1+(8*r*s)*n.val=s*A^2+r*B^2 := by
    dsimp [point]
    rw [first n,second n]
    ring
  have inj : Function.Injective point := by
    intro n n' same
    have eq := congrArg Prod.fst same
    have prod : (8*r*s)*n.val=(8*r*s)*n'.val := by
      have h := recover n
      have h' := recover n'
      omega
    exact Subtype.ext (Nat.eq_of_mul_eq_mul_left (by positivity) prod)
  have coord (n : S) : (point n).1^2=t*(point n).2^2+(difference (r,s) A B)^2 := by
    have ha : (A:ℤ)^2=d n+4*(r:ℤ)*n.val := by exact_mod_cast first n
    have hb : (B:ℤ)^2=e n+4*(s:ℤ)*n.val := by exact_mod_cast second n
    have hd : (d n:ℤ)*e n=m*(u n:ℤ)^2 := by exact_mod_cast square n
    have hr : (f:ℤ)^2*t=(r:ℤ)*s*m := by exact_mod_cast rad
    have diff : (s:ℤ)*A^2-(r:ℤ)*B^2=s*(d n:ℤ)-r*(e n:ℤ) := by
      rw [ha,hb]
      ring
    change (s*d n+r*e n)^2=t*(2*f*u n)^2+(difference (r,s) A B)^2
    apply (Nat.cast_inj (R:=ℤ)).mp
    unfold difference
    push_cast
    rw [sq_abs,diff]
    linear_combination 4*(r:ℤ)*s*hd-4*(u n:ℤ)^2*hr
  let P := univ.image point
  have count : P.card=S.card := by
    simpa [P] using (Finset.card_image_of_injective univ inj)
  rw [←count]
  apply WeightedMultiplierPoints.points cp free
  intro z hz
  obtain ⟨n,_,rfl⟩ := mem_image.mp hz
  have eq := coord n
  have pos : 0<(point n).1 := by
    apply Nat.pos_of_ne_zero
    intro zero
    rw [zero] at eq
    have strict := pow_pos cp 2
    omega
  exact ⟨pos,eq,height n⟩

/-- Sum the count over the divisors of one public integer. This does not
require either its factorization or any independence between candidate rows. -/
theorem divisor_union {r s A B M H : ℕ} (rp : 0<r) (sp : 0<s) (mp : 0<M)
    (cp : 0<difference (r,s) A B) (S : Finset ℕ)
    (inside : ∀ n∈S, ∃ m : ℕ, m∣M ∧ InClass r s A B m H n) :
    S.card ≤ M.divisors.card*(2*H*((difference (r,s) A B)^2).divisors.card) := by
  classical
  let cell (m : ℕ) := S.filter (InClass r s A B m H)
  have cover : S ⊆ M.divisors.biUnion cell := by
    intro n hn
    obtain ⟨m,div,hit⟩ := inside n hn
    exact mem_biUnion.mpr ⟨m,Nat.mem_divisors.mpr ⟨div,mp.ne'⟩,mem_filter.mpr ⟨hn,hit⟩⟩
  exact (card_le_card cover).trans (card_biUnion_le_card_mul _ _ _ (fun m _ =>
    bound rp sp cp (cell m) (fun _ h => (mem_filter.mp h).2)))

end PrimeFactors.WeightedTripleFiber
