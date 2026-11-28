import PrimeFactors.ConeUnitTarget
import PrimeFactors.RandomSignMenu
import PrimeFactors.ProductResidueRefinement

/-! The distribution of ternary modular representation counts on a full
Jacobi-sign class of unit targets. All averages are uniform on that class. -/

namespace PrimeFactors.ConeJacobiClassMean

open Finset ThreeSquareCone RandomSignMenu
open scoped Classical
open private PrimeFactors.RandomSignMenu.surjective from PrimeFactors.RandomSignMenu

/-- Unit targets t with the given public Jacobi sign of −t. -/
noncomputable def targets (n : ℕ) [NeZero n] (j : ℤˣ) : Finset (ZMod n)ˣ :=
  univ.filter fun t => jacobiSym (-(t.val.val : ℤ)) n = (j : ℤ)

/-- Ordered ternary representations at the sampled residue. -/
noncomputable def count (n : ℕ) [NeZero n] (t : (ZMod n)ˣ) : ℤ :=
  (points (ZMod n) t.val).card

def center (n : ℕ) (j : ℤˣ) : ℤ := (n : ℤ)*(n+(j:ℤ))

/-- For p<q this is positive. The sign chooses the prime sum or gap. -/
def spread (p q : ℕ) (j : ℤˣ) : ℤ := (p*q : ℤ)*(q+(j:ℤ)*p)

private theorem both_signs (f : ℤˣ → ℤ) : (∑ x, f x) = f 1 + f (-1) := by
  have keys : (univ : Finset ℤˣ) = {1,-1} := by
    ext s
    simpa only [mem_univ, mem_insert, mem_singleton, true_iff] using Int.units_eq_one_or s
  rw [keys]
  simp [show (1 : ℤˣ) ≠ -1 by decide]

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime]

private def reading (p q : ℕ) (z : Signs) : ℤ :=
  (p*q : ℤ)*(p+(z.1:ℤ))*(q+(z.2:ℤ))

private theorem reading_eq (cop : p.Coprime q) (ne : p≠q) (op : p≠2) (oq : q≠2)
    (t : (ZMod (p*q))ˣ) : count (p*q) t = reading p q (signs cop (-t)) := by
  let a : ℤ := t.val.val
  have rep : (a : ZMod (p*q)) = t.val := by simp [a]
  have rep' : ((-a : ℤ) : ZMod (p*q)) = (-t).val := by simp [rep]
  have crt := congrArg (ZMod.chineseRemainder cop) rep'
  rw [map_intCast] at crt
  have cp := congrArg (quadraticChar (ZMod p)) (congrArg Prod.fst crt)
  have cq := congrArg (quadraticChar (ZMod q)) (congrArg Prod.snd crt)
  unfold count
  rw [←rep,ConeUnitTarget.character_count ne op oq]
  exact congrArg₂ (fun x y : ℤ => (p*q : ℤ)*(p+x)*(q+y)) cp cq

omit [Fact p.Prime] [Fact q.Prime] in
private theorem four_terms (j : ℤˣ) (f : ℤ → ℤ) :
    (∑ z : Signs, if z.1*z.2=j then f (reading p q z) else 0) =
    f (center (p*q) j+spread p q j)+f (center (p*q) j-spread p q j) := by
  rw [Fintype.sum_prod_type, both_signs, both_signs, both_signs]
  rcases Int.units_eq_one_or j with rfl|rfl <;>
    norm_num [reading,center,spread,show (1:ℤˣ)≠ -1 by decide,show (-1:ℤˣ)≠1 by decide] <;>
    congr 1 <;> congr 1 <;> ring

/-- Each of the two possible counts has the same multiplicity. Applying any
integer-valued statistic to the count preserves the exact two-point sum. -/
theorem two_point_law (ne : p≠q) (op : p≠2) (oq : q≠2) (j : ℤˣ) (f : ℤ → ℤ) :
    (∑ t ∈ targets (p*q) j, f (count (p*q) t)) =
      (((p-1)*(q-1)/4 : ℕ) : ℤ) *
        (f (center (p*q) j+spread p q j)+f (center (p*q) j-spread p q j)) := by
  let cop := (Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : q.Prime)).mpr ne
  let π := signs cop
  have onto := PrimeFactors.RandomSignMenu.surjective cop op oq
  let g (z : Signs) := if z.1*z.2=j then f (reading p q z) else 0
  have reindex : (∑ t ∈ targets (p*q) j, f (count (p*q) t)) =
      ∑ u : (ZMod (p*q))ˣ, g (π u) := by
    unfold targets
    rw [sum_filter]
    apply Fintype.sum_equiv (Equiv.neg _) _ _
    intro t
    have rep : ((-(t.val.val : ℤ) : ℤ) : ZMod (p*q)) = (-t).val := by simp
    rw [jacobi_signs cop (-t) _ rep, reading_eq cop ne op oq]
    change (if ((π (-t)).1*(π (-t)).2 : ℤˣ).val = (j : ℤ)
      then f (reading p q (π (-t))) else 0) = _
    simp [g,Units.ext_iff]
  have all := ProductResidueRefinement.sum_pullback π onto (fun _ => (1:ℕ))
  simp only [sum_const,card_univ,Fintype.card_prod,Fintype.card_units_int,
    nsmul_eq_mul,Nat.cast_id,mul_one,ZMod.card_units_eq_totient,Nat.totient_mul cop,
    Nat.totient_prime (Fact.out : p.Prime),Nat.totient_prime (Fact.out : q.Prime)] at all
  rw [reindex, ProductResidueRefinement.sum_pullback π onto, nsmul_eq_mul]
  congr 1
  · apply congrArg (Nat.cast : ℕ → ℤ)
    rw [all,Nat.mul_div_cancel _ (by decide : 0 < 4)]
  · exact four_terms j f

/-- The exact frequency of any proposed count, including those outside the
two supported values. -/
theorem frequency (ne : p≠q) (op : p≠2) (oq : q≠2) (j : ℤˣ) (v : ℤ) :
    ((targets (p*q) j).filter (fun t => count (p*q) t = v)).card =
      (p-1)*(q-1)/4 * ((if center (p*q) j+spread p q j = v then 1 else 0) +
                        (if center (p*q) j-spread p q j = v then 1 else 0)) := by
  have h := two_point_law ne op oq j (fun x => if x=v then 1 else 0)
  rw [sum_boole] at h
  split_ifs at h ⊢ <;> exact_mod_cast h

/-- Conditional average over the actual unit targets in a single class. -/
noncomputable def average (n : ℕ) [NeZero n] (j : ℤˣ) (f : ℤ → ℤ) : ℚ :=
  ((∑ t ∈ targets n j, f (count n t) : ℤ) : ℚ)/(targets n j).card

theorem conditional_law (ne : p≠q) (op : p≠2) (oq : q≠2) (j : ℤˣ) (f : ℤ → ℤ) :
    average (p*q) j f =
      ((f (center (p*q) j+spread p q j)+f (center (p*q) j-spread p q j) : ℤ) : ℚ)/2 := by
  have p2 := (Fact.out : p.Prime).two_le
  have q2 := (Fact.out : q.Prime).two_le
  have four : 4 ≤ (p-1)*(q-1) := Nat.mul_le_mul (by omega : 2≤p-1) (by omega : 2≤q-1)
  have pos : 0 < (p-1)*(q-1)/4 := by omega
  have pop := two_point_law ne op oq j (fun _ => 1)
  simp only [sum_const, nsmul_eq_mul, mul_one] at pop
  have popQ : ((targets (p*q) j).card : ℚ) = ((((p-1)*(q-1)/4 : ℕ) : ℚ)*2) := by
    exact_mod_cast pop
  rw [average, two_point_law ne op oq, popQ, Int.cast_mul]
  have nz : ((((p-1)*(q-1)/4 : ℕ) : ℚ)) ≠ 0 := by positivity
  rw [Int.cast_natCast, mul_div_mul_left _ _ nz]

/-- The conditional mean depends only on the modulus and public sign. -/
theorem mean (ne : p≠q) (op : p≠2) (oq : q≠2) (j : ℤˣ) :
    average (p*q) j id = (center (p*q) j : ℚ) := by
  rw [conditional_law ne op oq]
  simp only [id_eq,Int.cast_add,Int.cast_sub]
  ring

/-- The conditional variance is N² times the squared prime sum for positive
Jacobi sign and N² times the squared prime difference for negative sign. -/
theorem variance (ne : p≠q) (op : p≠2) (oq : q≠2) (j : ℤˣ) :
    average (p*q) j (fun v => (v-center (p*q) j)^2) = (spread p q j : ℚ)^2 := by
  rw [conditional_law ne op oq]
  push_cast
  ring

/-- At modulus 15 the eight units split into two Jacobi classes. Each of
the four displayed values occurs at two targets in the corresponding class. -/
theorem control_15 :
    ((targets 15 1).filter (fun t => count 15 t=360)).card=2 ∧
    ((targets 15 1).filter (fun t => count 15 t=120)).card=2 ∧
    ((targets 15 (-1)).filter (fun t => count 15 t=240)).card=2 ∧
    ((targets 15 (-1)).filter (fun t => count 15 t=180)).card=2 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h := frequency (p:=3) (q:=5) (by decide) (by decide) (by decide)
  exact ⟨by simpa [center,spread] using h 1 360,
         by simpa [center,spread] using h 1 120,
         by simpa [center,spread] using h (-1) 240,
         by simpa [center,spread] using h (-1) 180⟩

end PrimeFactors.ConeJacobiClassMean
