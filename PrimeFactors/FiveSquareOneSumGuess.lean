import PrimeFactors.FiveSquarePolicy
import PrimeFactors.FiveSquareSignPopulation

/-! Success in predicting the sum residue of two independent uniform units
after observing their product at the fixed modulus 5²·7²·11²·13²·17². -/

namespace PrimeFactors.FiveSquareOneSumGuess

open Finset PrimeSquareSumWeights FiveSquareSignRanks
open FiveSquareGuessRanks (primes)
open FiveSquarePrimeSupply (m)
open FiveSquarePolicy (U)
open private PrimeFactors.FiveSquarePolicy.fiber PrimeFactors.FiveSquarePolicy.change_product
  from PrimeFactors.FiveSquarePolicy
open scoped Classical

set_option maxRecDepth 4096
attribute [local irreducible] CoprimeGuessTables.modulus Fintype.card

/-- Peak ordered-pair multiplicity for a product with this quadratic
sign pattern. Each square coordinate contributes p and every other
coordinate contributes two. -/
noncomputable def peak (b : Pattern) : ℕ := ∏ i, if b i then primes i else 2

private theorem table (b : Pattern) :
    rows b (fun w => if peak b<w then 1 else 0)=0 ∧
      0<rows b (fun w => if w=peak b then 1 else 0) :=
  (by decide +kernel : ∀ b : Pattern, rows b (fun w => if peak b<w then 1 else 0)=0 ∧
    0<rows b (fun w => if w=peak b then 1 else 0)) b

private theorem from_histogram {α : Type*} [Fintype α] (w : α→ℕ) (b : Pattern)
    (law : ∀ f : ℕ→ℕ,(∑ a,f (w a))=rows b f) : IsGreatest (Set.range w) (peak b) := by
  have top := law (fun k => if peak b<k then 1 else 0)
  have hit := law (fun k => if k=peak b then 1 else 0)
  rw [(table b).1] at top
  have some := (table b).2.trans_eq hit.symm
  constructor
  · by_contra absent
    have noHit (a : α) : w a≠peak b := fun eq => absent ⟨a,eq⟩
    simp only [noHit,if_false,sum_const_zero,lt_self_iff_false] at some
  · rintro _ ⟨a,rfl⟩
    by_contra bad
    have above := Nat.lt_of_not_ge bad
    have pos := single_le_sum (s:=univ) (f:=fun x => if peak b<w x then 1 else 0)
      (fun x _ => Nat.zero_le _) (mem_univ a)
    simp only [above,if_true,top] at pos
    omega

private theorem label_maximum (u : U) :
    IsGreatest (Set.range (fun s : Labels u.val.val => weight u.val.val s.val)) (peak (sign u.val.val)) := by
  have unit : IsUnit (u.val.val:ZMod m) := by rw [ZMod.natCast_zmod_val]; exact u.isUnit
  exact from_histogram _ _ (histogram _ (local_units unit))

theorem weight_le (u : U) (s : ZMod m) : weight u.val.val s≤peak (sign u.val.val) := by
  by_cases h : AdmissibleSum (u.val.val:ZMod m) s
  · exact (label_maximum u).2 ⟨⟨s,h⟩,rfl⟩
  · have z := Nat.eq_zero_of_not_pos (fun pos => h ((CoprimeGuessTables.positive_iff s).mp pos))
    rw [z]
    exact Nat.zero_le _

theorem attains (u : U) : ∃ s : ZMod m,weight u.val.val s=peak (sign u.val.val) := by
  obtain ⟨s,eq⟩ := (label_maximum u).1
  exact ⟨s.val,eq⟩

theorem peak_le (b : Pattern) : peak b≤85085 :=
  (by decide +kernel : ∀ p : Pattern,peak p≤85085) b

/-- Conditional success probability for a specified product and guess. -/
noncomputable def conditional (u : U) (s : ZMod m) : ℚ := (weight u.val.val s:ℚ)/3920716800

theorem conditional_maximum (u : U) :
    IsGreatest (Set.range (conditional u)) ((peak (sign u.val.val):ℚ)/3920716800) := by
  obtain ⟨s,eq⟩ := attains u
  exact ⟨⟨s,by rw [conditional,eq]⟩,fun y ⟨r,hy⟩ => hy ▸
    div_le_div_of_nonneg_right (by exact_mod_cast weight_le u r) (by norm_num)⟩

theorem ceiling (u : U) (s : ZMod m) : conditional u s≤1/46080 := by
  have cap := (weight_le u s).trans (peak_le _)
  unfold conditional
  exact (div_le_div_of_nonneg_right (by exact_mod_cast cap : (weight u.val.val s:ℚ)≤85085)
    (by norm_num : (0:ℚ)≤3920716800)).trans (by norm_num)

theorem ceiling_attained : ∃ (u : U) (s : ZMod m),conditional u s=1/46080 := by
  let sq : Pattern := fun _ => true
  have h := FiveSquareSignPopulation.pattern_count sq
  obtain ⟨u,hu⟩ := card_pos.mp (h ▸ (by decide : 0<122522400))
  obtain ⟨s,eq⟩ := attains u
  have signs : sign u.val.val=sq := (mem_filter.mp hu).2
  rw [signs,show peak sq=85085 by decide +kernel] at eq
  exact ⟨u,s,by rw [conditional,eq]; norm_num⟩

abbrev Policy := U→ZMod m
private noncomputable def hit (g : Policy) (a b : U) : ℕ :=
  if (a:ZMod m)+(b:ZMod m)=g (a*b) then 1 else 0

/-- Hits are counted on all ordered pairs of units. The product selects
a single sum-residue guess before the sum is observed. -/
noncomputable def success (g : Policy) : ℚ :=
  ((∑ v : U×U,hit g v.1 v.2:ℕ):ℚ)/Fintype.card (U×U)

private theorem indicator_mass {α : Type*} [Fintype α] (p : α→Prop) [DecidablePred p] :
    (∑ a : α,if p a then 1 else 0)=Nat.card {a // p a} := by
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype,sum_ite]
  simp

private theorem row (g : Policy) (u : U) :
    (∑ a : U,hit g a (a⁻¹*u))=weight u.val.val (g u) := by
  let e := PrimeFactors.FiveSquarePolicy.fiber u
  have entry (a : U) : hit g a (a⁻¹*u)=(if sumOf (e a)=g u then 1 else 0) := by
    rw [hit,mul_inv_cancel_left]
    rfl
  calc
    _ = ∑ a : U, (if sumOf (e a)=g u then 1 else 0) := sum_congr rfl (fun a _ => entry a)
    _ = ∑ v : Pairs u.val.val m, (if sumOf v=g u then 1 else 0) :=
      e.sum_comp (fun v : Pairs u.val.val m => if sumOf v=g u then (1:ℕ) else 0)
    _ = _ := indicator_mass (fun v : Pairs u.val.val m => sumOf v=g u)

/-- Exact conditional hit count over the first unit; its partner is
uniquely determined by the given product. -/
theorem conditional_count (u : U) (s : ZMod m) :
    (∑ a : U,if (a:ZMod m)+((a⁻¹*u:U):ZMod m)=s then 1 else 0)=weight u.val.val s :=
  row (fun _ => s) u

theorem success_eq (g : Policy) :
    success g=(∑ u : U,conditional u (g u))/Fintype.card U := by
  unfold success
  rw [PrimeFactors.FiveSquarePolicy.change_product (hit g)]
  simp only [row,conditional,←sum_div,Fintype.card_prod,FiveSquarePolicy.unit_count.1,Nat.cast_sum,
    Nat.cast_mul,Nat.cast_ofNat]
  ring

private theorem pattern_mean :
    (∑ u : U,(peak (sign u.val.val):ℚ)/3920716800)/Fintype.card U=
      233415/(32*3920716800) := by
  refine (FiveSquareSignPopulation.mean_by_pattern (fun b => (peak b:ℚ)/3920716800)).trans ?_
  decide +kernel

/-- One product-dependent policy attains all of the conditional maxima
simultaneously, and attains the pooled optimum on actual ordered unit pairs. -/
theorem pooled : IsGreatest (Set.range success) (233415/(32*3920716800)) := by
  choose g eq using attains
  constructor
  · refine ⟨g,?_⟩
    rw [success_eq]
    simpa only [conditional,eq] using pattern_mean
  · rintro _ ⟨g,rfl⟩
    rw [success_eq,←pattern_mean]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact sum_le_sum (fun u _ => (conditional_maximum u).2 ⟨g u,rfl⟩)

end PrimeFactors.FiveSquareOneSumGuess
