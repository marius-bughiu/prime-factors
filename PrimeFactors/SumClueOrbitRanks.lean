import PrimeFactors.FactorOrbitGuessRanks
import PrimeFactors.SquareFiberMoments

/-! Guessing the unordered pair of unit residues after both its product and
its correct sum are supplied. Ranks count the successful orbit guess. -/
namespace PrimeFactors.SumClueOrbitRanks

open Finset FactorOrbitGuessRanks PrimeSquareSumWeights
open FiveSquareGuessRanks (score)
open scoped Classical
open private PrimeFactors.FactorOrbitGuessRanks.integer_optimum PrimeFactors.FactorOrbitGuessRanks.sizes
  PrimeFactors.FactorOrbitGuessRanks.singleton_iff from PrimeFactors.FactorOrbitGuessRanks
open private PrimeFactors.FiveSquareGuessRanks.overlap from PrimeFactors.FiveSquareGuessRanks

-- Fix the finite instance at the abstract group before specializing to ring units.
private noncomputable def labelFintype {G : Type*} [CommGroup G] [Fintype G] (u : G) :
    Fintype (Label u) := inferInstance
attribute [local instance 2000] labelFintype

variable {m : ℕ} [NeZero m]
private abbrev U (m : ℕ) := (ZMod m)ˣ
private noncomputable def rep {u : U m} (o : Label u) : U m := o.property.choose
omit [NeZero m] in
private theorem rep_label {u : U m} (o : Label u) : label u (rep o)=o :=
  Subtype.ext o.property.choose_spec

/-- Both orders of a complementary pair give the same ring sum. -/
noncomputable def clue (u : U m) (o : Label u) : ZMod m :=
  ((rep o : U m) : ZMod m)+((u/rep o : U m) : ZMod m)

omit [NeZero m] in
theorem clue_label (u a : U m) : clue u (label u a)=(a:ZMod m)+((u/a : U m):ZMod m) := by
  unfold clue
  rcases (hit_iff _ _ _).mp (rep_label (label u a)) with h|h
  · rw [h]
  · rw [h,div_div_self',add_comm]

abbrev Row (u : U m) (s : ZMod m) := {o : Label u // clue u o=s}
abbrev Policy (u : U m) := (s : ZMod m) → Fin (Fintype.card (Row u s)) ≃ Row u s
private noncomputable def rankOf {u : U m} (P : Policy u) (o : Label u) :=
  ((P (clue u o)).symm ⟨o,rfl⟩).val+1

noncomputable def rank {u : U m} (P : Policy u) (a : U m) := rankOf P (label u a)
noncomputable def mean {u : U m} (P : Policy u) : ℚ := ((∑ a,rank P a : ℕ):ℚ)/Fintype.card (U m)

theorem rank_partner {u : U m} (P : Policy u) (a : U m) : rank P (u/a)=rank P a := by
  unfold rank
  rw [(hit_iff u (u/a) a).mpr (Or.inr rfl)]

theorem rank_bound {u : U m} (P : Policy u) (a : U m) : rank P a≤Fintype.card (U m) := by
  let o := label u a
  have one := ((P (clue u o)).symm ⟨o,rfl⟩).isLt
  exact (Nat.succ_le_of_lt one).trans ((Fintype.card_subtype_le _).trans
    (Fintype.card_le_of_surjective (label u) (fun t => ⟨_,rep_label t⟩)))

private def w {u : U m} {s : ZMod m} (l : Row u s) := l.val.val.card
private noncomputable def singles (u : U m) (s : ZMod m) := ∑ x : Row u s, if w x=1 then 1 else 0

private theorem mass (u : U m) (s : ZMod m) : (∑ x : Row u s,w x)=weight u.val.val s := by
  let f (a : U m) : Pairs u.val.val m := ⟨(a,(u/a:U m)),by
    rw [ZMod.natCast_zmod_val]; exact congrArg Units.val (by simp [div_eq_mul_inv,mul_left_comm] : a*(u/a)=u)⟩
  have bij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card _).mpr ⟨
    fun x y h => Units.ext (congrArg (fun z : Pairs u.val.val m => z.val.1) h),by
      rw [ZMod.card_units_eq_totient,←Nat.card_eq_fintype_card,total (by simp)]⟩
  let e := Equiv.ofBijective f bij
  have pairs := e.sum_comp (fun z : Pairs u.val.val m => if sumOf z=s then (1 : ℕ) else 0)
  have eq := by_orbit u (fun o => if clue u o=s then 1 else 0)
  simp_rw [clue_label] at eq
  have sub := (sum_subtype (F:=inferInstanceAs (Fintype (Row u s))) (p:=fun o : Label u => clue u o=s) (univ.filter (fun o : Label u => clue u o=s)) (by simp) (fun o => o.val.card))
  rw [sum_filter] at sub
  rw [show (∑ x : Row u s,w x)=(∑ o : Label u, if clue u o=s then o.val.card else 0) from sub.symm]
  simp only [mul_ite,mul_one,mul_zero] at eq
  rw [←eq]
  change (∑ a : U m, if sumOf (e a)=s then 1 else 0)=_
  rw [pairs,weight,Nat.card_eq_fintype_card,Fintype.card_subtype]
  simp

private theorem row_score (u : U m) (s : ZMod m) : ∃ k : ℕ,
    IsLeast (Set.range (score (w (u:=u) (s:=s)))) k ∧
    4*k=(weight u.val.val s)^2+2*weight u.val.val s+(singles u s)^2 := by
  obtain ⟨k,least,h⟩ := PrimeFactors.FactorOrbitGuessRanks.integer_optimum (w (u:=u) (s:=s))
  refine ⟨k,least,?_⟩
  have sizes (l : Row u s) : w l=1 ∨ w l=2 := PrimeFactors.FactorOrbitGuessRanks.sizes u l.val
  have each (l : Row u s) : (if w l=1 then 1 else 0)+w l=2 := by
    rcases sizes l with h|h <;> simp [h]
  have both := sum_congr (rfl : (univ : Finset (Row u s))=univ) (fun i _ => each i)
  simp only [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,mass] at both
  have cnt : (singles u s:ℝ)+weight u.val.val s=Fintype.card (Row u s)*2 := by unfold singles; exact_mod_cast both
  have tot : (∑ l : Row u s,(w l:ℝ))=weight u.val.val s := by exact_mod_cast mass u s
  have overlap : (2:ℝ)*k=weight u.val.val s+∑ x : Row u s,∑ y : Row u s,(min (w x:ℝ) (w y:ℝ)) := by
    rw [mass] at h
    dsimp only [PrimeFactors.FiveSquareGuessRanks.overlap] at h
    exact_mod_cast h
  rw [FirstPowerGuessOverlap.one_two w sizes,tot] at overlap
  have formula : (4:ℝ)*k=(weight u.val.val s:ℝ)^2+2*weight u.val.val s+(singles u s:ℝ)^2 := by
    rw [show (Fintype.card (Row u s):ℝ)=(singles u s+weight u.val.val s)/2 by linarith] at overlap
    nlinarith only [overlap]
  exact_mod_cast formula

private theorem sum_scores {u : U m} (P : Policy u) :
    (∑ a,rank P a)=∑ s,score w (P s) := by
  unfold rank
  calc
    _ = ∑ l : Label u, l.val.card*rankOf P l := by_orbit u (rankOf P)
    _ = ∑ s,∑ l : Row u s,l.val.val.card*rankOf P l.val :=
      (Fintype.sum_fiberwise (clue u) (fun l => l.val.card*rankOf P l)).symm
    _ = _ := ?_
  apply sum_congr rfl
  intro s _
  have loc (l : Row u s) : rankOf P l.val=((P s).symm l).val+1 := by
    rcases l with ⟨l,rfl⟩; rfl
  simp_rw [loc]
  have eq := (P s).sum_comp (fun l : Row u s => l.val.val.card*(((P s).symm l).val+1))
  simpa only [Equiv.symm_apply_apply,score,w,Nat.mul_comm] using eq.symm

private theorem sum_mass (u : U m) : (∑ s : ZMod m,weight u.val.val s)=Fintype.card (U m) := by
  calc
    _ = ∑ s : ZMod m, ∑ x : Row u s, w x := sum_congr rfl (fun s _ => (mass u s).symm)
    _ = ∑ l : Label u,l.val.card := Fintype.sum_fiberwise (clue u) (fun l => l.val.card)
    _ = _ := FactorOrbitGuessRanks.mass u

private theorem sum_singles (u : U m) : (∑ s,singles u s)=SquareFiberMoments.roots u := by
  calc
    _ = ∑ l : Label u, if l.val.card=1 then 1 else 0 :=
      Fintype.sum_fiberwise (clue u) (fun l => if l.val.card=1 then (1:ℕ) else 0)
    _ = _ := by
      rw [sum_ite]
      simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,mul_one,mul_zero,add_zero]
      exact singleton_count u

private theorem one_single (u : U m) (two : IsUnit (2 : ZMod m)) (s : ZMod m) : singles u s≤1 := by
  have eq (l : Row u s) (h : w l=1) : 2*((rep l.val:U m):ZMod m)=s := by
    have single : (label u (rep l.val)).val.card=1 := by rw [rep_label]; exact h
    have fixed := (PrimeFactors.FactorOrbitGuessRanks.singleton_iff _ _).mp single
    have same : u/rep l.val=rep l.val := by
      simpa only [pow_two,mul_div_cancel_right] using congrArg (fun z : U m => z/rep l.val) fixed.symm
    simpa only [clue,same,two_mul] using l.property
  unfold singles
  rw [sum_ite]
  simp only [sum_const_zero,add_zero,sum_const,nsmul_eq_mul,Nat.cast_id,mul_one]
  apply card_le_one.mpr
  intro a ha b hb
  have ab : rep a.val=rep b.val := Units.ext (two.mul_left_cancel ((eq a (mem_filter.mp ha).2).trans
    (eq b (mem_filter.mp hb).2).symm))
  exact Subtype.ext (by rw [←rep_label a.val,←rep_label b.val,ab])

private theorem normalize {a b c t : ℚ} (ht : 0<t) (h : 4*a=b+2*t+c) :
    a/t=1/2+(b+c)/(4*t) := by
  field_simp [ht.ne']
  nlinarith only [h, congrArg (fun z => z*t) h]

/-- A separate inclusive order for each supplied sum attains the exact optimum.
The population is all ordered unit pairs with the stated product. -/
theorem mean_optimum (u : U m) (two : IsUnit (2 : ZMod m)) :
    IsLeast (Set.range (mean (u:=u)))
      (1/2+(((∑ s : ZMod m, (weight u.val.val s)^2:ℕ):ℚ)+SquareFiberMoments.roots u)/
        (4*Fintype.card (U m))) := by
  choose k least eq using row_score u
  have squares (s : ZMod m) : singles u s ^ 2=singles u s := by
    rcases (show singles u s=0 ∨ singles u s=1 by have := one_single u two s; omega) with h|h <;> simp [h]
  have all := sum_congr (rfl : (univ : Finset (ZMod m))=univ) (fun s _ => eq s)
  simp only [←mul_sum,sum_add_distrib,squares,sum_mass,sum_singles] at all
  have size : (0:ℚ)<Fintype.card (U m) := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card (U m))
  have rat : (4:ℚ)*(∑ s,k s:ℕ)=((∑ s : ZMod m,(weight u.val.val s)^2:ℕ):ℚ)+
      2*Fintype.card (U m)+SquareFiberMoments.roots u := by exact_mod_cast all
  have val : ((∑ s,k s:ℕ):ℚ)/Fintype.card (U m)=
      1/2+(((∑ s : ZMod m,(weight u.val.val s)^2:ℕ):ℚ)+SquareFiberMoments.roots u)/(4*Fintype.card (U m)) := by
    exact normalize size rat
  rw [←val]
  choose P attained using fun s => (least s).1
  constructor
  · refine ⟨P,?_⟩
    simp only [mean,sum_scores,attained]
  · rintro _ ⟨P,rfl⟩
    apply div_le_div_of_nonneg_right _ size.le
    rw [sum_scores]
    exact_mod_cast sum_le_sum (s:=univ) (fun s _ => (least s).2 ⟨P s,rfl⟩)

end PrimeFactors.SumClueOrbitRanks
