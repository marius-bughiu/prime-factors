import PrimeFactors.FactorOrbitGuessRanks

/-! A finite number of advice messages can select different orderings of
complementary factor residues. The selector may know the hidden pair. -/
namespace PrimeFactors.FactorOrbitAdviceFloor

open Finset FactorOrbitGuessRanks
open scoped Classical
open private PrimeFactors.JointSumGuessFloor.capped_ranks from PrimeFactors.JointSumGuessFloor
open private PrimeFactors.FactorOrbitGuessRanks.sizes from PrimeFactors.FactorOrbitGuessRanks

variable {G : Type*} [CommGroup G] [Fintype G] {n : G} {B : ℕ}

abbrev Menu (n : G) (B : ℕ) := Fin B → Order n

/-- The successful test counts as one guess. -/
noncomputable def rank (P : Menu n B) (b : Fin B) (a : G) := ((P b) (label n a)).val+1

/-- Even when the message is a function of the hidden coordinate, at most
two coordinates per message can be assigned the same rank. -/
theorem slot_bound (P : Menu n B) (choose : G → Fin B) (i : Fin (Fintype.card (Label n))) :
    (univ.filter (fun a => P (choose a) (label n a)=i)).card ≤ 2*B := by
  let orbits (b : Fin B) := ((P b).symm i).val
  have cover : univ.filter (fun a => P (choose a) (label n a)=i) ⊆ univ.biUnion orbits := by
    intro a ha
    have same := (P (choose a)).apply_eq_iff_eq_symm_apply.mp (mem_filter.mp ha).2
    have own : a∈(label n a).val := mem_insert_self ..
    exact mem_biUnion.mpr ⟨choose a,mem_univ _,by simpa only [same] using own⟩
  have small (b : Fin B) : (orbits b).card ≤ 2 := by
    change ((P b).symm i).val.card≤2
    rcases PrimeFactors.FactorOrbitGuessRanks.sizes n ((P b).symm i) with h|h <;> omega
  calc
    _ ≤ (univ.biUnion orbits).card := card_le_card cover
    _ ≤ ∑ b, (orbits b).card := card_biUnion_le
    _ ≤ ∑ _b : Fin B, 2 := sum_le_sum (fun b _ => small b)
    _ = 2*B := by simp [Nat.mul_comm]

/-- At most two first coordinates per message and rank can be covered in
an arbitrary prefix, including prefixes longer than the complete order. -/
theorem prefix_bound (P : Menu n B) (choose : G → Fin B) (t : ℕ) :
    (univ.filter (fun a => rank P (choose a) a ≤ t)).card ≤ 2*B*t := by
  let pos (a : G) := P (choose a) (label n a)
  let slots := univ.filter (fun i : Fin (Fintype.card (Label n)) => i.val<t)
  have size : slots.card ≤ t := by
    simpa only [card_range] using (card_le_card_of_injOn (s:=slots) (t:=range t) Fin.val
      (fun _ hi => mem_range.mpr (mem_filter.mp hi).2) (fun _ _ _ _ h => Fin.ext h))
  have same : univ.filter (fun a => rank P (choose a) a≤t)=univ.filter (fun a => pos a∈slots) := by
    ext a
    simp only [rank,slots,pos,mem_filter,mem_univ,true_and,Nat.succ_le_iff]
  rw [same,←sum_card_fiberwise_eq_card_filter]
  calc
    _ ≤ ∑ _i ∈ slots, 2*B := sum_le_sum (fun i _ => slot_bound P choose i)
    _ = 2*B*slots.card := by simp [Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ size

/-- The integer inequality also records the message and population sizes
without rational rounding. -/
theorem rank_mass (P : Menu n B) (choose : G → Fin B) :
    Fintype.card G*(Fintype.card G+2*B) ≤ 4*B*∑ a,rank P (choose a) a := by
  let pos (a : G) := P (choose a) (label n a)
  let w (i : Fin (Fintype.card (Label n))) := (univ.filter (fun a => pos a=i)).card
  have total : (∑ i,w i)=Fintype.card G :=
    (card_eq_sum_card_fiberwise (s:=univ) (t:=univ) (f:=pos) (fun _ _ => mem_univ _)).symm.trans card_univ
  have parts := sum_fiberwise_of_maps_to' (s:=univ) (t:=univ) (g:=pos) (fun _ _ => mem_univ _)
    (fun i => i.val+1)
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at parts
  have weights : (∑ i,(i.val+1)*w i)=∑ a,rank P (choose a) a := by
    simpa only [w,rank,pos,Nat.mul_comm] using parts
  have h := PrimeFactors.JointSumGuessFloor.capped_ranks (2*B) w (slot_bound P choose)
  rw [total,weights] at h
  simpa only [←Nat.mul_assoc] using h

private theorem normalize {T C K : ℚ} (t : 0<T) (b : 0<C) (h : T*(T+2*C) ≤ 4*C*K) :
    T/(4*C)+1/2 ≤ K/T := by
  calc
    _ = T*(T+2*C)/(4*C*T) := by field_simp; ring
    _ ≤ (4*C*K)/(4*C*T) := div_le_div_of_nonneg_right h (by positivity)
    _ = _ := by field_simp; ring

/-- Average under a uniform first coordinate, conditional on the known
product. Each message may use its own complete ordering of the orbits. -/
theorem rank_floor (hB : 0<B) (P : Menu n B) (choose : G → Fin B) :
    (Fintype.card G:ℚ)/(4*B)+1/2 ≤ ((∑ a,rank P (choose a) a : ℕ):ℚ)/Fintype.card G := by
  apply normalize (by exact_mod_cast (Fintype.card_pos : 0<Fintype.card G)) (by exact_mod_cast hB)
  exact_mod_cast rank_mass P choose

private theorem messages (hB : 0<B) : (univ : Finset (Fin B)).Nonempty := ⟨⟨0,hB⟩,mem_univ _⟩

/-- Give the hidden coordinate the lowest rank that any of the messages
could offer it. -/
noncomputable def bestRank (hB : 0<B) (P : Menu n B) (a : G) := univ.inf' (messages hB) (fun b => rank P b a)

theorem bestRank_le (hB : 0<B) (P : Menu n B) (a : G) (b : Fin B) : bestRank hB P a≤rank P b a :=
  inf'_le _ (mem_univ b)

theorem bestRank_partner (hB : 0<B) (P : Menu n B) (a : G) : bestRank hB P (n/a)=bestRank hB P a := by
  simp only [bestRank,rank,(hit_iff n (n/a) a).mpr (Or.inr rfl)]

theorem bestRank_floor (hB : 0<B) (P : Menu n B) :
    (Fintype.card G:ℚ)/(4*B)+1/2 ≤ ((∑ a,bestRank hB P a : ℕ):ℚ)/Fintype.card G := by
  choose b _ eq using fun a : G => exists_mem_eq_inf' (messages hB) (fun b => rank P b a)
  simpa only [bestRank,eq] using rank_floor hB P b

theorem bestRank_prefix (hB : 0<B) (P : Menu n B) (t : ℕ) :
    (univ.filter (fun a => bestRank hB P a≤t)).card ≤ 2*B*t := by
  choose b _ eq using fun a : G => exists_mem_eq_inf' (messages hB) (fun b => rank P b a)
  simpa only [bestRank,eq] using prefix_bound P b t

end PrimeFactors.FactorOrbitAdviceFloor
