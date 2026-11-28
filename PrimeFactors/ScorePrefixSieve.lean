import PrimeFactors.StreamSumScores

/-! Counting how many entries of a score-ordered prefix survive one further
coprime residue test. A visit is one old passing position, including the target. -/
namespace PrimeFactors.ScorePrefixSieve

open Finset StreamSumScores PeriodicSumRank ScoreSumOrder
open private PrimeFactors.StreamSumScores.before_trans from PrimeFactors.StreamSumScores
open scoped Classical

private def residue (t : ℕ) : Fin 100 := ⟨t%100,Nat.mod_lt _ (by decide)⟩
noncomputable def residues (n : ℕ) := (univ : Finset (Fin 100)).filter (fun r => passes (n%100) r.val)

/-- The bound of ten applies to unit products modulo five. -/
theorem at_most_ten {n : ℕ} (unit : n%5≠0) : (residues n).card≤10 := by
  have check : ∀ v : Fin 100, v.val%5≠0 →
      ((univ : Finset (Fin 100)).filter (fun r => passes v.val r.val)).card≤10 := by decide +kernel
  exact check (residue n) (by simpa only [residue,Nat.mod_mod_of_dvd n (by decide : 5∣100)] using unit)

private noncomputable def indices (n lo hi s : ℕ) (r : Fin 100) :=
  (range (hi+1)).filter fun j => term lo r j∈ScoreSumOrder.«prefix» n lo hi s
noncomputable def length (n lo hi s : ℕ) (r : Fin 100) := (indices n lo hi s r).card

private theorem term_inj (lo : ℕ) (r : Fin 100) : Function.Injective (term lo r) := by
  intro i j eq
  unfold term at eq
  omega

private theorem mem_indices {n lo hi s j : ℕ} {r : Fin 100} : j∈indices n lo hi s r ↔
    term lo r j∈ScoreSumOrder.«prefix» n lo hi s := by
  refine ⟨fun h => (mem_filter.mp h).2,fun h => mem_filter.mpr ⟨mem_range.mpr ?_,h⟩⟩
  have upper := (mem_prefix.mp h).1.2
  unfold term at upper
  omega

private theorem initial (n lo hi s : ℕ) (r : Fin 100) : indices n lo hi s r=range (length n lo hi s r) := by
  let J := indices n lo hi s r
  have lower {j k : ℕ} (hit : j∈J) (le : k≤j) : k∈J := by
    obtain ⟨⟨_,upper⟩,pass,ord⟩ := mem_prefix.mp (mem_indices.mp hit)
    apply mem_indices.mpr
    apply mem_prefix.mpr
    have sr := term_spec lo r k
    have jr := term_spec lo r j
    exact ⟨⟨sr.1,(show term lo r k≤term lo r j by unfold term; omega).trans upper⟩,
      by rwa [sr.2.1,←jr.2.1],PrimeFactors.StreamSumScores.before_trans ((ordered ..).mpr le) ord⟩
  change J=range J.card
  by_cases h : J.Nonempty
  · have eq : J=range (J.max' h+1) := by
      ext j
      rw [mem_range,Nat.lt_succ_iff]
      exact ⟨fun hj => J.le_max' j hj,fun hj => lower (J.max'_mem h) hj⟩
    have size := (congrArg Finset.card eq).trans (card_range _)
    exact eq.trans (congrArg range size.symm)
  · simp [not_nonempty_iff_eq_empty.mp h]

/-- Each residue slice is exactly the indicated initial progression. -/
theorem slice (n lo hi s : ℕ) (r : Fin 100) :
    ((ScoreSumOrder.«prefix» n lo hi s).filter (fun t => residue t=r)) =
      (range (length n lo hi s r)).image (term lo r) := by
  rw [←initial]
  ext t
  constructor
  · intro h
    obtain ⟨inP,cls⟩ := mem_filter.mp h
    obtain ⟨⟨l,upper⟩,pass,_⟩ := mem_prefix.mp inP
    obtain ⟨_,⟨⟨c,j⟩,⟨_,reach⟩,_⟩⟩ := (partition n lo hi t).mp ⟨l,upper,pass⟩
    change term lo c j=t at reach
    have cr : residue t=c := by apply Fin.ext; exact reach ▸ (term_spec lo c j).2.1
    have same := cr.symm.trans cls
    have reach' : term lo r j=t := by rwa [←same]
    exact mem_image.mpr ⟨j,mem_indices.mpr (by rwa [reach']),reach'⟩
  · rintro h
    obtain ⟨j,hj,rfl⟩ := mem_image.mp h
    exact mem_filter.mpr ⟨mem_indices.mp hj,Fin.ext (term_spec lo r j).2.1⟩

/-- The complete visited set is the union of these streams. -/
theorem decomposition (n lo hi s : ℕ) : ScoreSumOrder.«prefix» n lo hi s=
    (residues n).biUnion (fun r => (range (length n lo hi s r)).image (term lo r)) := by
  simp_rw [←slice]
  ext t
  constructor
  · intro h
    exact mem_biUnion.mpr ⟨residue t,mem_filter.mpr ⟨mem_univ _,(mem_prefix.mp h).2.1⟩,mem_filter.mpr ⟨h,rfl⟩⟩
  · intro h
    obtain ⟨_,_,hit⟩ := mem_biUnion.mp h
    exact (mem_filter.mp hit).1

private theorem total_length (n lo hi s : ℕ) :
    (ScoreSumOrder.«prefix» n lo hi s).card=∑ r∈residues n,length n lo hi s r := by
  have h := card_eq_sum_card_fiberwise (s:=ScoreSumOrder.«prefix» n lo hi s) (t:=residues n) (f:=residue)
    (fun t ht => mem_filter.mpr ⟨mem_univ _,(mem_prefix.mp ht).2.1⟩)
  simpa only [slice,card_image_of_injective _ (term_inj _ _),card_range] using h

private theorem one_stream {L : ℕ} [NeZero L] (cop : Nat.Coprime 100 L) (A : Finset (ZMod L))
    (lo : ℕ) (r : Fin 100) (j : ℕ) :
    L*(((range j).image (term lo r)).filter (fun t : ℕ => (t:ZMod L)∈A)).card ≤ (j+L)*A.card := by
  let S := (range j).filter (fun i => (term lo r i:ZMod L)∈A)
  have same : (((range j).image (term lo r)).filter fun t : ℕ => (t:ZMod L)∈A)=S.image (term lo r) := by
    ext t
    simp only [S,mem_image,mem_filter]
    constructor
    · rintro ⟨⟨i,hi,rfl⟩,ha⟩
      exact ⟨i,⟨hi,ha⟩,rfl⟩
    · rintro ⟨i,⟨hi,ha⟩,rfl⟩
      exact ⟨⟨i,hi,rfl⟩,ha⟩
  let code (i : S) : Fin (j/L+1) × A :=
    (⟨i.val/L,Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt (mem_range.mp (mem_filter.mp i.property).1)))⟩,
      ⟨(term lo r i.val:ZMod L),(mem_filter.mp i.property).2⟩)
  have inject : Function.Injective code := by
    intro a b h
    have quot : a.val/L=b.val/L := congrArg (fun t => t.1.val) h
    have residues : (term lo r a.val:ZMod L)=(term lo r b.val:ZMod L) := congrArg (fun t => t.2.val) h
    simp only [term,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,add_right_inj] at residues
    have eq : (a.val:ZMod L)=(b.val:ZMod L) := ((ZMod.isUnit_iff_coprime _ _).mpr cop).mul_left_cancel residues
    have rem := (ZMod.natCast_eq_natCast_iff' _ _ _).mp eq
    exact Subtype.ext (by simpa only [Nat.div_add_mod] using congrArg₂ (fun q z => L*q+z) quot rem)
  have bound := Nat.card_le_card_of_injective code inject
  simp only [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_coe,Fintype.card_fin] at bound
  rw [same,card_image_of_injective _ (term_inj ..)]
  calc
    _ ≤ L*((j/L+1)*A.card) := Nat.mul_le_mul_left _ bound
    _ = (j/L*L+L)*A.card := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.div_mul_le_self ..) _)

noncomputable def filtered {L : ℕ} (n lo hi s : ℕ) (A : Finset (ZMod L)) :=
  (ScoreSumOrder.«prefix» n lo hi s).filter (fun t : ℕ => (t:ZMod L)∈A)

/-- The density contribution is multiplied by the exact original prefix
length. Each of at most ten residue progressions contributes one partial block. -/
theorem filtered_bound {n L : ℕ} [NeZero L] (unit : n%5≠0) (cop : Nat.Coprime 100 L)
    (A : Finset (ZMod L)) (lo hi s : ℕ) : L*(filtered n lo hi s A).card ≤
      (ScoreSumOrder.«prefix» n lo hi s).card*A.card+10*L*A.card := by
  let old := ScoreSumOrder.«prefix» n lo hi s
  let new := filtered n lo hi s A
  have count := card_eq_sum_card_fiberwise (s:=new) (t:=residues n) (f:=residue)
    (fun t ht => mem_filter.mpr ⟨mem_univ _,(mem_prefix.mp (mem_filter.mp ht).1).2.1⟩)
  have piece (r : Fin 100) : L*(new.filter (fun t => residue t=r)).card ≤ (length n lo hi s r+L)*A.card := by
    have swap : new.filter (fun t => residue t=r) = (old.filter (fun t => residue t=r)).filter (fun t : ℕ => (t:ZMod L)∈A) := by
      ext t; simp [new,filtered,old,and_assoc,and_comm,and_left_comm]
    rw [swap]
    change L*(((ScoreSumOrder.«prefix» n lo hi s).filter _).filter _).card≤_
    rw [slice]
    exact one_stream cop A lo r _
  change L*new.card≤_
  rw [count,mul_sum]
  calc
    _ ≤ ∑ r∈residues n,(length n lo hi s r+L)*A.card := sum_le_sum (fun r _ => piece r)
    _ = (ScoreSumOrder.«prefix» n lo hi s).card*A.card+(residues n).card*L*A.card := by
      rw [←sum_mul,sum_add_distrib,←total_length,sum_const]; simp [add_mul]
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (at_most_ten unit))) _

/-- A filter passing the true sum preserves the unique successful integer-square test. -/
theorem true_hit {p q b L : ℕ} (A : Finset (ZMod L)) (size : 3≤b) (pl : b≤p)
    (ord : p<q) (qu : q<2*b) (pp : p.Prime) (qp : q.Prime) (accept : ((p+q:ℕ):ZMod L)∈A) :
    (filtered (p*q) (ceilSqrt (4*(p*q))) (ProductDeficitBand.sumCap (p*q) b) (p+q) A).filter
      (fun t => IsSquare (t^2-4*(p*q)))={p+q} := by
  have known := ScoreSumOrder.unique_hit size pl ord qu pp qp
  ext t
  have iff := Finset.ext_iff.mp known t
  simp only [filtered,mem_filter,mem_singleton] at iff ⊢
  constructor
  · rintro ⟨⟨h,_⟩,sq⟩
    exact iff.mp ⟨h,sq⟩
  · rintro rfl
    have good := iff.mpr rfl
    exact ⟨⟨good.1,accept⟩,good.2⟩

end PrimeFactors.ScorePrefixSieve
