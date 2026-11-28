import PrimeFactors.ResiduePairMultiplicity
import Mathlib.Data.Nat.Totient

/-! Actual frequencies of unordered distinct prime pairs with a fixed product
residue, when their sum is required to lie in a specified set. The weight
of each local solution depends on the prime populations of its two classes. -/
namespace PrimeFactors.ResiduePairWeights

open Finset

variable {m : ℕ} [NeZero m]

private noncomputable def pool (lo hi : ℕ) := (Ico lo hi).filter Nat.Prime

/-- Ordered pairs of local residues for the event under consideration. -/
noncomputable def cells (r : ZMod m) (A : Finset (ZMod m)) : Finset (ZMod m × ZMod m) :=
  univ.filter fun v => v.1*v.2=r ∧ v.1+v.2∈A

private noncomputable def residues (v : ℕ × ℕ) : ZMod m × ZMod m := (v.1,v.2)

private noncomputable def ordered (lo hi : ℕ) (r : ZMod m) (A : Finset (ZMod m)) :=
  (pool lo hi).offDiag.filter fun v => residues v ∈ cells r A

/-- One pair per two distinct primes, with the smaller prime first. -/
noncomputable def pairs (lo hi : ℕ) (r : ZMod m) (A : Finset (ZMod m)) :=
  (ordered lo hi r A).filter fun v => v.1<v.2

theorem mem_pairs {lo hi p q : ℕ} {r : ZMod m} {A : Finset (ZMod m)} :
    (p,q)∈pairs lo hi r A ↔ lo≤p ∧ p<q ∧ q<hi ∧ p.Prime ∧ q.Prime ∧
      ((p*q:ℕ):ZMod m)=r ∧ ((p+q:ℕ):ZMod m)∈A := by
  simp only [pairs,ordered,mem_filter,mem_offDiag,pool,mem_Ico,residues,cells,mem_univ,true_and,
    Nat.cast_mul,Nat.cast_add]
  constructor
  · rintro ⟨⟨⟨⟨⟨lp,_⟩,P⟩,⟨⟨_,qh⟩,Q⟩,_⟩,pr,sm⟩,lt⟩
    exact ⟨lp,lt,qh,P,Q,pr,sm⟩
  · rintro ⟨lp,lt,qh,P,Q,pr,sm⟩
    exact ⟨⟨⟨⟨⟨lp,lt.trans qh⟩,P⟩,⟨⟨lp.trans lt.le,qh⟩,Q⟩,lt.ne⟩,pr,sm⟩,lt⟩

private theorem ordered_twice (lo hi : ℕ) (r : ZMod m) (A : Finset (ZMod m)) :
    (ordered lo hi r A).card = 2*(pairs lo hi r A).card := by
  classical
  let S := ordered lo hi r A
  have flip {z : ℕ×ℕ} (h : z∈S) : z.swap∈S := by
    obtain ⟨mem,cell⟩ := mem_filter.mp h
    obtain ⟨p,q,ne⟩ := mem_offDiag.mp mem
    refine mem_filter.mpr ⟨mem_offDiag.mpr ⟨q,p,ne.symm⟩,?_⟩
    simpa only [cells,mem_filter,mem_univ,true_and,residues,Prod.fst_swap,Prod.snd_swap,
      mul_comm,add_comm] using cell
  let lt (z : ℕ×ℕ) := z.1<z.2
  have eq : (S.filter lt).card=(S.filter fun z => ¬lt z).card := by
    apply card_nbij' Prod.swap Prod.swap
    · intro z hz
      obtain ⟨mem,h⟩ := mem_filter.mp hz
      exact mem_filter.mpr ⟨flip mem,not_lt_of_ge h.le⟩
    · intro z hz
      obtain ⟨mem,h⟩ := mem_filter.mp hz
      have ne := (mem_offDiag.mp (mem_filter.mp mem).1).2.2
      exact mem_filter.mpr ⟨flip mem,lt_of_le_of_ne (le_of_not_gt h) ne.symm⟩
    · intro _ _; rfl
    · intro _ _; rfl
  have split := filter_card_add_filter_neg_card_eq_card (s:=S) lt
  change S.card=2*(S.filter lt).card
  omega

private noncomputable abbrev cls (lo hi : ℕ) (x : ZMod m) := ResiduePairMultiplicity.primes m lo hi x.val

private theorem mem_cls {lo hi p : ℕ} {x : ZMod m} : p ∈ cls lo hi x ↔
    p∈pool lo hi ∧ (p:ZMod m)=x := by
  rw [ResiduePairMultiplicity.mem_primes]
  simp only [pool,mem_filter,mem_Ico]
  have cast : p%m=x.val ↔ (p:ZMod m)=x := by
    rw [←ZMod.val_natCast m p]
    exact ⟨fun eq => ZMod.val_injective m eq,congrArg ZMod.val⟩
  tauto

/-- The actual number of primes in [lo,hi) representing x. -/
noncomputable def population (lo hi : ℕ) (x : ZMod m) : ℕ := (cls lo hi x).card

/-- An ordered residue pair contributes this many ordered pairs of distinct
primes. The factor in the second class decreases by one on the diagonal. -/
noncomputable def weight (lo hi : ℕ) (v : ZMod m × ZMod m) : ℕ :=
  population lo hi v.1 * (population lo hi v.2 - if v.1=v.2 then 1 else 0)

private theorem fiber (lo hi : ℕ) (x y : ZMod m) :
    ((pool lo hi).offDiag.filter (fun v => residues v=(x,y))).card=weight lo hi (x,y) := by
  classical
  by_cases eq : x=y
  · subst y
    have same : (pool lo hi).offDiag.filter (fun v => residues v=(x,x))=(cls lo hi x).offDiag := by
      ext ⟨p,q⟩
      simp only [mem_filter,mem_offDiag,residues,Prod.mk.injEq,mem_cls]
      tauto
    rw [same,offDiag_card]
    simp [weight,population,Nat.mul_sub_left_distrib]
  · have same : (pool lo hi).offDiag.filter (fun v => residues v=(x,y))=cls lo hi x ×ˢ cls lo hi y := by
      ext ⟨p,q⟩
      simp only [mem_filter,mem_offDiag,residues,Prod.mk.injEq,mem_product,mem_cls]
      constructor
      · tauto
      · rintro ⟨⟨pm,px⟩,⟨qm,qy⟩⟩
        exact ⟨⟨pm,qm,fun h => eq (px.symm.trans ((congrArg (fun z : ℕ => (z:ZMod m)) h).trans qy))⟩,px,qy⟩
    rw [same,card_product]
    simp [weight,population,eq]

/-- Exact sum of the local weights, allowing any fixed product residue. All
prime pairs in the given interval contribute once to the unordered count. -/
theorem exact_count (lo hi : ℕ) (r : ZMod m) (A : Finset (ZMod m)) :
    2*(pairs lo hi r A).card = ∑ v∈cells r A,weight lo hi v := by
  rw [←ordered_twice]
  exact (sum_card_fiberwise_eq_card_filter (pool lo hi).offDiag (cells r A) residues).symm.trans
    (sum_congr rfl (fun ⟨x,y⟩ _ => fiber lo hi x y))

/-- For a fixed unit product, the second residue is determined by the first. -/
noncomputable def classPair (r : ZMod m) (v : (ZMod m)ˣ) : ZMod m × ZMod m :=
  (v,(↑v⁻¹:ZMod m)*r)

noncomputable def starts (r : ZMod m) (A : Finset (ZMod m)) : Finset (ZMod m)ˣ :=
  univ.filter fun v => (classPair r v).1+(classPair r v).2∈A

omit [NeZero m] in
private theorem classPair_injective (r : ZMod m) : Function.Injective (classPair r) := by
  intro v w eq
  exact Units.ext (congrArg Prod.fst eq)

private theorem cells_image (r : ZMod m) (unit : IsUnit r) (A : Finset (ZMod m)) :
    cells r A = (starts r A).image (classPair r) := by
  ext ⟨x,y⟩
  simp only [cells,mem_filter,mem_univ,true_and,mem_image]
  constructor
  · rintro ⟨eq,sum⟩
    have ux := ((Commute.all x y).isUnit_mul_iff.mp (eq ▸ unit)).1
    obtain ⟨v,rfl⟩ := ux
    have val : classPair r v=((v:ZMod m),y) := by
      simp [classPair,←eq,←mul_assoc]
    exact ⟨v,mem_filter.mpr ⟨mem_univ _,by rwa [val]⟩,val⟩
  · rintro ⟨v,h,val⟩
    have eq : (classPair r v).1*(classPair r v).2=r := by simp [classPair,←mul_assoc]
    have sum := (mem_filter.mp h).2
    rw [val] at eq sum
    exact ⟨eq,sum⟩

/-- The weighted sum only requires considering one residue pair per starting
unit. No assumption on the relative sizes of the prime classes is needed. -/
theorem exact_by_unit (lo hi : ℕ) (r : ZMod m) (unit : IsUnit r) (A : Finset (ZMod m)) :
    2*(pairs lo hi r A).card=∑ x∈starts r A,weight lo hi (classPair r x) := by
  rw [exact_count,cells_image r unit,Finset.sum_image (fun _ _ _ _ eq => classPair_injective r eq)]

/-- Before selecting sums, precisely φ(m) ordered local roots are possible. -/
theorem all_cells_card (r : ZMod m) (unit : IsUnit r) : (cells r univ).card=m.totient := by
  rw [cells_image r unit,card_image_of_injective _ (classPair_injective r)]
  simp [starts,ZMod.card_units_eq_totient]

/-- Uniform weight total, with the diagonal correction retained. -/
noncomputable def uniform (r : ZMod m) (A : Finset (ZMod m)) (k : ℕ) : ℕ :=
  ∑ v∈cells r A,k*(k-if v.1=v.2 then 1 else 0)

/-- Only the unit-class populations occur when the fixed product is a unit. -/
theorem count_bounds {lo hi l u : ℕ} (r : ZMod m) (unit : IsUnit r) (A : Finset (ZMod m))
    (pop : ∀ x : ZMod m, IsUnit x → l≤population lo hi x ∧ population lo hi x≤u) :
    uniform r A l ≤ 2*(pairs lo hi r A).card ∧ 2*(pairs lo hi r A).card ≤ uniform r A u := by
  have both {v : ZMod m×ZMod m} (h : v∈cells r A) : IsUnit v.1 ∧ IsUnit v.2 :=
    (Commute.all v.1 v.2).isUnit_mul_iff.mp (by rw [(mem_filter.mp h).2.1]; exact unit)
  rw [exact_count]
  exact ⟨sum_le_sum (fun v h => Nat.mul_le_mul (pop _ (both h).1).1
    (Nat.sub_le_sub_right (pop _ (both h).2).1 _)),sum_le_sum (fun v h =>
      Nat.mul_le_mul (pop _ (both h).1).2 (Nat.sub_le_sub_right (pop _ (both h).2).2 _))⟩

/-- Equal class populations imply the exact uniform-weight formula. -/
theorem equal_populations {lo hi k : ℕ} (r : ZMod m) (unit : IsUnit r) (A : Finset (ZMod m))
    (pop : ∀ x : ZMod m, IsUnit x → population lo hi x=k) :
    2*(pairs lo hi r A).card=uniform r A k := by
  have h := count_bounds r unit A (fun x ux => ⟨(pop x ux).ge,(pop x ux).le⟩)
  exact h.2.antisymm h.1

/-- At uniform population k, a diagonal cell loses k ordered pairs from the
unrestricted product k². This formula also holds for k=0. -/
theorem uniform_diagonal (r : ZMod m) (A : Finset (ZMod m)) (k : ℕ) :
    uniform r A k + ((cells r A).filter (fun v => v.1=v.2)).card*k = (cells r A).card*k^2 := by
  classical
  have diag : ((cells r A).filter (fun v => v.1=v.2)).card*k =
      ∑ v∈cells r A,(if v.1=v.2 then k else 0) := by simp [sum_ite]
  rw [uniform,diag,←sum_add_distrib]
  apply sum_const_nat
  intro v _
  by_cases eq : v.1=v.2
  · simp only [if_pos eq]
    cases k with
    | zero => rfl
    | succ k => simp only [Nat.add_one_sub_one,pow_two]; ring
  · simp [eq,pow_two]

/-- Conditional frequency bounds among all actual pairs with this product residue.
The denominator condition is implied by a positive lower bound from the uniform model. -/
theorem frequency_bounds {lo hi l u : ℕ} (r : ZMod m) (unit : IsUnit r) (A : Finset (ZMod m))
    (pop : ∀ x : ZMod m, IsUnit x → l≤population lo hi x ∧ population lo hi x≤u)
    (positive : 0<uniform r univ l) :
    (uniform r A l:ℚ)/(uniform r univ u) ≤ ((pairs lo hi r A).card:ℚ)/(pairs lo hi r univ).card ∧
      ((pairs lo hi r A).card:ℚ)/(pairs lo hi r univ).card ≤ (uniform r A u:ℚ)/(uniform r univ l) := by
  obtain ⟨la,ua⟩ := count_bounds r unit A pop
  obtain ⟨lt,ut⟩ := count_bounds r unit univ pop
  have pt : 0<(pairs lo hi r univ).card := by omega
  have pu : 0<uniform r univ u := by omega
  constructor
  · apply (div_le_div_iff₀ (Nat.cast_pos.mpr pu) (Nat.cast_pos.mpr pt)).mpr
    exact_mod_cast (show uniform r A l * (pairs lo hi r univ).card ≤
      (pairs lo hi r A).card * uniform r univ u by nlinarith only [Nat.mul_le_mul la ut])
  · apply (div_le_div_iff₀ (Nat.cast_pos.mpr pt) (Nat.cast_pos.mpr positive)).mpr
    exact_mod_cast (show (pairs lo hi r A).card * uniform r univ l ≤
      uniform r A u * (pairs lo hi r univ).card by nlinarith only [Nat.mul_le_mul ua lt])

/-- There are two primes per unit class modulo five in [7,32). Even with
these equal populations, the three admissible sums at product residue one
occur with different frequencies. -/
theorem classroom :
    (∀ x : ZMod 5, IsUnit x → population 7 32 x=2) ∧
    (pairs 7 32 (1:ZMod 5) {0}).card=4 ∧ (pairs 7 32 (1:ZMod 5) {2}).card=1 ∧
    (pairs 7 32 (1:ZMod 5) {3}).card=1 ∧ (pairs 7 32 (1:ZMod 5) univ).card=6 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have nonzero : ∀ x : ZMod 5, x≠0 → population 7 32 x=2 := by decide +kernel
  have all (x : ZMod 5) (unit : IsUnit x) := nonzero x unit.ne_zero
  have weightTable : uniform (1:ZMod 5) {0} 2=8 ∧ uniform (1:ZMod 5) {2} 2=2 ∧
      uniform (1:ZMod 5) {3} 2=2 ∧ uniform (1:ZMod 5) univ 2=12 := by decide +kernel
  have s₀ := equal_populations (1:ZMod 5) isUnit_one {0} all
  have s₂ := equal_populations (1:ZMod 5) isUnit_one {2} all
  have s₃ := equal_populations (1:ZMod 5) isUnit_one {3} all
  have full := equal_populations (1:ZMod 5) isUnit_one univ all
  exact ⟨all,by omega,by omega,by omega,by omega⟩

end PrimeFactors.ResiduePairWeights
