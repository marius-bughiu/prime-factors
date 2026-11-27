import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.FinCases

/-! Recover local Legendre sign rows from the complete space of square-rootable
generator masks and the public Jacobi row. A mask records which signed integer
generators occur an odd number of times. -/
namespace PrimeFactors.RootableSignSpan

abbrev Bit := ZMod 2
abbrev Mask (s : ℕ) := Fin s → Bit
abbrev Row (s : ℕ) := Module.Dual Bit (Mask s)

/-- On inputs coprime to the modulus, encode +1 as zero and −1 as one. -/
noncomputable def bit (a : ℤ) : Bit := if a = 1 then 0 else 1

theorem bit_mul {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    bit (a*b) = bit a + bit b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

/-- The linear functional with the specified binary coefficients. -/
noncomputable def row {s : ℕ} (c : Fin s → Bit) : Row s :=
  ∑ i, c i • LinearMap.proj i

theorem row_apply {s : ℕ} (c : Fin s → Bit) (v : Mask s) :
    row c v = ∑ i, c i * v i := by
  simp [row, LinearMap.sum_apply, LinearMap.proj_apply]

/-- One Legendre sign per signed generator. -/
noncomputable def localRow {s : ℕ} (p : ℕ) [Fact p.Prime] (g : Fin s → ℤ) : Row s :=
  row fun i => bit (legendreSym p (g i))

/-- The public row uses the product alone. -/
noncomputable def publicRow {s : ℕ} (N : ℕ) (g : Fin s → ℤ) : Row s :=
  row fun i => bit (jacobiSym (g i) N)

theorem public_eq_add {s p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (g : Fin s → ℤ) (gp : ∀ i, (g i : ZMod p) ≠ 0) (gq : ∀ i, (g i : ZMod q) ≠ 0) :
    publicRow (p*q) g = localRow p g + localRow q g := by
  apply LinearMap.ext
  intro v
  simp only [publicRow, localRow, row_apply, LinearMap.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [jacobiSym.mul_right' _ hp.out.ne_zero hq.out.ne_zero,
    ← jacobiSym.legendreSym.to_jacobiSym p, ← jacobiSym.legendreSym.to_jacobiSym q,
    bit_mul (legendreSym.eq_one_or_neg_one p (gp i)) (legendreSym.eq_one_or_neg_one q (gq i)),
    add_mul]

/-- The actual signed integer represented by a binary exponent mask. -/
noncomputable def word {s : ℕ} (g : Fin s → ℤ) (v : Mask s) : ℤ := ∏ i, if v i = 0 then 1 else g i

private theorem word_local {s p : ℕ} [Fact p.Prime] (g : Fin s → ℤ) (v : Mask s)
    (gp : ∀ i, (g i : ZMod p) ≠ 0) :
    IsSquare (word g v : ZMod p) ↔ localRow p g v = 0 := by
  let f (i : Fin s) : ℤ := if v i = 0 then 1 else g i
  have nz (t : Finset (Fin s)) : ((∏ i ∈ t, f i : ℤ) : ZMod p) ≠ 0 := by
    push_cast
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    by_cases h : v i = 0 <;> simp [f,h,gp]
  have mask (t : Finset (Fin s)) :
      bit (legendreSym p (∏ i ∈ t, f i)) = ∑ i ∈ t, bit (legendreSym p (g i)) * v i := by
    induction t using Finset.induction_on with
    | empty => simp [legendreSym.at_one, bit]
    | @insert i t hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, legendreSym.mul,
        bit_mul (legendreSym.eq_one_or_neg_one p (by by_cases h : v i = 0 <;> simp [f,h,gp]))
          (legendreSym.eq_one_or_neg_one p (nz t)), ih]
      congr 1
      have either : v i = 0 ∨ v i = 1 := (by decide : ∀ b : Bit, b = 0 ∨ b = 1) (v i)
      rcases either with h | h <;> simp [f,h,bit,legendreSym.at_one]
  change IsSquare ((∏ i, f i : ℤ) : ZMod p) ↔ _
  rw [← legendreSym.eq_one_iff p (nz Finset.univ)]
  change legendreSym p (∏ i, f i) = 1 ↔ row _ v = 0
  rw [row_apply, ← mask Finset.univ]
  simp [bit]

/-- The rootable masks are the common kernel of the two local sign rows. -/
theorem rootable_iff {s p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (g : Fin s → ℤ) (gp : ∀ i, (g i : ZMod p) ≠ 0) (gq : ∀ i, (g i : ZMod q) ≠ 0)
    (v : Mask s) :
    IsSquare (word g v : ZMod (p*q)) ↔ v ∈ LinearMap.ker (localRow p g) ⊓ LinearMap.ker (localRow q g) := by
  change _ ↔ localRow p g v = 0 ∧ localRow q g v = 0
  rw [← word_local g v gp, ← word_local g v gq]
  let e := ZMod.chineseRemainder cop
  constructor
  · rintro ⟨z,hz⟩
    have h := congrArg e hz
    rw [map_intCast,map_mul] at h
    exact ⟨⟨_,congrArg Prod.fst h⟩,⟨_,congrArg Prod.snd h⟩⟩
  · rintro ⟨⟨u,hu⟩,⟨w,hw⟩⟩
    refine ⟨e.symm (u,w),e.injective ?_⟩
    rw [map_intCast,map_mul,e.apply_symm_apply]
    exact Prod.ext hu hw

section Reconstruction

variable {s : ℕ} (x y : Row s)

/-- All linear tests vanishing on the complete rootable space are precisely
the combinations of the two local rows. -/
theorem annihilator : (LinearMap.ker x ⊓ LinearMap.ker y).dualAnnihilator = Submodule.span Bit {x,y} := by
  have eq : (Submodule.span Bit {x,y}).dualCoannihilator = LinearMap.ker x ⊓ LinearMap.ker y := by
    apply SetLike.coe_injective
    simp [Submodule.coe_dualCoannihilator_span, Set.ext_iff, LinearMap.mem_ker]
  rw [← eq, Subspace.dualCoannihilator_dualAnnihilator_eq]

private theorem four {z : Row s} (hz : z ∈ Submodule.span Bit {x,y}) :
    z = 0 ∨ z = x ∨ z = y ∨ z = x+y := by
  obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hz
  fin_cases a <;> fin_cases b <;> simp

/-- In rank two the other two nonzero rows, after removing the public sum,
are exactly the two factor rows. The formula in fact only requires that
both factor rows be nonzero. -/
theorem recover (hx : x ≠ 0) (hy : y ≠ 0) :
    {z | z ∈ (LinearMap.ker x ⊓ LinearMap.ker y).dualAnnihilator ∧ z ≠ 0 ∧ z ≠ x+y} = {x,y} := by
  ext z
  rw [Set.mem_setOf_eq, annihilator]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hz,nz,ns⟩
    rcases four x y hz with h | h | h | h
    · exact (nz h).elim
    · exact Or.inl h
    · exact Or.inr h
    · exact (ns h).elim
  · rintro (rfl | rfl)
    · exact ⟨Submodule.subset_span (by simp),hx,by simpa using hy⟩
    · exact ⟨Submodule.subset_span (by simp),hy,by simpa using hx⟩

/-- Partial positive witnesses only give an inclusion in the opposite direction. -/
theorem partial_bound (L : Submodule Bit (Mask s)) (witnessed : L ≤ LinearMap.ker x ⊓ LinearMap.ker y) :
    Submodule.span Bit {x,y} ≤ L.dualAnnihilator :=
  (annihilator x y) ▸ Submodule.dualAnnihilator_anti witnessed

/-- A dimension certificate can close the inclusion obtained from partial witnesses. -/
theorem complete_of_dimension (L : Submodule Bit (Mask s)) (witnessed : L ≤ LinearMap.ker x ⊓ LinearMap.ker y)
    (dim : Module.finrank Bit L.dualAnnihilator = Module.finrank Bit (Submodule.span Bit {x,y})) :
    L = LinearMap.ker x ⊓ LinearMap.ker y := by
  have eq := Submodule.eq_of_le_of_finrank_eq (partial_bound x y L witnessed) dim.symm
  have same : (LinearMap.ker x ⊓ LinearMap.ker y).dualAnnihilator = L.dualAnnihilator := (annihilator x y).trans eq
  simpa only [Subspace.dualAnnihilator_dualCoannihilator_eq] using
    (congrArg Submodule.dualCoannihilator same).symm

/-- Choose the order of the rows by their values at a mask with negative public sign. -/
theorem orient (n : Row s) (sum : x+y = n) (a : Mask s) (ha : n a = 1) :
    (x a = 0 ∧ y a = 1) ∨ (y a = 0 ∧ x a = 1) := by
  rw [← sum, LinearMap.add_apply] at ha
  exact (by decide : ∀ b c : Bit, b+c = 1 → (b=0 ∧ c=1) ∨ (c=0 ∧ b=1)) _ _ ha

/-- Subtracting the public bit times the anchor moves v into the public kernel.
The oriented row vanishes on v exactly when this corrected mask has a root. -/
theorem oriented_query (n : Row s) (sum : x+y = n) (a : Mask s)
    (ha : n a = 1) (oriented : x a = 0) (v : Mask s) :
    let h := v - n v • a
    n h = 0 ∧ (x v = 0 ↔ h ∈ LinearMap.ker x ⊓ LinearMap.ker y) := by
  let h := v - n v • a
  have nh : n h = 0 := by simp [h,ha]
  have xh : x h = x v := by simp [h,oriented]
  have both : x h + y h = 0 := by simpa [← sum] using nh
  refine ⟨nh,?_⟩
  change x v = 0 ↔ x h = 0 ∧ y h = 0
  rw [xh] at both ⊢
  exact ⟨fun z => ⟨z,by simpa [z] using both⟩,And.left⟩

end Reconstruction

/-- For a complete space of square-rootable generator masks, deleting zero
and the public Jacobi row recovers the unordered local rows when both are
nonzero. In particular this applies whenever they are linearly independent. -/
theorem factor_rows {s p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (g : Fin s → ℤ) (gp : ∀ i, (g i : ZMod p) ≠ 0) (gq : ∀ i, (g i : ZMod q) ≠ 0)
    (K : Submodule Bit (Mask s))
    (complete : ∀ v, v ∈ K ↔ IsSquare (word g v : ZMod (p*q)))
    (xp : localRow p g ≠ 0) (yq : localRow q g ≠ 0) :
    {z | z ∈ K.dualAnnihilator ∧ z ≠ 0 ∧ z ≠ publicRow (p*q) g} = {localRow p g, localRow q g} := by
  have eq : K = LinearMap.ker (localRow p g) ⊓ LinearMap.ker (localRow q g) :=
    SetLike.ext fun v => (complete v).trans (rootable_iff cop g gp gq v)
  rw [eq, public_eq_add g gp gq]
  exact recover _ _ xp yq

/-- Unordered pairs of abstract rows consistent with the known public sum and
a subspace of witnessed positive masks. Repeated rows would be represented by
a singleton, and a nonzero public sum rules out that case. -/
def Compatible {s : ℕ} (n : Row s) (L : Submodule Bit (Mask s)) (P : Set (Row s)) : Prop :=
  ∃ x y : Row s, P = {x,y} ∧ x+y = n ∧ L ≤ LinearMap.ker x ⊓ LinearMap.ker y

private theorem oriented_mem {s : ℕ} (L : Submodule Bit (Mask s)) (a : Mask s) (z : Row s) :
    z ∈ (L ⊔ Submodule.span Bit {a}).dualAnnihilator ↔ L ≤ LinearMap.ker z ∧ z a = 0 := by
  rw [Submodule.mem_dualAnnihilator]
  change (L ⊔ Submodule.span Bit {a} ≤ LinearMap.ker z) ↔ _
  rw [sup_le_iff, Submodule.span_le, Set.singleton_subset_iff]
  rfl

private noncomputable def orientedEquiv {s : ℕ} (n : Row s) (L : Submodule Bit (Mask s))
    (positive : L ≤ LinearMap.ker n) (a : Mask s) (ha : n a = 1) :
    (L ⊔ Submodule.span Bit {a}).dualAnnihilator ≃ {P : Set (Row s) // Compatible n L P} := by
  let f (z : (L ⊔ Submodule.span Bit {a}).dualAnnihilator) :
      {P : Set (Row s) // Compatible n L P} := by
    refine ⟨{z.val,n-z.val},z.val,n-z.val,rfl,by abel,?_⟩
    obtain ⟨onL,_⟩ := (oriented_mem L a _).mp z.property
    refine le_inf onL ?_
    intro v hv
    change n v - z.val v = 0
    rw [show n v = 0 from positive hv, show z.val v = 0 from onL hv,sub_self]
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro u v eq
    have sets : ({u.val,n-u.val} : Set (Row s)) = {v.val,n-v.val} := congrArg Subtype.val eq
    rcases Set.pair_eq_pair_iff.mp sets with h | h
    · exact Subtype.ext h.1
    · have atA := LinearMap.congr_fun h.1 a
      rw [(oriented_mem L a _).mp u.property |>.2, LinearMap.sub_apply,
        (oriented_mem L a _).mp v.property |>.2,ha,sub_zero] at atA
      exact (zero_ne_one atA).elim
  · rintro ⟨P,x,y,rfl,sum,both⟩
    rcases orient x y n sum a ha with hx | hy
    · refine ⟨⟨x,(oriented_mem L a _).mpr ⟨both.trans inf_le_left,hx.1⟩⟩,Subtype.ext ?_⟩
      change ({x,n-x} : Set (Row s)) = {x,y}
      rw [← sum,add_sub_cancel_left]
    · refine ⟨⟨y,(oriented_mem L a _).mpr ⟨both.trans inf_le_right,hy.1⟩⟩,Subtype.ext ?_⟩
      change ({y,n-y} : Set (Row s)) = {x,y}
      rw [← sum,add_sub_cancel_right,Set.pair_comm]

private theorem anchor_dimension {s : ℕ} (n : Row s) (L : Submodule Bit (Mask s))
    (positive : L ≤ LinearMap.ker n) (a : Mask s) (ha : n a = 1) :
    Module.finrank Bit (L ⊔ Submodule.span Bit {a} : Submodule Bit (Mask s)) = Module.finrank Bit L + 1 := by
  have outside : a ∉ L := fun h => zero_ne_one ((show n a = 0 from positive h).symm.trans ha)
  have nonzero : a ≠ 0 := fun h => outside (h ▸ L.zero_mem)
  have disj := Submodule.disjoint_span_singleton_of_not_mem outside
  have sup := Submodule.finrank_sup_add_finrank_inf_eq L (Submodule.span Bit {a})
  rw [disj.eq_bot,finrank_bot,add_zero,finrank_span_singleton nonzero] at sup
  exact sup

/-- With a nonzero public row, r independent positive masks among s generators
leave exactly 2^(s-r-1) possible unordered pairs of abstract sign rows. -/
theorem compatible_count {s : ℕ} (n : Row s) (L : Submodule Bit (Mask s))
    (positive : L ≤ LinearMap.ker n) (a : Mask s) (ha : n a = 1) :
    Nat.card {P : Set (Row s) // Compatible n L P} = 2^(s - Module.finrank Bit L - 1) := by
  have sup := anchor_dimension n L positive a ha
  have dim := Subspace.finrank_add_finrank_dualAnnihilator_eq (L ⊔ Submodule.span Bit {a})
  rw [sup] at dim
  have size : Module.finrank Bit (Mask s) = s := by simp [Mask, Module.finrank_fintype_fun_eq_card]
  rw [size] at dim
  rw [← Nat.card_congr (orientedEquiv n L positive a ha),
    Module.natCard_eq_pow_finrank (K := Bit),Nat.card_eq_fintype_card,ZMod.card]
  congr 1
  omega
/-- A fixed list of s-r-1 queries inside the public kernel distinguishes all
the oriented possibilities. The list uses only n, L and the public anchor.
For the actual local rows, zero is exactly a positive square-rootability
answer on these masks by `oriented_query`. -/
theorem distinguishing_queries {s : ℕ} (n : Row s) (L : Submodule Bit (Mask s))
    (positive : L ≤ LinearMap.ker n) (a : Mask s) (ha : n a = 1) :
    ∃ Q : Fin (s - Module.finrank Bit L - 1) → Mask s,
      (∀ i, n (Q i) = 0) ∧
      ∀ z w : (L ⊔ Submodule.span Bit {a}).dualAnnihilator,
        (∀ i, z.val (Q i) = w.val (Q i)) → z = w := by
  let W := L ⊔ Submodule.span Bit {a}
  obtain ⟨C,compl⟩ := W.exists_isCompl
  have dims := Submodule.finrank_sup_add_finrank_inf_eq W C
  rw [compl.sup_eq_top,compl.inf_eq_bot,finrank_bot,add_zero,finrank_top] at dims
  have size : Module.finrank Bit (Mask s) = s := by simp [Mask, Module.finrank_fintype_fun_eq_card]
  have dimW := anchor_dimension n L positive a ha
  change Module.finrank Bit W = _ at dimW
  rw [dimW,size] at dims
  let b := Module.finBasisOfFinrankEq Bit C (show Module.finrank Bit C = s - Module.finrank Bit L - 1 by omega)
  let Q (i) : Mask s := (b i : Mask s) - n (b i : Mask s) • a
  refine ⟨Q,fun i => by simp [Q,ha],?_⟩
  intro z w tests
  have za := ((oriented_mem L a _).mp z.property).2
  have wa := ((oriented_mem L a _).mp w.property).2
  have onC : z.val.comp C.subtype = w.val.comp C.subtype := by
    apply b.ext
    intro i
    simpa [Q,za,wa] using tests i
  apply Subtype.ext
  apply LinearMap.eqLocus_eq_top.mp
  apply top_unique
  rw [← compl.sup_eq_top]
  apply sup_le
  · intro t ht
    exact ((Submodule.mem_dualAnnihilator _).mp z.property _ ht).trans
      ((Submodule.mem_dualAnnihilator _).mp w.property _ ht).symm
  · intro t ht
    exact LinearMap.congr_fun onC ⟨t,ht⟩

end PrimeFactors.RootableSignSpan
