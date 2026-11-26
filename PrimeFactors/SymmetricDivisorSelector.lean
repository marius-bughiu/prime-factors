import PrimeFactors.LeastSeparatingModulus
import PrimeFactors.FixedDivisorSignatures

/-! Construct a separator whose wheel offsets can also be paired under
reflection, even if a single supplied Jacobi character swaps its signs. -/
namespace PrimeFactors.SymmetricDivisorSelector

open Finset DivisorResidueCover ReciprocalWheel

variable {W : ℕ} [NeZero W]

/-- The smaller of a residue's two unsigned representatives up to sign. -/
def rank (x : (ZMod W)ˣ) : ℕ := min (x : ZMod W).val ((-x : (ZMod W)ˣ) : ZMod W).val

omit [NeZero W] in
theorem rank_neg (x : (ZMod W)ˣ) : rank (-x) = rank x := by simp [rank,min_comm]

theorem rank_eq (x y : (ZMod W)ˣ) : rank x = rank y ↔ x=y ∨ x= -y := by
  constructor
  · intro eq
    have inj {a b : (ZMod W)ˣ} (h : (a:ZMod W).val=(b:ZMod W).val) : a=b :=
      Units.ext (ZMod.val_injective W h)
    unfold rank at eq
    rcases le_total (x:ZMod W).val ((-x:(ZMod W)ˣ):ZMod W).val with a|a <;>
      rcases le_total (y:ZMod W).val ((-y:(ZMod W)ˣ):ZMod W).val with b|b
    · exact Or.inl (inj (by simpa only [min_eq_left a,min_eq_left b] using eq))
    · exact Or.inr (inj (by simpa only [min_eq_left a,min_eq_right b] using eq))
    · exact Or.inr (neg_eq_iff_eq_neg.mp (inj (by simpa only [min_eq_right a,min_eq_left b] using eq)))
    · exact Or.inl (neg_inj.mp (inj (by simpa only [min_eq_right a,min_eq_right b] using eq)))
  · rintro (rfl|rfl)
    · rfl
    · exact rank_neg _

/-- Compare the ranks of the two candidate factors. -/
noncomputable def mask (n : (ZMod W)ˣ) : Finset (ZMod W)ˣ :=
  univ.filter fun x => rank x < rank (partner n x)

def Reflects (A : Finset (ZMod W)ˣ) : Prop := ∀ x, x∈A ↔ -x∈A

theorem mask_reflects (n : (ZMod W)ˣ) : Reflects (mask n) := by
  intro x
  simp [mask,partner,div_neg,rank_neg]

private theorem coincides (n x : (ZMod W)ˣ) :
    rank x = rank (partner n x) ↔ x^2=n ∨ x^2= -n := by
  rw [rank_eq]
  have eq : x = partner n x ↔ x^2=n := by
    simpa only [pow_two] using (product_iff_partner n x x).symm
  have neq : x = -partner n x ↔ x^2= -n := by
    rw [← neg_eq_iff_eq_neg, ← product_iff_partner, mul_neg, ← sq, neg_eq_iff_eq_neg]
  rw [eq,neq]

theorem mask_separates (n : (ZMod W)ˣ) (absent : ∀ x : (ZMod W)ˣ, x^2≠n ∧ x^2≠ -n) :
    Separates n (mask n) := by
  intro x y pair
  obtain rfl := (product_iff_partner ..).mp pair
  have different : rank x ≠ rank (partner n x) := fun eq =>
    ((coincides ..).mp eq).elim (absent x).1 (absent x).2
  simp only [mask,mem_filter,mem_univ,true_and,partner_partner,not_lt]
  omega

/-- Both obstructions are necessary even for arbitrary Boolean masks. -/
theorem exists_iff (n : (ZMod W)ˣ) :
    (∃ A, Reflects A ∧ Separates n A) ↔ ∀ x : (ZMod W)ˣ, x^2≠n ∧ x^2≠ -n := by
  constructor
  · rintro ⟨A,stable,exactly⟩ x
    constructor
    · intro h
      exact iff_not_self (exactly x x (by simpa [pow_two] using h))
    · intro h
      have flip := exactly x (-x) (by simp [mul_neg,← sq,h])
      exact iff_not_self ((stable x).symm.trans flip)
  · intro absent
    exact ⟨mask n,mask_reflects n,mask_separates n absent⟩

/-- Finite check used to certify a proposed period from the input alone. -/
def hasRoot (W value : ℕ) : Bool :=
  (List.range W).any fun i => (i*i)%W == value%W

theorem hasRoot_iff (value : ℕ) : hasRoot W value ↔ IsSquare (value : ZMod W) := by
  simp only [hasRoot,List.any_eq_true,List.mem_range,beq_iff_eq]
  constructor
  · rintro ⟨i,_,eq⟩
    exact ⟨i,by simpa using ((ZMod.natCast_eq_natCast_iff' (i*i) value W).mpr eq).symm⟩
  · rintro ⟨x,eq⟩
    exact ⟨x.val,x.val_lt,(ZMod.natCast_eq_natCast_iff' ..).mp (by simpa using eq.symm)⟩

omit [NeZero W] in
private theorem unit_square (u : (ZMod W)ˣ) : (∃ x : (ZMod W)ˣ, x^2=u) ↔ IsSquare (u:ZMod W) := by
  constructor
  · rintro ⟨x,h⟩
    exact ⟨x,by simpa [pow_two] using (congrArg Units.val h).symm⟩
  · rintro ⟨x,h⟩
    have unit := u.isUnit
    rw [h] at unit
    obtain ⟨v,rfl⟩ := isUnit_of_mul_isUnit_left unit
    exact ⟨v,Units.ext (by simpa [pow_two] using h.symm)⟩

def works (n W : ℕ) (reflect : Bool) : Bool :=
  !hasRoot W n && (!reflect || !hasRoot W (W-n%W))

theorem works_iff (n : ℕ) (cop : n.Coprime W) (reflect : Bool) :
    works n W reflect ↔ ∃ A, Separates (ZMod.unitOfCoprime n cop) A ∧
      (reflect = true → Reflects A) := by
  cases reflect with
  | false =>
    simp only [works,Bool.not_false,Bool.true_or,Bool.and_true,Bool.not_eq_true',
      ←Bool.not_eq_true,hasRoot_iff,Bool.false_eq_true,false_implies,and_true,
      LeastSeparatingModulus.has_selector_iff cop]
  | true =>
    have neg : ((W-n%W:ℕ):ZMod W) = -(n : ZMod W) := by
      rw [Nat.cast_sub (Nat.mod_lt _ (NeZero.pos W)).le]
      simp
    have equiv := exists_iff (ZMod.unitOfCoprime n cop)
    simp only [←not_or,←not_exists,exists_or,unit_square,Units.val_neg,
      ZMod.coe_unitOfCoprime] at equiv
    simp only [works,Bool.not_true,Bool.false_or,Bool.and_eq_true,Bool.not_eq_true',
      ←Bool.not_eq_true,hasRoot_iff,neg,true_implies]
    simpa only [and_comm,not_or] using equiv.symm

/-- Form a single product from any separating mask over an interval containing
each prime and no other multiple of either. -/
noncomputable def column (lo hi : ℕ) (A : Finset (ZMod W)ˣ) : ℕ :=
  FixedDivisorSignatures.column (Icc lo hi) fun a =>
    if h : a.Coprime W then decide (ZMod.unitOfCoprime a h ∈ A) else false

omit [NeZero W] in
theorem split {p q lo hi : ℕ} (pp : p.Prime) (qp : q.Prime) (cop : (p*q).Coprime W)
    (A : Finset (ZMod W)ˣ) (sep : Separates (ZMod.unitOfCoprime (p*q) cop) A)
    (pos : 0<lo) (hp : p∈Icc lo hi) (hq : q∈Icc lo hi) (sp : hi<2*p) (sq' : hi<2*q) :
    (column lo hi A).gcd (p*q) = p ∨ (column lo hi A).gcd (p*q) = q := by
  have bit {r : ℕ} (pr : r.Prime) (mem : r∈Icc lo hi) (small : hi<2*r) (co : r.Coprime W) :
      r ∣ column lo hi A ↔ ZMod.unitOfCoprime r co ∈ A := by
    have unique (a : ℕ) (ha : a∈Icc lo hi) (div : r ∣ a) : a=r := by
      obtain ⟨al,ah⟩ := mem_Icc.mp ha
      exact Nat.eq_of_dvd_of_lt_two_mul (by omega) div (by omega)
    unfold column
    rw [FixedDivisorSignatures.column_dvd pr mem unique,dif_pos co,decide_eq_true_eq]
  obtain ⟨pc,qc⟩ := Nat.coprime_mul_iff_left.mp cop
  have sep' := sep (ZMod.unitOfCoprime p pc) (ZMod.unitOfCoprime q qc)
    (Units.ext (by simp))
  apply FixedDivisorSignatures.separates pp qp
  rw [bit pp hp sp pc,bit qp hq sq' qc]
  intro same
  exact iff_not_self (same.symm.trans sep')

/-- Modulo 21 negation and separation coexist even though both constituent
prime wheels alone fail one of the two square tests. -/
theorem example_323 :
    let n := ZMod.unitOfCoprime 323 (by decide : Nat.Coprime 323 21)
    (mask n).image (fun x : (ZMod 21)ˣ => (x:ZMod 21).val) = {1,2,5,16,19,20} ∧
    Nat.gcd (column 16 31 (mask n)) 323=19 ∧
    (∀ x : (ZMod 21)ˣ, x^2≠n ∧ x^2≠ -n) ∧
    IsSquare ((-323:ℤ): ZMod 3) ∧ IsSquare (323 : ZMod 7) := by
  decide +kernel

end PrimeFactors.SymmetricDivisorSelector
