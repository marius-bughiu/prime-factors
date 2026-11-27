import PrimeFactors.PersistentLocalSurvivors

/-! Counts for simultaneous residue tests in an interval, including when
each test has some classes whose verdict is already settled at all depths. -/
namespace PrimeFactors.FiniteWheelPrecision

variable {ι : Type*} [Fintype ι]

/-- Each row combination occurs at most once per period in the interval. -/
theorem upper (m : ι → ℕ) (positive : ∀ i, 0<m i)
    (cop : Pairwise (fun i j => (m i).Coprime (m j))) (A : (i : ι) → Finset (ZMod (m i)))
    (start W : ℕ) : Nat.card {k : Fin W // ∀ i, ((start+k.val : ℕ) : ZMod (m i)) ∈ A i} ≤
      (W/(∏ i, m i)+1)*(∏ i, (A i).card) := by
  classical
  let M := ∏ i, m i
  have pos : 0<M := Finset.prod_pos (fun i _ => positive i)
  letI : NeZero M := ⟨pos.ne'⟩
  let e := ZMod.prodEquivPi m cop
  let S := {k : Fin W // ∀ i, ((start+k.val : ℕ) : ZMod (m i)) ∈ A i}
  let encode (x : S) : Fin (W/M+1) × ((i : ι) → A i) :=
    (⟨x.val.val/M,Nat.lt_succ_of_le (Nat.div_le_div_right x.val.isLt.le)⟩,fun i => ⟨_,x.property i⟩)
  have inject : Function.Injective encode := by
    intro x y h
    have div : x.val.val/M = y.val.val/M := congrArg (fun z => z.1.val) h
    have all : ((start+x.val.val : ℕ) : ZMod M) = ((start+y.val.val : ℕ) : ZMod M) := by
      apply e.injective
      funext i
      simpa only [map_natCast,Pi.natCast_apply] using
        (congrArg (fun z => (z.2 i).val) h : ((start+x.val.val : ℕ) : ZMod (m i)) = _)
    simp only [Nat.cast_add,add_right_inj] at all
    have rem := congrArg ZMod.val all
    simp only [ZMod.val_natCast] at rem
    apply Subtype.ext
    apply Fin.ext
    simpa only [Nat.div_add_mod] using congrArg₂ (fun a b : ℕ => M*a+b) div rem
  have count := Nat.card_le_card_of_injective encode inject
  have sizes (i : ι) : Nat.card (A i) = (A i).card := by simp [Nat.card_eq_fintype_card]
  simpa only [Nat.card_prod,Nat.card_pi,sizes,Nat.card_eq_fintype_card (α:=Fin _),
    Fintype.card_fin] using count

/-- A subset of local classes can certify acceptance at every precision,
while a larger subset contains every possible passing position. -/
theorem sandwich (m : ι → ℕ) (positive : ∀ i, 0<m i)
    (cop : Pairwise (fun i j => (m i).Coprime (m j)))
    (settled possible : (i : ι) → Finset (ZMod (m i))) (start W : ℕ) (P : Fin W → Prop)
    (keep : ∀ k : Fin W, (∀ i, ((start+k.val : ℕ) : ZMod (m i)) ∈ settled i) → P k)
    (necessary : ∀ k : Fin W, P k → ∀ i, ((start+k.val : ℕ) : ZMod (m i)) ∈ possible i) :
    W/(∏ i, m i)*(∏ i, (settled i).card) ≤ Nat.card {k // P k} ∧
      Nat.card {k // P k} ≤ (W/(∏ i, m i)+1)*(∏ i, (possible i).card) := by
  have include_card {A B : Fin W → Prop} (inc : ∀ k, A k → B k) :
      Nat.card {k // A k} ≤ Nat.card {k // B k} := by
    let f (x : {k // A k}) : {k // B k} := ⟨x.val,inc _ x.property⟩
    exact Nat.card_le_card_of_injective f
      (fun _ _ h => Subtype.ext (congrArg (fun k : {k // B k} => k.val) h))
  exact ⟨(PersistentLocalSurvivors.full_period_product m positive cop settled start W).trans
    (include_card keep), (include_card necessary).trans (upper m positive cop possible start W)⟩

end PrimeFactors.FiniteWheelPrecision
