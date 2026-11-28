import PrimeFactors.FractionalTwoCorrectionLimit

/-! Select the shortest interval among all denominators with at most two
universal corrections. The finite selection depends only on the given product.
A measured count and at most two discriminant tests complete this readout. -/
namespace PrimeFactors.FractionalPrefixPlanner

open Finset FractionalCorrectionBudget FractionalPrefixResidues

/-- A finite table entry using integer representatives only. -/
noncomputable def ordinary (n m : ℕ) : Finset ℕ :=
  (((range m) ×ˢ (range m)).filter (fun z => (z.1*z.2)%m = n%m)).image
    (fun z => z.1+z.2)

theorem ordinary_eq {n m : ℕ} [NeZero m] (cop : n.Coprime m) :
    ordinary n m = menu (ZMod.unitOfCoprime n cop) := by
  let u := ZMod.unitOfCoprime n cop
  ext r
  constructor
  · rintro hr
    obtain ⟨⟨a,b⟩, hab, rfl⟩ := mem_image.mp hr
    obtain ⟨bounds,residue⟩ := mem_filter.mp hab
    obtain ⟨ha,hb⟩ := mem_product.mp bounds
    have prod : (a:ZMod m)*b = (u : ZMod m) := by
      rw [←Nat.cast_mul, ZMod.coe_unitOfCoprime]
      exact (ZMod.natCast_eq_natCast_iff ..).mpr residue
    have unit : IsUnit ((a:ZMod m)*b) := prod ▸ u.isUnit
    obtain ⟨x,hx⟩ := isUnit_of_mul_isUnit_left unit
    obtain ⟨y,hy⟩ := isUnit_of_mul_isUnit_right unit
    have xy : x*y = u := Units.ext (by simpa only [Units.val_mul,hx,hy] using prod)
    refine mem_image.mpr ⟨x,mem_univ _,?_⟩
    change correction u x = a+b
    rw [←xy,correction,mul_div_cancel_left,hx,hy,
      ZMod.val_natCast_of_lt (mem_range.mp ha),ZMod.val_natCast_of_lt (mem_range.mp hb)]
  · intro hr
    obtain ⟨x,_,rfl⟩ := mem_image.mp hr
    let y := u/x
    let a := (x : ZMod m).val
    let b := (y : ZMod m).val
    have prod : (a*b : ℕ) ≡ n [MOD m] := by
      apply (ZMod.natCast_eq_natCast_iff ..).mp
      simp only [Nat.cast_mul, a, b, ZMod.natCast_zmod_val]
      change ((x*y : (ZMod m)ˣ) : ZMod m) = _
      rw [show x*y = u from mul_div_cancel _ _]
      rfl
    exact mem_image.mpr ⟨(a,b), mem_filter.mpr
      ⟨mem_product.mpr ⟨mem_range.mpr (ZMod.val_lt _),mem_range.mpr (ZMod.val_lt _)⟩,prod⟩,rfl⟩

/-- Enumerate at most 119 denominators. The proof of the 120 limit makes
this bounded table exhaustive at every input size. -/
noncomputable def candidates (n : ℕ) : Finset ℕ :=
  (Icc 2 120).filter fun m => n.Coprime m ∧ (ordinary n m).card ≤ 2

noncomputable def denominator (n : ℕ) : ℕ := (candidates n).sup id

theorem eligible_iff {n m : ℕ} (hm : 2 ≤ m) (cop : n.Coprime m) :
    m ∈ candidates n ↔ (ordinary n m).card ≤ 2 := by
  letI : NeZero m := ⟨by omega⟩
  simp only [candidates,mem_filter,mem_Icc]
  refine ⟨fun h => h.2.2,fun h => ⟨⟨hm,?_⟩,cop,h⟩⟩
  exact FractionalTwoCorrectionLimit.at_most_120 (ZMod.unitOfCoprime n cop) (ordinary_eq cop ▸ h)

private theorem contains_two {n : ℕ} (odd : Odd n) : 2 ∈ candidates n := by
  have cop := Nat.coprime_two_right.mpr odd
  apply (eligible_iff (by decide) cop).mpr
  have same : ordinary n 2 = ordinary 1 2 := by
    simp only [ordinary,Nat.odd_iff.mp odd,Nat.reduceMod]
  rw [same]
  decide +kernel

/-- Every odd input has a qualifying denominator. No qualifying denominator,
even outside the enumerated range, is larger than the selected one. -/
theorem greatest {n : ℕ} (odd : Odd n) :
    denominator n ∈ candidates n ∧
    ∀ m, 2 ≤ m → n.Coprime m → (ordinary n m).card ≤ 2 → m ≤ denominator n := by
  have nonempty : (candidates n).Nonempty := ⟨2, contains_two odd⟩
  constructor
  · simpa only [denominator, Set.image_id] using
      (sup_mem_of_nonempty (f := id) nonempty)
  · intro m hm cop size
    exact le_sup (f := id) ((eligible_iff hm cop).mpr size)

/-- The two-answer interval is never longer than the best one-answer
interval. This compares lengths and does not count the work of obtaining C. -/
theorem no_longer {n : ℕ} (odd : Odd n) :
    n / denominator n ≤ n / Nat.gcd 24 (n+1) := by
  let g := Nat.gcd 24 (n+1)
  obtain ⟨hg,_,dn,_⟩ := FractionalPrefixReadout.greatest odd
  have hm : 2 ≤ g := hg
  letI : NeZero g := ⟨by omega⟩
  have cop : n.Coprime g :=
    (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)).of_dvd_right dn
  obtain ⟨c,constant⟩ := (FractionalPrefixReadout.constant_iff_dvd_gcd hm cop).mpr (dvd_refl g)
  have one : (ordinary n g).card ≤ 1 := by
    rw [ordinary_eq cop]
    apply card_le_one.mpr
    intro x hx y hy
    obtain ⟨a,_,rfl⟩ := mem_image.mp hx
    obtain ⟨b,_,rfl⟩ := mem_image.mp hy
    exact (constant a).trans (constant b).symm
  exact Nat.div_le_div_left ((greatest odd).2 g hm cop (one.trans (by decide))) (by omega)

/-- The two corrections are determined by the product residue itself. -/
noncomputable def options (n m : ℕ) : Finset ℕ := {1+n%m,2*m-(1+n%m)}

private theorem endpoints {n m : ℕ} [NeZero m] (hm : 2 ≤ m) (cop : n.Coprime m) :
    let u := ZMod.unitOfCoprime n cop
    correction u 1 = 1+n%m ∧ correction u (-1) = 2*m-(1+n%m) := by
  letI : Fact (1 < m) := ⟨hm⟩
  let u := ZMod.unitOfCoprime n cop
  have first : correction u 1 = 1+n%m := by
    rw [correction,div_one,Units.val_one,ZMod.val_one, ZMod.coe_unitOfCoprime,ZMod.val_natCast]
  have ref := reflection hm u 1
  change correction u 1 = _ ∧ correction u (-1) = _
  exact ⟨first,by omega⟩

theorem exact_options {n m : ℕ} (hm : 2 ≤ m) (cop : n.Coprime m) (small : (ordinary n m).card ≤ 2) :
    ordinary n m = options n m := by
  letI : NeZero m := ⟨by omega⟩
  let u := ZMod.unitOfCoprime n cop
  let a := correction u 1
  let b := correction u (-1)
  have in_menu (x : (ZMod m)ˣ) : correction u x ∈ menu u := mem_image_of_mem _ (mem_univ x)
  have h := endpoints hm cop
  change a = _ ∧ b = _ at h
  rw [ordinary_eq cop] at small ⊢
  change (menu u).card ≤ 2 at small
  rw [options,←h.2,←h.1]
  ext z
  change z ∈ menu u ↔ z ∈ ({a,b} : Finset ℕ)
  rw [mem_insert,mem_singleton]
  constructor
  · intro hz
    by_contra! miss
    have triple {v : ℕ} (hv : v ∈ menu u) (av : a ≠ v) (vz : v ≠ z) : False :=
      (not_lt.mpr small) (two_lt_card_iff.mpr ⟨a,v,z,in_menu 1,hv,hz,av,miss.1.symm,vz⟩)
    by_cases eqn : a=b
    · obtain ⟨x,_,hx⟩ := mem_image.mp hz
      have sum := reflection hm u x
      have center : a+b=2*m := reflection hm u 1
      exact triple (in_menu (-x)) (by omega) (by omega)
    · exact triple (in_menu (-1)) eqn miss.2.symm
  · rintro (rfl|rfl)
    · exact in_menu 1
    · exact in_menu (-1)

/-- Starting with only N, choose the denominator, then use the count C
to reduce the true sum to mC plus one of two specified integer corrections. -/
theorem readout {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (diff : p ≠ q) (odd : Odd (p*q)) :
    let m := denominator (p*q)
    ∃ r ∈ options (p*q) m, p+q=m*FractionalNonunitPrefix.prefixCount (p*q) m+r := by
  let n := p*q
  let m := denominator n
  have selected := mem_filter.mp (greatest odd).1
  obtain ⟨lo,_⟩ := mem_Icc.mp selected.1
  obtain ⟨cop,small⟩ := selected.2
  have hm : 2 ≤ m := lo
  letI : NeZero m := ⟨by omega⟩
  have pc : p.Coprime m := cop.of_dvd_left (dvd_mul_right p q)
  have qc : q.Coprime m := cop.of_dvd_left (dvd_mul_left q p)
  have actual := FractionalCorrectionBudget.actual pc qc
  have units : ZMod.unitOfCoprime p pc * ZMod.unitOfCoprime q qc =
      ZMod.unitOfCoprime n cop := by apply Units.ext; simp [n]
  rw [units,←ordinary_eq cop,exact_options hm cop small] at actual
  exact ⟨p%m+q%m, actual, (FractionalNonunitPrefix.scaled hp hq diff hm).symm⟩

end PrimeFactors.FractionalPrefixPlanner
