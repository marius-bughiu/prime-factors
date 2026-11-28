import PrimeFactors.UniversalSumStride
import PrimeFactors.FractionalPrefixReadout

/-! Shortening a prefix by allowing several ordinary residue corrections trades
interval length against the size of the full correction list. The bounds here
charge an exhaustive list before information specific to the factor widths. -/
namespace PrimeFactors.FractionalCorrectionBudget

open Finset FractionalPrefixResidues

/-- Every possible ordinary correction consistent with the unit product. -/
noncomputable def menu {m : ℕ} [NeZero m] (u : (ZMod m)ˣ) : Finset ℕ :=
  univ.image (correction u)

theorem actual {p q m : ℕ} [NeZero m] (pc : p.Coprime m) (qc : q.Coprime m) :
    p%m+q%m ∈ menu (ZMod.unitOfCoprime p pc * ZMod.unitOfCoprime q qc) :=
  mem_image.mpr ⟨_, mem_univ _, FractionalPrefixReadout.correction_pair pc qc⟩

theorem represents {m : ℕ} [NeZero m] (u : (ZMod m)ˣ) (s : ZMod m) :
    AdmissibleSum (u : ZMod m) s ↔ ∃ a ∈ menu u, (a : ZMod m) = s := by
  constructor
  · rintro ⟨x,y,prod,rfl⟩
    obtain ⟨v,rfl⟩ := isUnit_of_mul_isUnit_left (prod ▸ u.isUnit : IsUnit (x*y))
    obtain ⟨w,rfl⟩ := isUnit_of_mul_isUnit_right (prod ▸ u.isUnit : IsUnit ((v:ZMod m)*y))
    have pair : v*w = u := Units.ext prod
    refine ⟨_, mem_image_of_mem (correction u) (mem_univ v), ?_⟩
    simp [correction, ←pair]
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨x,_,rfl⟩ := mem_image.mp ha
    refine ⟨x, ↑(u/x), ?_, ?_⟩
    · exact_mod_cast mul_div_cancel x u
    · simp [correction]

private noncomputable def differences {m : ℕ} (A : Finset ℕ) : Finset (ZMod m) :=
  insert 0 (A.offDiag.image fun xy => (xy.1 : ZMod m) - xy.2)

private theorem diff_mem {m : ℕ} (A : Finset ℕ) {x y : ℕ} (hx : x ∈ A) (hy : y ∈ A) :
    (x : ZMod m) - y ∈ differences A := by
  by_cases h : x = y
  · simp [h, differences]
  · exact mem_insert_of_mem (mem_image.mpr ⟨(x,y), mem_offDiag.mpr ⟨hx,hy,h⟩, rfl⟩)

/-- Every multiple of 20160 occurs as a difference modulo m. There are only
K(K−1) ordered unequal pairs in a list of K corrections, plus the zero difference. -/
theorem spacing_bound {m : ℕ} [NeZero m] (u : (ZMod m)ˣ) :
    m / m.gcd 20160 ≤ (menu u).card * (menu u).card - (menu u).card + 1 := by
  classical
  let H := AddSubgroup.zmultiples ((20160:ℕ) : ZMod m)
  have covers : (H : Set (ZMod m)).toFinset ⊆ differences (menu u) := by
    intro t ht
    obtain ⟨z,rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp (Set.mem_toFinset.mp ht : t ∈ H)
    obtain ⟨s, a, b⟩ := UniversalSumStride.all_moduli (u : ZMod m).val (20160*z) ⟨z,rfl⟩ m (NeZero.pos m)
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_mul, Int.cast_ofNat] at a b
    obtain ⟨x,hx,ex⟩ := (represents u s).mp a
    obtain ⟨y,hy,ey⟩ := (represents u _).mp b
    have h := diff_mem (m := m) (menu u) hy hx
    rw [ey, ex, add_sub_cancel_left] at h
    simpa only [zsmul_eq_mul, mul_comm, Nat.cast_ofNat] using h
  have cover := card_le_card covers
  rw [Set.toFinset_card, ← Nat.card_eq_fintype_card] at cover
  change Nat.card H ≤ _ at cover
  rw [show Nat.card H = m / m.gcd 20160 from
    (Nat.card_zmultiples _).trans (ZMod.addOrderOf_coe 20160 (NeZero.ne m))] at cover
  exact cover.trans ((card_insert_le ..).trans (Nat.add_le_add_right
    (card_image_le.trans_eq (offDiag_card (menu u))) 1))

/-- Moving the cutoff to floor(N/m) leaves a list with m ≤ 20160 K². -/
theorem modulus_bound {m : ℕ} [NeZero m] (u : (ZMod m)ˣ) :
    m ≤ 20160 * (menu u).card^2 := by
  have pos : 0 < (menu u).card := card_pos.mpr ⟨_, mem_image_of_mem (correction u) (mem_univ 1)⟩
  have h := spacing_bound u
  have positive := Nat.mul_pos pos pos
  have sq : m / m.gcd 20160 ≤ (menu u).card^2 := by rw [sq]; omega
  have g := Nat.le_of_dvd (by decide : 0 < 20160) (Nat.gcd_dvd_right m 20160)
  calc
    m = m.gcd 20160 * (m / m.gcd 20160) := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..) |>.symm
    _ ≤ _ := Nat.mul_le_mul g sq

theorem work_product {m : ℕ} [NeZero m] (n : ℕ) (u : (ZMod m)ˣ) :
    n < 20160 * (menu u).card^2 * (n/m+1) :=
  (Nat.lt_mul_div_succ n (NeZero.pos m)).trans_le (Nat.mul_le_mul_right _ (modulus_bound u))

set_option exponentiation.threshold 4096 in
/-- A direct prefix scan and an exhaustive full correction
list cannot both have at most 2^677 entries on a 2048-bit input. -/
theorem full_width {n m : ℕ} [NeZero m] (width : 2^2047 ≤ n) (u : (ZMod m)ˣ) :
    2^677 < n/m ∨ 2^677 < (menu u).card := by
  by_contra! small
  have b := Nat.mul_le_mul (Nat.mul_le_mul_left 20160 (Nat.pow_le_pow_left small.2 2))
    (Nat.add_le_add_right small.1 1)
  exact (not_le.mpr ((work_product n u).trans_le b))
    ((by norm_num : 20160*(2^677)^2*(2^677+1) ≤ (2^2047 : ℕ)).trans width)

/-- At a prime modulus the two roots of a fixed sum and product form one
unordered pair, so reduction loses no ordinary correction. -/
theorem prime_menu {m : ℕ} [Fact m.Prime] (u : (ZMod m)ˣ) :
    (menu u).card = (factorSumResidues m (u : ZMod m)).card := by
  have inj : Set.InjOn (fun a : ℕ => (a : ZMod m)) (menu u) := by
    intro a ha b hb eqn
    obtain ⟨x,_,rfl⟩ := mem_image.mp ha
    obtain ⟨y,_,rfl⟩ := mem_image.mp hb
    simp only [correction,Nat.cast_add,ZMod.natCast_zmod_val,Units.val_div_eq_div_val] at eqn
    have member : (y : ZMod m) ∈ (univ.erase (0 : ZMod m)).filter
        (fun z => z + (u : ZMod m)/z = (x : ZMod m) + (u : ZMod m)/x) :=
      mem_filter.mpr ⟨mem_erase.mpr ⟨y.ne_zero, mem_univ _⟩,eqn.symm⟩
    rw [factorSum_fiber m u.ne_zero x.ne_zero,mem_insert,mem_singleton] at member
    rcases member with h|h
    · rw [show y=x from Units.ext h]
    · have swap : y=u/x := Units.ext (by simpa only [Units.val_div_eq_div_val] using h)
      simp [swap,correction,add_comm]
  have image : (menu u).image (fun a : ℕ => (a : ZMod m)) = factorSumResidues m u := by
    ext z
    rw [mem_image, mem_factorSumResidues_iff m u.ne_zero, represents u z]
  rw [←image, card_image_of_injOn inj]

theorem prime_count {m : ℕ} [Fact m.Prime] (u : (ZMod m)ˣ) :
    2*(menu u).card = m-1+(squareRootsMod m u).card := by
  rw [prime_menu, two_mul_card_factorSumResidues m u u.ne_zero]

set_option exponentiation.threshold 4096 in
/-- Once the denominator reaches the square root, measuring the prefix can
sometimes be free. The complete unpruned residue menu alone is still large. -/
theorem near_root_menu {n m : ℕ} [NeZero m] (width : 2^2047 ≤ n) (above : n ≤ m^2)
    (u : (ZMod m)ˣ) : 2^504 < (menu u).card := by
  by_contra! small
  have modCap := (modulus_bound u).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left small 2))
  have nCap := above.trans (Nat.pow_le_pow_left modCap 2)
  exact (not_le.mpr (by norm_num : (20160*(2^504)^2)^2 < (2^2047 : ℕ))) (width.trans nCap)

set_option exponentiation.threshold 4096 in
/-- A prime denominator requires a full list of roughly half the modulus. -/
theorem prime_full_width {n m : ℕ} [hp : Fact m.Prime] (width : 2^2047 ≤ n) (u : (ZMod m)ˣ) :
    2^1022 < n/m ∨ 2^1022 < (menu u).card := by
  by_contra! small
  have h := prime_count u
  have modCap : m ≤ 2*2^1022+1 := by omega
  have nCap := (Nat.lt_mul_div_succ n hp.out.pos).trans_le
    (Nat.mul_le_mul modCap (Nat.add_le_add_right small.1 1))
  exact (not_le.mpr nCap)
    ((by norm_num : (2*2^1022+1)*(2^1022+1) ≤ (2^2047 : ℕ)).trans width)

end PrimeFactors.FractionalCorrectionBudget
