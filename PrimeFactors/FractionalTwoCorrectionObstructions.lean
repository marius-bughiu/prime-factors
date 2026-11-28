import PrimeFactors.FractionalCorrectionBudget

/-! Four local unit/inverse pairs suffice to exhibit three distinct sums at each
of six obstructing moduli. The 120 example concerns ordinary integer sums. -/
namespace PrimeFactors.FractionalTwoCorrectionObstructions

open Finset FractionalCorrectionBudget FractionalPrefixResidues FractionalNonunitPrefix

private def witnesses : ℕ → Finset (ℕ × ℕ)
  | 7 => {(1,1), (2,4), (3,5), (4,2)}
  | 27 => {(1,1), (2,14), (4,7), (5,11)}
  | 64 => {(1,1), (3,43), (5,13), (9,57)}
  | 45 => {(1,1), (2,23), (4,34), (7,13)}
  | 80 => {(1,1), (3,27), (7,23), (9,9)}
  | 144 => {(1,1), (11,131), (5,29), (17,17)}
  | _ => ∅

private def traces (m : ℕ) (t : ZMod m) :=
  (witnesses m).image fun z => (z.1 : ZMod m) + t*z.2

private theorem certificate {m : ℕ} (hm : m ∈ ([7,27,64,45,80,144] : List ℕ)) :
    (∀ z ∈ witnesses m, (z.1 : ZMod m)*z.2=1) ∧
      ∀ t : Fin m, t.val.Coprime m → 2 < (traces m t.val).card := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- Every unit product modulo one of the six listed moduli has three distinct
admissible modular sums. Only four candidate factor pairs are used per product. -/
theorem three {m : ℕ} [NeZero m] (hm : m ∈ ([7,27,64,45,80,144] : List ℕ))
    (u : (ZMod m)ˣ) : ∃ a b c : ZMod m, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      AdmissibleSum (u : ZMod m) a ∧ AdmissibleSum (u : ZMod m) b ∧ AdmissibleSum (u : ZMod m) c := by
  obtain ⟨inv, spread⟩ := certificate hm
  have enough := spread ⟨(u : ZMod m).val, ZMod.val_lt _⟩ (ZMod.val_coe_unit_coprime u)
  simp only [ZMod.natCast_zmod_val] at enough
  obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := two_lt_card_iff.mp enough
  have adm (s : ZMod m) (hs : s ∈ traces m u) : AdmissibleSum (u : ZMod m) s := by
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hs
    exact ⟨z.1, (u : ZMod m)*z.2, by rw [mul_left_comm, inv z hz, mul_one], rfl⟩
  exact ⟨a,b,c,ab,ac,bc,adm a ha,adm b hb,adm c hc⟩

private theorem mem_menu_iff {m c : ℕ} [NeZero m] (u : (ZMod m)ˣ) :
    c ∈ menu u ↔ ∃ x, correction u x = c := by simp [menu]

/-- The extremal ordinary menu has both values, witnessed by (1,107) and (13,119). -/
theorem menu_120 :
    menu (ZMod.unitOfCoprime 107 (by decide : Nat.Coprime 107 120)) = {108,132} := by
  let u := ZMod.unitOfCoprime 107 (by decide : Nat.Coprime 107 120)
  change menu u = _
  have possible : ∀ x y : ZMod 120, x*y=107 → x.val+y.val ∈ ({108,132} : Finset ℕ) := by
    decide +kernel
  ext c
  rw [mem_menu_iff]
  constructor
  · rintro ⟨x,rfl⟩
    apply possible (x : ZMod 120) ((u/x : (ZMod 120)ˣ) : ZMod 120)
    change ((x * (u/x) : (ZMod 120)ˣ) : ZMod 120)=107
    rw [mul_div_cancel]
    exact ZMod.coe_unitOfCoprime ..
  · intro h
    simp only [mem_insert, mem_singleton] at h
    rcases h with rfl | rfl
    · exact ⟨1,by decide +kernel⟩
    · let x := ZMod.unitOfCoprime 13 (by decide : Nat.Coprime 13 120)
      let y := ZMod.unitOfCoprime 119 (by decide : Nat.Coprime 119 120)
      have pair : x*y = u := by
        apply Units.ext
        change (13 : ZMod 120)*119 = 107
        decide +kernel
      refine ⟨x, ?_⟩
      rw [← pair, correction, mul_div_cancel_left]
      decide +kernel

private theorem ordinary_mem {m : ℕ} [NeZero m] (u : (ZMod m)ˣ) {a b : ZMod m}
    (prod : a*b=u) : a.val+b.val ∈ menu u := by
  obtain ⟨x,rfl⟩ := isUnit_of_mul_isUnit_left (prod ▸ u.isUnit : IsUnit (a*b))
  obtain ⟨y,rfl⟩ := isUnit_of_mul_isUnit_right (prod ▸ u.isUnit : IsUnit ((x : ZMod m)*b))
  have xy : x*y=u := Units.ext prod
  exact (mem_menu_iff u).mpr ⟨x, by rw [← xy, correction, mul_div_cancel_left]⟩

private def probes120 : Finset (ℕ × ℕ) := {(1,1), (107,83), (23,47), (19,19)}
private def ordinaryTests {m : ℕ} (P : Finset (ℕ × ℕ)) (t : ZMod m) :=
  P.image fun z => (z.1 : ZMod m).val + (t*z.2).val

private theorem probes_subset {m : ℕ} [NeZero m] (u : (ZMod m)ˣ) (P : Finset (ℕ × ℕ))
    (inverses : ∀ z ∈ P, (z.1 : ZMod m)*z.2=1) : ordinaryTests P (u : ZMod m) ⊆ menu u := by
  intro c hc
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hc
  exact ordinary_mem u (a := z.1) (b := (u : ZMod m)*z.2)
    (by rw [mul_left_comm, inverses z hz, mul_one])

/-- Only the product class 107 attains a two-entry menu at modulus 120.
Four fixed factor/inverse probes rule out all other unit classes. -/
theorem at_most_two_120 (u : (ZMod 120)ˣ) : (menu u).card ≤ 2 ↔ (u : ZMod 120) = 107 := by
  constructor
  · intro small
    by_contra other
    have spread : ∀ t : Fin 120, t.val.Coprime 120 → t.val ≠ 107 → 2 < (ordinaryTests probes120 (t.val : ZMod 120)).card := by
      decide +kernel
    have many := spread ⟨(u : ZMod 120).val, ZMod.val_lt _⟩ (ZMod.val_coe_unit_coprime u)
      (fun h => other (by
        change (u : ZMod 120).val = 107 at h
        rw [← ZMod.natCast_zmod_val (u : ZMod 120), h]
        rfl))
    simp only [ZMod.natCast_zmod_val] at many
    have inverses : ∀ z ∈ probes120, (z.1 : ZMod 120)*z.2=1 := by decide +kernel
    have included := probes_subset u probes120 inverses
    exact (not_lt_of_ge small) (many.trans_le (card_le_card included))
  · intro cls
    have eqn : u = ZMod.unitOfCoprime 107 (by decide : Nat.Coprime 107 120) := Units.ext cls
    rw [eqn, menu_120]
    decide

/-- Two balanced products have the same product residue and count at m=120,
and realize the two different corrections. -/
theorem both_readings :
    (101:ℕ).Prime ∧ (127:ℕ).Prime ∧ (113:ℕ).Prime ∧ (139:ℕ).Prime ∧
    101 < 127 ∧ 127 < 2*101 ∧ 113 < 139 ∧ 139 < 2*113 ∧
    (101*127)%120=107 ∧ (113*139)%120=107 ∧
    prefixCount (101*127) 120=1 ∧ prefixCount (113*139) 120=1 ∧
    101+127=120+108 ∧ 113+139=120+132 := by
  have a := quotient_sum (p:=101) (q:=127) (m:=120) (by decide) (by decide) (by decide) (by decide)
  have b := quotient_sum (p:=113) (q:=139) (m:=120) (by decide) (by decide) (by decide) (by decide)
  rw [a,b]
  decide +kernel

end PrimeFactors.FractionalTwoCorrectionObstructions
