import PrimeFactors.ConditionalStride
import PrimeFactors.PrimePowerCount

namespace PrimeFactors

open scoped Classical

/-- At a prime power one of the two coordinates of a primitive pair is a unit. -/
def PrimitiveNormPair {R : Type*} [Monoid R] (v : R × R) : Prop :=
  IsUnit v.1 ∨ IsUnit v.2

/-- A primitive solution of x²=d y² necessarily has unit y. -/
theorem primitiveNorm_unit_snd {R : Type*} [CommMonoid R] {v : R × R} {d : R}
    (prim : PrimitiveNormPair v) (norm : v.1^2=d*v.2^2) : IsUnit v.2 := by
  rcases prim with hx | hy
  · have h := hx.pow 2
    rw [norm] at h
    exact (isUnit_pow_iff (by decide : 2 ≠ 0)).mp ((Commute.all _ _).isUnit_mul_iff.mp h).2
  · exact hy

/-- Multiplying a root by the unit second coordinate parametrizes precisely
the primitive solutions, for all targets including nonunits. -/
theorem primitiveNorm_solution_count {R : Type*} [CommMonoid R] (d : R) :
    Nat.card {v : R × R // PrimitiveNormPair v ∧ v.1^2=d*v.2^2} =
      Nat.card {z : R // z^2=d} * Nat.card Rˣ := by
  let f (a : {z : R // z^2=d} × Rˣ) : {v : R × R // PrimitiveNormPair v ∧ v.1^2=d*v.2^2} :=
    ⟨(a.1.val*(a.2 : R), a.2), Or.inr a.2.isUnit, by simp only [mul_pow, a.1.property]⟩
  have inj : Function.Injective f := by
    rintro ⟨x,u⟩ ⟨y,v⟩ h
    obtain rfl : u = v := Units.ext (congrArg (fun b => b.val.2) h)
    have a : (x : R)*u = (y : R)*u := congrArg (fun b => b.val.1) h
    obtain rfl : x = y := Subtype.ext (u.isUnit.mul_left_inj.mp a)
    rfl
  have surj : Function.Surjective f := by
    rintro ⟨⟨x,y⟩, prim, norm⟩
    obtain ⟨u,hu⟩ := primitiveNorm_unit_snd prim norm
    change (u : R) = y at hu
    change x^2 = d*y^2 at norm
    subst y
    let z : {z : R // z^2=d} := ⟨x*(↑u⁻¹ : R), by
      rw [mul_pow, norm, mul_assoc, ← mul_pow, Units.mul_inv, one_pow, mul_one]⟩
    exact ⟨(z,u), Subtype.ext (Prod.ext (by simp [f,z,mul_assoc]) rfl)⟩
  rw [← Nat.card_prod]
  exact Nat.card_congr (Equiv.ofBijective f ⟨inj,surj⟩).symm

private noncomputable def primitiveNorm_isUnitEquiv (R : Type*) [Monoid R] :
    {z : R // IsUnit z} ≃ Rˣ where
  toFun z := z.property.unit
  invFun u := ⟨u,u.isUnit⟩
  left_inv z := Subtype.ext z.property.unit_spec
  right_inv u := Units.ext u.isUnit.unit_spec

/-- Local nonsolutions to the primitivity condition have two nonunit coordinates. -/
theorem primitiveNorm_primitive_count {R : Type*} [Monoid R] [Fintype R] :
    Nat.card {v : R × R // PrimitiveNormPair v} =
      (Nat.card R)^2 - (Nat.card R - Nat.card Rˣ)^2 := by
  classical
  let E : {v : R × R // ¬ PrimitiveNormPair v} ≃
      {z : R // ¬ IsUnit z} × {z : R // ¬ IsUnit z} :=
    (Equiv.subtypeEquivRight (fun v => show (¬ PrimitiveNormPair v) ↔ _ from not_or)).trans
      (Equiv.subtypeProdEquivProd (p := fun x : R => ¬ IsUnit x) (q := fun y : R => ¬ IsUnit y))
  have bad := Nat.card_congr E
  rw [Nat.card_prod] at bad
  have non : Nat.card {z : R // ¬ IsUnit z} = Nat.card R - Nat.card Rˣ := by
    rw [← Nat.card_congr (primitiveNorm_isUnitEquiv R)]
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  rw [non, ← pow_two] at bad
  have total := Fintype.card_subtype_compl (PrimitiveNormPair (R := R))
  have le := Fintype.card_subtype_le (PrimitiveNormPair (R := R))
  simp only [Nat.card_eq_fintype_card, Fintype.card_prod, ← pow_two] at bad ⊢ total le
  omega

/-- Exact finite-level ratio with denominators cleared. The local probability
at level k+1 is the number of roots divided by p^k (p+1). -/
theorem primitiveNorm_primePower_ratio {p : ℕ} [Fact p.Prime] (k : ℕ)
    (d : ZMod (p^(k+1))) :
    Nat.card {v : ZMod (p^(k+1)) × ZMod (p^(k+1)) //
      PrimitiveNormPair v ∧ v.1^2=d*v.2^2} * (p^k*(p+1)) =
      Nat.card {v : ZMod (p^(k+1)) × ZMod (p^(k+1)) // PrimitiveNormPair v} *
        Nat.card {z : ZMod (p^(k+1)) // z^2=d} := by
  rw [primitiveNorm_solution_count, primitiveNorm_primitive_count]
  have units : Nat.card (ZMod (p^(k+1)))ˣ = p^k*(p-1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow_succ (Fact.out : p.Prime)]
  rw [units, Nat.card_eq_fintype_card (α := ZMod _), ZMod.card]
  have hp := (Fact.out : p.Prime).one_le
  have prime_eq : p-1+1=p := by omega
  have arithmetic (n a r : ℕ) :
      r*(n*a)*(n*((a+1)+1)) = ((n*(a+1))^2-(n*(a+1)-n*a)^2)*r := by
    have sub : n*(a+1)-n*a=n := by rw [Nat.mul_add,mul_one,Nat.add_sub_cancel_left]
    have sq : (n*(a+1))^2=n^2+(n*a)*(n*((a+1)+1)) := by ring
    rw [sub,sq,Nat.add_sub_cancel_left]
    ring
  simpa only [prime_eq, ← pow_succ] using arithmetic (p^k) (p-1)
    (Nat.card {z : ZMod (p^(k+1)) // z^2=d})

private theorem primitiveNorm_unit_of_digit {p k : ℕ} [Fact p.Prime]
    {x : ZMod (p^(k+1))} (h : firstPrimeDigit p k x ≠ 0) : IsUnit x := by
  obtain ⟨v,rfl⟩ := ZMod.natCast_zmod_surjective x
  rw [map_natCast] at h
  exact (ZMod.isUnit_iff_coprime _ _).mpr <| Nat.Coprime.pow_right _ <|
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr (fun hd => h <|
      (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr hd)).symm

/-- At every odd prime power a nonzero square on the first digit gives exactly
two roots. A nonsquare on the first digit gives none. -/
theorem primitiveNorm_odd_root_count {p : ℕ} [Fact p.Prime] (odd : p ≠ 2)
    (D : ℤ) (unit : (D : ZMod p) ≠ 0) (k : ℕ) :
    Nat.card {z : ZMod (p^(k+1)) // z^2 = (D : ZMod (p^(k+1)))} =
      if IsSquare (D : ZMod p) then 2 else 0 := by
  classical
  have transfer := isSquare_primePow_iff_of_unit odd D unit k
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  by_cases sq : IsSquare (D : ZMod p)
  · rw [if_pos sq]
    obtain ⟨s,hs⟩ := (isSquare_iff_exists_sq _).mp (transfer.mpr sq)
    have base : firstPrimeDigit p k s ≠ 0 := by
      intro hz
      apply unit
      have h := congrArg (firstPrimeDigit p k) hs
      simpa only [map_intCast,map_pow,hz,zero_pow (by decide : 2 ≠ 0)] using h
    have two : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
    have ne : s ≠ -s := by
      intro same
      have h := congrArg (firstPrimeDigit p k) same
      rw [map_neg] at h
      exact (mul_ne_zero two base) (by linear_combination h)
    have roots : Finset.univ.filter (fun z : ZMod (p^(k+1)) => z^2=(D : ZMod (p^(k+1)))) = {s,-s} := by
      ext x
      simp only [Finset.mem_filter,Finset.mem_univ,true_and, Finset.mem_insert,Finset.mem_singleton]
      constructor
      · intro h
        have product : (x-s)*(x+s)=0 := by linear_combination h + hs
        by_cases he : firstPrimeDigit p k (x-s)=0
        · have plus : firstPrimeDigit p k (x+s) ≠ 0 := by
            rw [map_sub,sub_eq_zero] at he
            rw [map_add,he,← two_mul]
            exact mul_ne_zero two base
          exact Or.inl (sub_eq_zero.mp ((primitiveNorm_unit_of_digit plus).mul_left_eq_zero.mp product))
        · exact Or.inr (eq_neg_of_add_eq_zero_left
            ((primitiveNorm_unit_of_digit he).mul_right_eq_zero.mp product))
      · rintro (rfl|rfl) <;> simp [hs]
    rw [roots, Finset.card_pair ne]
  · rw [if_neg sq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _
    exact fun hx => sq (transfer.mp ((isSquare_iff_exists_sq _).mpr ⟨x,hx.symm⟩))

/-- For exact valuation one a root exists modulo p only at zero, and no
root survives to level two or above. This also covers p=2. -/
theorem primitiveNorm_ramified_roots {p : ℕ} [Fact p.Prime] (D : ℤ)
    (divides : (p : ℤ) ∣ D) (once : ¬ (p : ℤ)^2 ∣ D) (k : ℕ) :
    Nat.card {z : ZMod p // z^2 = (D : ZMod p)} = 1 ∧
    Nat.card {z : ZMod (p^(k+2)) // z^2 = (D : ZMod (p^(k+2)))} = 0 := by
  classical
  constructor
  · rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr divides]
    simp only [sq_eq_zero_iff]
    rw [show Finset.univ.filter (fun x : ZMod p => x = 0) = {0} by ext x; simp]
    rfl
  · rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
      Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hx
    let reduction := ZMod.castHom (pow_dvd_pow p (by omega : 2 ≤ k+2)) (ZMod (p^2))
    have eq := congrArg reduction hx
    rw [map_pow,map_intCast] at eq
    exact once ((isSquare_prime_sq_iff_of_dvd D divides).mp
      ((isSquare_iff_exists_sq _).mpr ⟨_,eq.symm⟩))

/-- At two, an odd root known modulo 2^(k+3) can be corrected at the next
level without changing its parity. Start with the root 1 modulo 8. -/
theorem primitiveNorm_two_lift (D : ℤ) (base : 8 ∣ D-1) (k : ℕ) :
    ∃ s : ℤ, Odd s ∧ (2 : ℤ)^(k+3) ∣ D-s^2 := by
  induction k with
  | zero => exact ⟨1, ⟨0,by decide⟩, by simpa using base⟩
  | succ k ih =>
    obtain ⟨s,⟨u,su⟩,h,hh⟩ := ih
    refine ⟨s+2^(k+2)*h, ⟨u+2^(k+1)*h,?_⟩, -u*h-2^k*h^2, ?_⟩
    · rw [su]
      ring
    · rw [su] at hh ⊢
      linear_combination hh

/-- Translating by half the old modulus flips the next bit of the square.
This pairs off the four odd roots at every level from eight onwards. -/
theorem primitiveNorm_two_toggle (u : ℤ) (k : ℕ) :
    (2*u+1+2^(k+2))^2 = (2*u+1)^2 + 2^(k+3) + 2^(k+4)*(u+2^k) := by ring

/-- The odd split expectation through exponent m, including the exact
uncollected tail factor p^(-m). -/
theorem primitiveNorm_split_sum (p : ℚ) (hp : 1 < p) (m : ℕ) :
    (∑ j ∈ Finset.range m, 2 / (p^j*(p+1))) =
      (2*p/(p^2-1))*(1-(1/p)^m) := by
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p+1 ≠ 0 := by linarith
  have hp2 : p^2-1 ≠ 0 := by nlinarith [mul_self_pos.mpr (by linarith : p-1 ≠ 0)]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ,ih,pow_succ (1/p),one_div_pow]
    field_simp
    ring

end PrimeFactors
