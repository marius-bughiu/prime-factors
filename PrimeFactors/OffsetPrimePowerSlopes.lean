import PrimeFactors.PrimePowerCount

namespace PrimeFactors.OffsetPrimePowerSlopes

open scoped Classical

/-- A primitive direction over Z/p^(k+1) has a unique representative (r,1)
or (1,p*b), with b in the indicated interval. -/
abbrev Direction (p k : ℕ) := ZMod (p^(k+1)) ⊕ Fin (p^k)

/-- Square test on the two normalized projective charts. -/
def accepts {p k : ℕ} (N T : ZMod (p^(k+1))) : Direction p k → Prop
  | .inl r => IsSquare ((r+2*T)^2-4*N)
  | .inr b => let s : ZMod (p^(k+1)) := (p : ZMod (p^(k+1)))*(b.val : ZMod (p^(k+1)))
              IsSquare ((1+2*T*s)^2-4*N*s^2)

variable {p : ℕ} [Fact p.Prime]

private theorem twoUnit (odd : p≠2) (k : ℕ) : IsUnit (2 : ZMod (p^(k+1))) := by
  exact (ZMod.isUnit_iff_coprime 2 _).mpr
    (((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (fun h => odd ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h))).symm.pow_right _)

/-- All p^k directions reducing to infinity modulo p pass the test.
Their discriminants are units congruent to one modulo p. -/
theorem exceptional_accepts (odd : p≠2) (k : ℕ) (N T : ZMod (p^(k+1))) (b : Fin (p^k)) :
    accepts N T (.inr b) := by
  obtain ⟨n,rfl⟩ := ZMod.natCast_zmod_surjective N
  obtain ⟨t,rfl⟩ := ZMod.natCast_zmod_surjective T
  let s : ℤ := (p:ℤ)*b.val
  let d : ℤ := (1+2*t*s)^2-4*n*s^2
  have one : (d : ZMod p)=1 := by simp [d,s]
  have lifted := (isSquare_primePow_iff_of_unit odd d (by simp [one]) k).mpr
    (by simp [one])
  simpa [accepts,d,s] using lifted

omit [Fact p.Prime] in
/-- Dividing a genuine weighted-square relation by a unit denominator selects
an accepted affine direction. The inverse is explicit over the local ring. -/
theorem affine_of_hit {k : ℕ} {N T j b d z : ZMod (p^(k+1))} (inv : b*z=1)
    (hit : (j+2*T*b)^2-4*N*b^2=d^2) : accepts N T (.inl (j*z)) := by
  have scale : j*z+2*T=(j+2*T*b)*z := by rw [add_mul,mul_assoc,inv,mul_one]
  have sq : b^2*z^2=1 := by rw [←mul_pow,inv,one_pow]
  refine ⟨d*z,?_⟩
  change (j*z+2*T)^2-4*N=d*z*(d*z)
  rw [scale,mul_pow]
  calc
    _ = ((j+2*T*b)^2-4*N*b^2)*z^2 := by rw [sub_mul,mul_assoc (4*N) (b^2) (z^2),sq,mul_one]
    _ = _ := by rw [hit]; ring

/-- When the normalized denominator reduces to zero at p there is an actual
index in the exceptional chart, even when that denominator is nonzero at p^(k+1). -/
theorem exceptional_of_zero_digit (odd : p≠2) (k : ℕ) (N T s : ZMod (p^(k+1)))
    (zero : firstPrimeDigit p k s = 0) :
    ∃ b : Fin (p^k), (p : ZMod (p^(k+1))) * (b.val : ZMod (p^(k+1))) = s ∧
      accepts N T (.inr b) := by
  have first : firstPrimeDigit p k s = (s.val : ZMod p) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val s,map_natCast]
  have hd := (ZMod.natCast_zmod_eq_zero_iff_dvd s.val p).mp (first.symm.trans zero)
  let b : Fin (p^k) := ⟨s.val/p,(Nat.div_lt_iff_lt_mul (Fact.out : p.Prime).pos).mpr
    (by simpa [pow_succ] using s.val_lt)⟩
  refine ⟨b,?_,exceptional_accepts odd k N T b⟩
  change (p : ZMod (p^(k+1))) * ((s.val/p : ℕ) : ZMod (p^(k+1))) = s
  rw [←Nat.cast_mul,Nat.mul_div_cancel' hd,ZMod.natCast_zmod_val]

noncomputable def affineEquiv (odd : p≠2) (k : ℕ) (N T : ZMod (p^(k+1))) :
    {r : ZMod (p^(k+1)) // accepts N T (.inl r)} ≃ {s // AdmissibleSum N s} where
  toFun r := ⟨r.val+2*T,(admissibleSum_iff_isSquare_of_two_unit (twoUnit odd k) ..).mpr r.property⟩
  invFun s := ⟨s.val-2*T,by
    simpa [accepts] using (admissibleSum_iff_isSquare_of_two_unit (twoUnit odd k) ..).mp s.property⟩
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

/-- At all precisions the square status of a unit discriminant is determined
by its first digit, pointwise on the affine chart. -/
theorem regular_affine_iff (odd : p≠2) (k : ℕ) (N T r : ZMod (p^(k+1)))
    (unit : firstPrimeDigit p k ((r+2*T)^2-4*N) ≠ 0) :
    accepts N T (.inl r) ↔ IsSquare (firstPrimeDigit p k ((r+2*T)^2-4*N)) := by
  let d := (r+2*T)^2-4*N
  have first : firstPrimeDigit p k d = ((d.val : ℤ) : ZMod p) := by
    rw [Int.cast_natCast]
    conv_lhs => rw [← ZMod.natCast_zmod_val d,map_natCast]
  have lift := isSquare_primePow_iff_of_unit odd (d.val : ℤ) (first ▸ unit) k
  rw [←first] at lift
  simp only [Int.cast_natCast,ZMod.natCast_zmod_val] at lift
  exact lift

/-- A regular admissible residue of the translated first coordinate selects
exactly p^k affine directions at level k+1. -/
theorem regular_lifts (odd : p≠2) (k : ℕ) (N T : ZMod (p^(k+1))) (s : ZMod p)
    (reg : s^2-4*firstPrimeDigit p k N≠0)
    (yes : AdmissibleSum (firstPrimeDigit p k N) s) :
    Nat.card {r : ZMod (p^(k+1)) // firstPrimeDigit p k (r+2*T)=s ∧ accepts N T (.inl r)} =
      p^k := by
  let e : {r : ZMod (p^(k+1)) // firstPrimeDigit p k (r+2*T)=s ∧ accepts N T (.inl r)} ≃
      {a : ZMod (p^(k+1)) // firstPrimeDigit p k a=s ∧ AdmissibleSum N a} :=
    { toFun := fun r => ⟨r.val+2*T,r.property.1,(affineEquiv odd k N T ⟨r.val,r.property.2⟩).property⟩
      invFun := fun a => ⟨a.val-2*T,by simpa using a.property.1,
        ((affineEquiv odd k N T).symm ⟨a.val,a.property.2⟩).property⟩
      left_inv := by intro r; ext; simp
      right_inv := by intro a; ext; simp }
  rw [Nat.card_congr e, card_admissible_regular_digit odd k N reg, dif_pos yes]

/-- Count first-level directions whose every lift survives, including infinity.
The finite coordinate is translated by 2T so its discriminant is s²−4N. -/
noncomputable def regularBaseCount (N : ZMod p) :=
  Nat.card {s : {a // AdmissibleSum N a} // s.val^2-4*N≠0} + 1

theorem regular_base_count (odd : p≠2) (N : ZMod p) (unit : N≠0) :
    regularBaseCount N = if IsSquare N then (p-1)/2 else (p+1)/2 := by
  classical
  let singular := fun s : {a // AdmissibleSum N a} => s.val^2-4*N=0
  let e : {s // singular s} ≃ {a : ZMod p // a^2-4*N=0} :=
    { toFun := fun s => ⟨s.val.val,s.property⟩
      invFun := fun a => ⟨⟨a.val,(admissibleSum_iff_isSquare odd _ _).mpr (by simp [a.property])⟩,a.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hs := (Nat.card_congr e).trans (base_singular_count odd unit)
  have size : regularBaseCount N = Nat.card {s // AdmissibleSum N s} - Nat.card {s // singular s} + 1 := by
    unfold regularBaseCount
    change Nat.card {s // ¬singular s} + 1 = _
    simp only [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  rw [size,hs,card_admissibleSum_eq p N unit]
  have hp := (Fact.out : p.Prime).two_le
  split_ifs with sq
  · rw [card_factorSumResidues_of_square p odd N unit sq]
    omega
  · rw [card_factorSumResidues_of_nonsquare p N unit sq]
    omega

/-- Total number of permitted directions at positive precision k+1.
Only the quadratic character of the product at p is needed. -/
def maskCount (p k : ℕ) (square : Bool) := primePowerSumCount p square (k+1) + p^k

theorem card_accepts (odd : p≠2) (k : ℕ) (N T : ZMod (p^(k+1)))
    (unitN : firstPrimeDigit p k N ≠ 0) :
    Nat.card {u // accepts N T u} =
      maskCount p k (decide (IsSquare (firstPrimeDigit p k N))) := by
  let equiv : {u // accepts N T u} ≃ ({r // accepts N T (.inl r)} ⊕ Fin (p^k)) :=
    { toFun := fun u => match u with
        | ⟨.inl r,hr⟩ => .inl ⟨r,hr⟩
        | ⟨.inr b,_⟩ => .inr b
      invFun := fun u => match u with
        | .inl r => ⟨.inl r.val,r.property⟩
        | .inr b => ⟨.inr b,exceptional_accepts odd k N T b⟩
      left_inv := by rintro ⟨r|b,h⟩ <;> rfl
      right_inv := by rintro (r|b) <;> rfl }
  rw [Nat.card_congr equiv,Nat.card_sum,Nat.card_congr (affineEquiv odd k N T),
    card_primePower_admissibleSum odd k N unitN]
  simp [maskCount]

theorem count_split (odd : p≠2) (k : ℕ) :
    2*(p+1)*maskCount p k true =
      (p^2+1)*p^k + 2*(if Even k then 2*p+1 else p+2) := by
  unfold maskCount
  nlinarith only [primePowerSumCount_closed_square odd k]

theorem count_nonsplit (odd : p≠2) (k : ℕ) :
    2*maskCount p k false = (p+1)*p^k := by
  have hp := (Fact.out : p.Prime).two_le
  obtain ⟨i,hi⟩ := (Fact.out : p.Prime).odd_of_ne_two odd
  have half : 2*((p-1)/2)+1=p := by omega
  simp only [maskCount,primePowerSumCount,Bool.false_eq_true,if_false]
  nlinarith only [congrArg (fun v : ℕ => p^k*v) half]

/-- Sharp uniform density floor, approached at p=3 for square products. -/
theorem density_floor (odd : p≠2) (k : ℕ) (square : Bool) :
    5*p^(k+1) ≤ 12*maskCount p k square := by
  have hp : 3≤p := by have := (Fact.out : p.Prime).two_le; omega
  rw [pow_succ]
  cases square with
  | false => nlinarith only [count_nonsplit odd k]
  | true =>
    have h : 5*p*(p+1) ≤ 6*(p^2+1) := by
      obtain ⟨a,ha⟩ := Nat.exists_eq_add_of_le hp
      rw [ha]
      nlinarith
    apply Nat.le_of_mul_le_mul_left (c:=p+1) _ (by omega)
    have hh : (p^2+1)*p^k ≤ 2*(p+1)*maskCount p k true := by rw [count_split odd k]; omega
    nlinarith only [Nat.mul_le_mul_right (p^k) h, hh]

/-- Each additional prime costs a factor close to p^e/2, even when powers of
arbitrary size are allowed. The retained p/(p+1) gives a product bound. -/
theorem prime_dependent_floor (odd : p≠2) (k : ℕ) (square : Bool) :
    (p^2+1)*p^k ≤ 2*(p+1)*maskCount p k square := by
  cases square with
  | true => rw [count_split odd k]; omega
  | false =>
    have h := congrArg (fun v : ℕ => (p+1)*v) (count_nonsplit odd k)
    nlinarith only [h]

theorem modulus_floor (odd : p≠2) (k : ℕ) (square : Bool) :
    p^(k+1)*(p-1) ≤ 2*p*maskCount p k square := by
  have hp : 1≤p := (Fact.out : p.Prime).one_lt.le
  have eq : p-1+1=p := Nat.sub_add_cancel hp
  rw [pow_succ]
  apply Nat.le_of_mul_le_mul_left (c:=p+1) _ (by omega)
  calc
    _ = ((p+1)*(p-1))*(p*p^k) := by ring
    _ ≤ (p^2+1)*(p*p^k) := by
      apply Nat.mul_le_mul_right
      nlinarith only [congrArg (fun v : ℕ => (p+1)*v) eq]
    _ ≤ _ := by
      simpa only [mul_assoc,mul_comm,mul_left_comm] using
        Nat.mul_le_mul_left p (prime_dependent_floor odd k square)

theorem base_floor (_odd : p≠2) (k : ℕ) (square : Bool) :
    (p+1)/2 ≤ maskCount p k square := by
  have hp := (Fact.out : p.Prime).two_le
  cases k with
  | zero =>
    cases square <;> simp [maskCount,primePowerSumCount,collidingDigitCount] <;> omega
  | succ k =>
    have pos := Nat.pow_pos (Fact.out : p.Prime).pos (n:=k)
    have bound : p ≤ p^(k+1) := by
      rw [pow_succ]
      simpa using Nat.mul_le_mul_right p pos
    unfold maskCount
    omega

/-- First-digit prices remain lower bounds when a prime is raised to any power. -/
theorem first_mask_min (odd : p≠2) (k : ℕ) (square : Bool) :
    maskCount p 0 square ≤ maskCount p k square := by
  have hp : 3≤p := by have := (Fact.out : p.Prime).two_le; omega
  cases k with
  | zero => rfl
  | succ k =>
    have h : maskCount p 0 square ≤ p := by
      cases square <;> simp [maskCount,primePowerSumCount,collidingDigitCount] <;> omega
    have pos := Nat.pow_pos (Fact.out : p.Prime).pos (n:=k)
    have bound : p ≤ p^(k+1) := by
      rw [pow_succ]
      simpa using Nat.mul_le_mul_right p pos
    exact h.trans (bound.trans (Nat.le_add_left ..))

/-- A fixed repeated split prime costs at least its price at exponent two. -/
theorem second_split_min (odd : p≠2) (k : ℕ) :
    maskCount p 1 true ≤ maskCount p (k+1) true := by
  have hp : 3≤p := by have := (Fact.out : p.Prime).two_le; omega
  cases k with
  | zero => rfl
  | succ k =>
    have h : maskCount p 1 true ≤ p^2 := by
      have half : (p-3)/2 + 1 ≤ p-1 := by omega
      have eq := Nat.sub_add_cancel (show 1≤p by omega)
      simp [maskCount,primePowerSumCount,collidingDigitCount,primePowerSquareCount]
      nlinarith only [Nat.mul_le_mul_right p half, congrArg (fun v : ℕ => p*v) eq,hp]
    have pos := Nat.pow_pos (Fact.out : p.Prime).pos (n:=k)
    have bound : p^2 ≤ p^(k+1+1) := by
      rw [show k+1+1=k+2 by omega,pow_add]
      simpa using Nat.mul_le_mul_right (p^2) pos
    exact h.trans (bound.trans (Nat.le_add_left ..))

theorem ternary : (List.range 6).map (fun k => maskCount 3 k true) = [3,5,13,35,103,305] := by
  decide

end PrimeFactors.OffsetPrimePowerSlopes
