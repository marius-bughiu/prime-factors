import PrimeFactors.LocalMidpointLanes

/-! The primitive local points of the quartic a⁴+4b⁴=N d⁴ at two.
For odd N, modulus sixteen completely decides solubility at all depths. -/
namespace PrimeFactors.QuarticTwoLocalPoints

def PrimitivePoint (N k : ℕ) : Prop :=
  ∃ a b d : ℕ, a.Coprime b ∧ Odd d ∧ a^4+4*b^4 ≡ N*d^4 [MOD 2^k]

/-- An integer equal to one modulo sixteen has a fourth root of the form
1+4v modulo every higher power. The correction to v at each step is
a multiple of the current power of two. -/
theorem lift_sixteen {D : ℤ} (base : (16:ℤ)∣D-1) (k : ℕ) :
    ∃ v : ℤ, (2:ℤ)^(k+4)∣D-(1+4*v)^4 := by
  induction k with
  | zero => exact ⟨0,by simpa using base⟩
  | succ k ih =>
    obtain ⟨v,z,hz⟩ := ih
    refine ⟨v+2^k*z,
      -z*(6*v+24*v^2+32*v^3)-3*2^k*z^2*(1+4*v)^2
        -8*(2^k)^2*z^3*(1+4*v)-8*(2^k)^3*z^4,?_⟩
    rw [show k+1+4=k+5 by omega,pow_add]
    rw [pow_add] at hz
    linear_combination hz

private theorem abs_fourth (a : ℤ) : |a|^4=a^4 := by
  rw [show 4=2*2 by decide,pow_mul,pow_mul,sq_abs]

/-- Taking an absolute value gives an odd natural root, including at depth zero. -/
theorem fourth_root {D : ℕ} (base : D%16=1) (k : ℕ) :
    ∃ a : ℕ, Odd a ∧ a^4 ≡ D [MOD 2^k] := by
  have hm : 1 ≡ D [MOD 16] := base.symm
  have hd := Int.modEq_iff_dvd.mp (Int.natCast_modEq_iff.mpr hm)
  obtain ⟨v,hv⟩ := lift_sixteen (D:=D) hd k
  let z : ℤ := 1+4*v
  have odd : Odd z := ⟨2*v,by dsimp [z]; ring⟩
  refine ⟨z.natAbs,odd.natAbs,Int.natCast_modEq_iff.mp (Int.modEq_iff_dvd.mpr ?_)⟩
  push_cast
  rw [abs_fourth]
  exact (pow_dvd_pow (2:ℤ) (show k≤k+4 by omega)).trans hv

/-- With a unit denominator equal to one, the two numerator coordinates
can be chosen coprime as natural numbers. -/
theorem affine_point {N : ℕ} (good : N%16=1 ∨ N%16=5) (k : ℕ) :
    ∃ a b : ℕ, Odd a ∧ a.Coprime b ∧ a^4+4*b^4 ≡ N [MOD 2^k] := by
  rcases good with one | five
  · obtain ⟨a,odd,hit⟩ := fourth_root one k
    have zero : 2^k ≡ 0 [MOD 2^k] := Nat.modEq_zero_iff_dvd.mpr (dvd_refl _)
    refine ⟨a,2^k,odd,odd.coprime_two_right.pow_right k,?_⟩
    simpa using hit.add ((zero.pow 4).mul_left 4)
  · have lower : 4≤N := by omega
    obtain ⟨a,odd,hit⟩ := fourth_root (D:=N-4) (by omega) k
    exact ⟨a,1,odd,Nat.coprime_one_right _,by
      simpa [Nat.sub_add_cancel lower] using hit.add_right 4⟩

private theorem fourth_mod (a : ℕ) : a^4%16=a%2 := by
  have table : ∀ z : Fin 16, z.val^4%16=z.val%2 := by decide +kernel
  have small := table ⟨a%16,Nat.mod_lt _ (by decide)⟩
  calc
    a^4%16 = (a%16)^4%16 := ((Nat.mod_modEq a 16).pow 4).symm
    _ = a%16%2 := small
    _ = a%2 := Nat.mod_mod_of_dvd a (by decide : 2∣16)

/-- Local primitivity at two forces the denominator to be a unit modulo two. -/
theorem odd_denominator {N a b d : ℕ} (primitive : ¬2∣a ∨ ¬2∣b)
    (point : a^4+4*b^4 ≡ N*d^4 [MOD 16]) : Odd d := by
  by_contra bad
  have even : d%2=0 := by have := Nat.odd_iff.not.mp bad; omega
  change (a^4+4*b^4)%16=(N*d^4)%16 at point
  rw [Nat.add_mod, Nat.mul_mod 4, Nat.mul_mod N, fourth_mod, fourth_mod,
    fourth_mod, even,mul_zero,Nat.zero_mod] at point
  omega

/-- At depth four the congruence already forces a odd and determines which
of the two allowed residues occurs from the parity of b. -/
theorem necessary {N a b d : ℕ} (odd : Odd N) (den : Odd d)
    (point : a^4+4*b^4 ≡ N*d^4 [MOD 16]) :
    Odd a ∧ N%16=1+4*(b%2) := by
  change (a^4+4*b^4)%16=(N*d^4)%16 at point
  rw [Nat.add_mod, Nat.mul_mod 4, Nat.mul_mod N, fourth_mod, fourth_mod,
    fourth_mod, Nat.odd_iff.mp den] at point
  have := Nat.odd_iff.mp odd
  have := Nat.mod_lt a (by decide : 0<2)
  have := Nat.mod_lt b (by decide : 0<2)
  constructor
  · apply Nat.odd_iff.mpr
    omega
  · omega

/-- This direction assumes only that at least one numerator is odd. -/
theorem class_of_mod16 {N a b d : ℕ} (odd : Odd N) (primitive : ¬2∣a ∨ ¬2∣b)
    (eq : a^4+4*b^4 ≡ N*d^4 [MOD 16]) : N%16=1 ∨ N%16=5 := by
  have main := (necessary odd (odd_denominator primitive eq) eq).2
  omega

/-- For every fixed depth from four onward the criterion is exact. -/
theorem primitive_iff {N k : ℕ} (odd : Odd N) (depth : 4≤k) :
    PrimitivePoint N k ↔ N%16=1 ∨ N%16=5 := by
  constructor
  · rintro ⟨a,b,d,_,den,h⟩
    have main := (necessary odd den (h.of_dvd (pow_dvd_pow 2 depth))).2
    omega
  · intro good
    obtain ⟨a,b,_,cop,h⟩ := affine_point good k
    exact ⟨a,b,1,cop,by decide,by simpa using h⟩

theorem all_depths_iff {N : ℕ} (odd : Odd N) :
    (∀ k, PrimitivePoint N k) ↔ N%16=1 ∨ N%16=5 := by
  refine ⟨fun h => (primitive_iff odd (le_refl 4)).mp (h 4),?_⟩
  intro good k
  obtain ⟨a,b,_,cop,h⟩ := affine_point good k
  exact ⟨a,b,1,cop,by decide,by simpa using h⟩

end PrimeFactors.QuarticTwoLocalPoints
