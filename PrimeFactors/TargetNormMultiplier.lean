import PrimeFactors.WeightedMultiplierPell
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.NormNum

/-! Necessary local tests before searching for a primitive witness
`X² = k N Y² + D T²`. Every coefficient in the tests is public. -/
namespace PrimeFactors.TargetNormMultiplier

/-- A prime dividing the multiplier exactly once and missing N cannot divide
the target's coordinate T. Otherwise it divides X, and cancellation of its
square forces it to divide Y as well. -/
theorem denominator_unit {k N D X Y T ell : ℕ} (hp : ell.Prime)
    (norm : X^2 = k*N*Y^2 + D*T^2) (primitive : X.Coprime Y)
    (divides : ell ∣ k) (once : ¬ell^2 ∣ k) (miss : ¬ell ∣ N) : ¬ell ∣ T := by
  intro ht
  have ht2 := pow_dvd_pow_of_dvd ht 2
  have hx := hp.dvd_of_dvd_pow (show ell ∣ X^2 by
    rw [norm]
    exact dvd_add ((divides.mul_right N).mul_right (Y^2))
      (dvd_mul_of_dvd_right (dvd_pow ht (by decide : 2 ≠ 0)) D))
  have hy := hp.coprime_iff_not_dvd.mp (primitive.coprime_dvd_left hx)
  have large := pow_dvd_pow_of_dvd hx 2
  rw [norm] at large
  have left := (Nat.dvd_add_iff_left (dvd_mul_of_dvd_right ht2 D)).mpr large
  obtain ⟨r,kr⟩ := divides
  have lift : ell*ell ∣ ell*(r*N*Y^2) := by simpa [kr, pow_two,mul_assoc] using left
  have small := Nat.dvd_of_mul_dvd_mul_left hp.pos lift
  rcases hp.dvd_mul.mp small with line | square
  · rcases hp.dvd_mul.mp line with root | nh
    · apply once
      obtain ⟨v,hv⟩ := root
      exact ⟨v,by rw [kr,hv,pow_two,mul_assoc]⟩
    · exact miss nh
  · exact hy (hp.dvd_of_dvd_pow square)

/-- The square root at the multiplier prime is X/T. The test applies to
every prime, and D may vanish modulo that prime. -/
theorem multiplier_square {k N D X Y T ell : ℕ} [hp : Fact ell.Prime]
    (norm : X^2 = k*N*Y^2 + D*T^2) (primitive : X.Coprime Y)
    (divides : ell ∣ k) (once : ¬ell^2 ∣ k) (miss : ¬ell ∣ N) : IsSquare (D : ZMod ell) := by
  have tn : (T : ZMod ell) ≠ 0 := fun h =>
    denominator_unit hp.out norm primitive divides once miss ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp h)
  have kz := (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mpr divides
  have eq := congrArg (fun v : ℕ => (v : ZMod ell)) norm
  push_cast at eq
  rw [kz,zero_mul,zero_mul,zero_add] at eq
  apply (isSquare_iff_exists_sq _).mpr
  exact ⟨(X : ZMod ell)/T, by rw [div_pow,eq,mul_div_cancel_right₀ _ (pow_ne_zero _ tn)]⟩

/-- Every divisor of D, including D itself, admits a square root of kN.
The existing primitive congruence theorem supplies a root modulo D*T². -/
theorem target_square {k N D X Y T m : ℕ}
    (norm : X^2 = k*N*Y^2 + D*T^2) (primitive : X.Coprime Y) (divides : m ∣ D) :
    IsSquare ((k*N : ℕ) : ZMod m) := by
  have eq : (X : ℤ)^2 = (k:ℤ)*N*Y^2+D*T^2 := by exact_mod_cast norm
  obtain ⟨r,h,_⟩ := WeightedMultiplierPell.primitive_class
    (sub_eq_iff_eq_add.mpr (eq.trans (add_comm ..))) primitive.symm.isCoprime
  have md : (m : ℤ) ∣ D := by exact_mod_cast divides
  have lift := (dvd_mul_of_dvd_left md ((T:ℤ)^2)).trans h
  have zero := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr lift
  push_cast at zero
  apply (isSquare_iff_exists_sq _).mpr
  refine ⟨(r : ZMod m),?_⟩
  push_cast
  exact (sub_eq_zero.mp zero).symm

/-- For unit D the multiplier-side square test is one Legendre-symbol check. -/
theorem multiplier_sign {k N D X Y T ell : ℕ} [Fact ell.Prime]
    (norm : X^2 = k*N*Y^2 + D*T^2) (primitive : X.Coprime Y)
    (divides : ell ∣ k) (once : ¬ell^2 ∣ k) (miss : ¬ell ∣ N) (unit : ¬ell ∣ D) :
    legendreSym ell D = 1 :=
  (legendreSym.eq_one_iff' ell (fun h => unit ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp h))).mpr
    (multiplier_square norm primitive divides once miss)

/-- For unit kN each target-prime check also reduces to one Legendre symbol. -/
theorem target_sign {k N D X Y T ell : ℕ} [Fact ell.Prime]
    (norm : X^2 = k*N*Y^2 + D*T^2) (primitive : X.Coprime Y) (divides : ell ∣ D)
    (unit : ¬ell ∣ k*N) : legendreSym ell (↑(k*N : ℕ) : ℤ) = 1 :=
  (legendreSym.eq_one_iff' ell (fun h => unit ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp h))).mpr
    (target_square norm primitive divides)

/-- Square residues and odd-square residues modulo 16. -/
noncomputable def squares16 : Finset (ZMod 16) := {0,1,4,9}
noncomputable def oddSquares16 : Finset (ZMod 16) := {1,9}

/-- An exact local gate for primitive coordinate pairs modulo 16.
The arguments are the public coefficients kN and D. -/
def pass16 (A D : ZMod 16) : Prop :=
  ∃ u ∈ squares16, ∃ v ∈ squares16, (u ∈ oddSquares16 ∨ v ∈ oddSquares16) ∧
    ∃ w ∈ squares16, u = A*v+D*w

private theorem square16 (x : ZMod 16) :
    x^2 ∈ squares16 ∧ (x^2 ∈ oddSquares16 ↔ x.val % 2 = 1) :=
  (by decide : ∀ z : ZMod 16, z^2 ∈ squares16 ∧ (z^2 ∈ oddSquares16 ↔ z.val % 2 = 1)) x

/-- Every entry retained by the table has a solution modulo 16 with an odd
first or second coordinate. An integer solution may still fail elsewhere. -/
theorem pass16_iff (A D : ZMod 16) :
    pass16 A D ↔ ∃ x y t : ZMod 16, (x.val%2 = 1 ∨ y.val%2 = 1) ∧ x^2 = A*y^2+D*t^2 := by
  have root : ∀ u : ZMod 16, u ∈ squares16 → ∃ x : ZMod 16, x^2 = u := by decide
  constructor
  · rintro ⟨u,hu,v,hv,odd,w,hw,eq⟩
    obtain ⟨x,rfl⟩ := root _ hu
    obtain ⟨y,rfl⟩ := root _ hv
    obtain ⟨t,rfl⟩ := root _ hw
    exact ⟨x,y,t,odd.imp (square16 x).2.mp (square16 y).2.mp,eq⟩
  · rintro ⟨x,y,t,odd,eq⟩
    exact ⟨x^2,(square16 x).1,y^2,(square16 y).1,
      odd.imp (square16 x).2.mpr (square16 y).2.mpr,t^2,(square16 t).1,eq⟩

theorem primitive_pass16 {k N D X Y T : ℕ}
    (norm : X^2 = k*N*Y^2 + D*T^2) (primitive : X.Coprime Y) :
    pass16 ((k*N:ℕ) : ZMod 16) D := by
  apply (pass16_iff ..).mpr
  refine ⟨X,Y,T,?_,?_⟩
  · simp only [ZMod.val_natCast, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 16)]
    by_contra! even
    have hx : 2 ∣ X := Nat.dvd_of_mod_eq_zero (by omega)
    have hy : 2 ∣ Y := Nat.dvd_of_mod_eq_zero (by omega)
    exact Nat.not_coprime_of_dvd_of_dvd (by decide : 1<2) hx hy primitive
  · exact_mod_cast congrArg (fun u : ℕ => (u : ZMod 16)) norm

end PrimeFactors.TargetNormMultiplier
