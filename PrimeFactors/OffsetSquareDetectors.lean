import PrimeFactors.OffsetSquareSplit
import PrimeFactors.GroupedOffsetRows

namespace PrimeFactors.OffsetSquareDetectors
open CompleteOffsetSearch GroupedOffsetRows

/-- A covering set of primes detects every positive nonsquare through the
stated bound. The analytic small-prime result can supply this hypothesis. -/
def Detects (bound cutoff : ℕ) : Prop :=
  ∀ n : ℕ, 0<n → n≤bound → (¬∃ x : ℕ, x^2=n) →
    ∃ p : ℕ, p.Prime ∧ p≤cutoff ∧ ¬∃ b : ℤ, b^2 ≡ (n:ℤ) [ZMOD (p:ℤ)]

def Passes (D : ℤ) (cutoff : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p≤cutoff → ∃ b : ℤ, b^2 ≡ D [ZMOD (p:ℤ)]

/-- The ellipse identity bounds the signed discriminant independently of
the multiplier or the sizes of the two weighted summands. -/
theorem discriminant_height {T h N j : ℕ} (digits : N=T^2+h) (hp : 0<h)
    (short : 3*j^2≤4*h) (k : ℕ) :
    3*form T h j k≤4*(N:ℤ) := by
  have n : (N:ℤ)=(T:ℤ)^2+h := by exact_mod_cast digits
  have sharp : 3*(j:ℤ)^2≤4*(h:ℤ) := by exact_mod_cast short
  have positive : 0<(h:ℤ) := by exact_mod_cast hp
  have identity : (h:ℤ)*form T h j k + (2*(h:ℤ)*k-(T:ℤ)*j)^2=(N:ℤ)*j^2 := by
    rw [n]; unfold form; ring
  apply le_of_mul_le_mul_left _ positive
  nlinarith only [identity,sq_nonneg (2*(h:ℤ)*k-(T:ℤ)*j),mul_le_mul_of_nonneg_left sharp (Nat.cast_nonneg N : 0≤(N:ℤ))]

theorem detected_square_iff {D : ℤ} {bound cutoff : ℕ} (off : 0≤D) (fit : D≤(bound:ℤ))
    (detector : Detects bound cutoff) : Passes D cutoff ↔ ∃ d : ℕ, (d:ℤ)^2=D := by
  constructor
  · intro pass
    by_contra! nonsquare
    let n := D.toNat
    have eq : (n:ℤ)=D := Int.toNat_of_nonneg off
    have pos : 0<n := by
      by_contra! bad
      have : D=0 := by omega
      exact nonsquare 0 (by simp [this])
    have no : ¬∃ d : ℕ, d^2=n := by
      rintro ⟨d,dd⟩
      exact nonsquare d ((show (d:ℤ)^2=(n:ℤ) by exact_mod_cast dd).trans eq)
    obtain ⟨p,prime,le,reject⟩ := detector n pos (by omega) no
    exact reject (eq ▸ pass p prime le)
  · rintro ⟨d,rfl⟩ p _ _
    exact ⟨d,Int.ModEq.refl _⟩

/-- After the explicit h=1 exception is removed, compatibility at all the
detecting primes is equivalent to a successful executable probe. -/
theorem probe_iff_local {N T h j k cutoff : ℕ} (digits : N=T^2+h) (tp : 0<T)
    (hp : 0<h) (jp : 0<j) (kp : 0<k) (prim : j.Coprime k) (short : 3*j^2≤4*h)
    (regular : ¬(h=1 ∧ j=1 ∧ k=T)) (detect : Detects (4*N/3) cutoff) :
    (∃ f, probe N T j k=some f) ↔ 0≤form T h j k ∧ Passes (form T h j k) cutoff := by
  let S := j+2*T*k
  have nz : (N:ℤ)=(T:ℤ)^2+h := by exact_mod_cast digits
  have expand : (S:ℤ)^2-4*(k:ℤ)^2*N=form T h j k := by
    rw [nz]; dsimp [S,form]; push_cast; ring
  constructor
  · rintro ⟨f,hit⟩
    unfold probe at hit
    dsimp only at hit
    split at hit
    next good =>
      let d := (S^2-4*k^2*N).sqrt
      have sq : S^2=4*k^2*N+d^2 := by
        have a : 4*k^2*N≤S^2 := good.1
        have b : d^2=S^2-4*k^2*N := good.2.1
        omega
      have sz : (S:ℤ)^2=4*(k:ℤ)^2*N+(d:ℤ)^2 := by exact_mod_cast sq
      have eq : form T h j k=(d:ℤ)^2 := by linarith only [expand,sz]
      rw [eq]
      exact ⟨sq_nonneg _, fun _ _ _ => ⟨d,Int.ModEq.refl _⟩⟩
    next => contradiction
  · rintro ⟨nonneg,pass⟩
    have high := discriminant_height digits hp short k
    have fit : form T h j k≤((4*N/3:ℕ):ℤ) := by omega
    obtain ⟨d,sd⟩ := (detected_square_iff nonneg fit detect).mp pass
    have sq : S^2=4*k^2*N+d^2 := by
      exact_mod_cast (show (S:ℤ)^2=4*(k:ℤ)^2*N+(d:ℤ)^2 by linarith only [sd,expand])
    by_cases heavy : 2≤h
    · obtain ⟨f,found,_⟩ := OffsetSquareSplit.sharp_split digits heavy kp prim short sq
      exact ⟨f,found⟩
    · have one : h=1 := by omega
      subst h
      subst N
      have no := OffsetSquareSplit.failed_iff_one_exception tp jp kp prim short sq
      cases actual : probe (T^2+1) T j k with
      | none =>
        have bad := no.mp actual
        exact False.elim (regular ⟨rfl,bad.1,bad.2.1⟩)
      | some f => exact ⟨f,rfl⟩

set_option exponentiation.threshold 4096 in
/-- Integer scale used when applying a detecting-prime bound to the
quadratic character modulo 4096D for a 2048-bit input. -/
theorem conductor_bound {D N : ℕ} (height : 3*D≤4*N) (width : N<2^2048) :
    4096*D<2^2061 := by
  have scale : 4096*(4*(2:ℕ)^2048)<3*2^2061 := by decide +kernel
  omega

end PrimeFactors.OffsetSquareDetectors
