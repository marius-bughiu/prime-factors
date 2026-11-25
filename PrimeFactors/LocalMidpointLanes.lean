import PrimeFactors.FactorSum
import Mathlib.Data.Nat.Factorization.Basic
import PrimeFactors.Certificate
import Mathlib.Tactic.NormNum.Prime

namespace PrimeFactors.LocalMidpointLanes

/-- An integer square root modulo a power of two. -/
def hasRoot (e : ℕ) (D : ℤ) : Prop := ∃ x : ℤ, (2:ℤ)^e ∣ D-x^2

/-- Completing the square with an integer midpoint requires no division by two
in the residue ring. This includes even moduli. -/
theorem midpoint_iff {m : ℕ} (N h : ZMod m) :
    AdmissibleSum N (2*h) ↔ IsSquare (h^2-N) := by
  constructor
  · rintro ⟨x,y,hprod,hsum⟩
    refine ⟨x-h, ?_⟩
    linear_combination hprod - x * hsum
  · rintro ⟨d,hd⟩
    exact ⟨h+d,h-d,by linear_combination hd,by ring⟩

private theorem odd_square {u : ℤ} (hu : Odd u) : (8:ℤ) ∣ u^2-1 := by
  obtain ⟨w,rfl⟩ := hu
  rcases Int.even_or_odd w with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · exact ⟨v*(2*v+1),by ring⟩
  · exact ⟨(v+1)*(2*v+1),by ring⟩

/-- An odd square unit modulo eight can be lifted one bit at a time. -/
theorem lift_eight {D : ℤ} (hD : (8:ℤ) ∣ D-1) (k : ℕ) :
    ∃ x : ℤ, Odd x ∧ (2:ℤ)^(k+3) ∣ D-x^2 := by
  induction k with
  | zero => exact ⟨1,by decide,by simpa using hD⟩
  | succ k ih =>
    obtain ⟨x,⟨v,hv⟩,z,hz⟩ := ih
    refine ⟨x+4*2^k*z, ⟨v+2*2^k*z,by linarith only [hv]⟩, -v*z-2^k*z^2, ?_⟩
    rw [pow_add] at hz
    rw [show k+1+3=k+4 by omega, pow_add]
    rw [hv] at hz ⊢
    linear_combination hz

/-- The available low bits of one suffice to construct a unit square root. -/
theorem square_unit {D : ℤ} (r : ℕ) (hd : (2:ℤ)^(min r 3) ∣ D-1) :
    hasRoot r D := by
  by_cases small : r ≤ 3
  · exact ⟨1,by simpa [min_eq_left small] using hd⟩
  · rw [min_eq_right (by omega : 3 ≤ r)] at hd
    obtain ⟨x,_,hx⟩ := lift_eight hd (r-3)
    exact ⟨x,by simpa [Nat.sub_add_cancel (by omega : 3 ≤ r)] using hx⟩

/-- A square is zero or has even valuation and odd part equal to one
through the first three available bits. The modulus in each nonzero lane
examines at most three bits beyond the valuation. -/
theorem root_iff_lane (e : ℕ) (D : ℤ) :
    hasRoot e D ↔ (2:ℤ)^e ∣ D ∨ ∃ j r : ℕ, 0<r ∧ e=2*j+r ∧
      (2:ℤ)^(2*j+min r 3) ∣ D-2^(2*j) := by
  constructor
  · rintro ⟨x,hx⟩
    by_cases zero : x.natAbs = 0
    · left
      have : x=0 := Int.natAbs_eq_zero.mp zero
      simpa [this] using hx
    obtain ⟨j,u,hu,he⟩ := Nat.exists_eq_two_pow_mul_odd zero
    have square : x^2=(2:ℤ)^(2*j)*(u:ℤ)^2 := by
      have castEq := congrArg (fun n : ℕ => (n:ℤ)) he
      push_cast at castEq
      calc
        _ = |x|^2 := (sq_abs x).symm
        _ = _ := by rw [castEq, mul_pow, ← pow_mul]; rw [Nat.mul_comm j 2]
    rw [square] at hx
    by_cases endpt : e ≤ 2*j
    · have scaled : (2:ℤ)^e ∣ 2^(2*j)*(u:ℤ)^2 :=
        (pow_dvd_pow (2:ℤ) endpt).trans (dvd_mul_right _ _)
      exact Or.inl (by simpa using dvd_add hx scaled) 
    · let r := e-2*j
      have er : e=2*j+r := by dsimp [r]; omega
      refine Or.inr ⟨j,r,by dsimp [r]; omega,er,?_⟩
      have div1 : (2:ℤ)^(2*j+min r 3) ∣ D-2^(2*j)*(u:ℤ)^2 :=
        (pow_dvd_pow _ (by rw [er]; omega)).trans hx
      have odd : Odd (u:ℤ) := by exact_mod_cast hu
      have div2 : (2:ℤ)^(min r 3) ∣ (u:ℤ)^2-1 :=
        (pow_dvd_pow (2:ℤ) (min_le_right r 3)).trans (odd_square odd)
      obtain ⟨a,ha⟩ := div1
      obtain ⟨b,hb⟩ := div2
      refine ⟨a+b,?_⟩
      rw [pow_add] at ha ⊢
      linear_combination ha + (2:ℤ)^(2*j)*hb
  · rintro (zero | ⟨j,r,_,rfl,b,hb⟩)
    · exact ⟨0,by simpa using zero⟩
    · obtain ⟨x,c,hc⟩ := square_unit (D:=1+2^(min r 3)*b) r ⟨b,by ring⟩
      refine ⟨2^j*x,c,?_⟩
      rw [pow_add] at hb ⊢
      rw [mul_pow, ← pow_mul, Nat.mul_comm j 2]
      linear_combination hb + (2:ℤ)^(2*j)*hc

/-- The integer lanes describe exactly the sums of residue-class factors. -/
theorem midpoint_iff_integer (e : ℕ) (N h : ℤ) :
    AdmissibleSum (N : ZMod (2^e)) (2*(h : ZMod (2^e))) ↔ hasRoot e (h^2-N) := by
  rw [midpoint_iff]
  constructor
  · rintro ⟨z,hz⟩
    obtain ⟨x,rfl⟩ := ZMod.intCast_surjective z
    refine ⟨x,?_⟩
    have H := (ZMod.intCast_zmod_eq_zero_iff_dvd (h^2-N-x^2) (2^e)).mp (by
      push_cast
      rw [hz, pow_two, sub_self])
    simpa using H
  · rintro ⟨x,hx⟩
    have H := (ZMod.intCast_zmod_eq_zero_iff_dvd (h^2-N-x^2) (2^e)).mpr (by simpa using hx)
    push_cast at H
    exact ⟨(x : ZMod (2^e)),by simpa [pow_two] using sub_eq_zero.mp H⟩

/-- The unique midpoint in the bounded worked example splits its input. -/
theorem example_34387 : 194^2-34387 = (57:ℕ)^2 ∧
    ExactFactorization 34387 [194-57,194+57] := by
  norm_num [ExactFactorization]

end PrimeFactors.LocalMidpointLanes
