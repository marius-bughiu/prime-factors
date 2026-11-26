import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic

/-! Homogeneous norms and rotations of a monic cubic taking a prescribed
integer value. The coefficient order is constant, linear, quadratic. -/
namespace PrimeFactors.CubicSmoothBaseChoice

def eval (c₀ c₁ c₂ x : ℤ) : ℤ := x^3+c₂*x^2+c₁*x+c₀

def rowNorm (c₀ c₁ c₂ a b : ℤ) : ℤ := a^3-c₂*a^2*b+c₁*a*b^2-c₀*b^3

/-- Multiplication by a+bα on the power basis 1,α,α² has this determinant. -/
theorem det_row (c₀ c₁ c₂ a b : ℤ) :
    (Matrix.det !![a,0,-c₀*b; b,a,-c₁*b; 0,b,a-c₂*b])=rowNorm c₀ c₁ c₂ a b := by
  rw [Matrix.det_fin_three]
  simp [rowNorm]
  ring

/-- The rational side divides the signed sum of the norm and b³ times the
public cubic value, even when m and all coefficients were chosen from that value. -/
theorem row_divides (c₀ c₁ c₂ m a b : ℤ) :
    a+b*m ∣ rowNorm c₀ c₁ c₂ a b+b^3*eval c₀ c₁ c₂ m := by
  refine ⟨a^2-a*b*m+b^2*m^2+c₂*b*(b*m-a)+c₁*b^2,?_⟩
  unfold rowNorm eval
  ring

theorem primitive (a b m : ℤ) (hab : IsCoprime a b) : IsCoprime (a+b*m) b := by
  obtain ⟨u,v,h⟩ := hab
  exact ⟨u,v-u*m,by linear_combination h⟩

theorem primitive_gcd {a b : ℤ} (m : ℤ) (hab : Int.gcd a b=1) : Int.gcd (a+b*m) b=1 :=
  Int.isCoprime_iff_gcd_eq_one.mp (primitive a b m (Int.isCoprime_iff_gcd_eq_one.mpr hab))

/-- Rotating f by (uX+v)(X−m) leaves f(m) fixed. -/
theorem rotate_eval (c₀ c₁ c₂ m u v x : ℤ) :
    eval (c₀-v*m) (c₁+v-u*m) (c₂+u) x =
      eval c₀ c₁ c₂ x + (u*x+v)*(x-m) := by unfold eval; ring

theorem rotate_norm (c₀ c₁ c₂ m u v a b : ℤ) :
    rowNorm (c₀-v*m) (c₁+v-u*m) (c₂+u) a b =
      rowNorm c₀ c₁ c₂ a b + b*(a+b*m)*(v*b-u*a) := by unfold rowNorm; ring

/-- Without any coefficient or irreducibility restriction, every integer in
the indicated progression is attained by a rotation at a primitive row. -/
theorem attainable {a b : ℤ} (hab : IsCoprime a b) (c₀ c₁ c₂ m z : ℤ) :
    (∃ u v : ℤ, rowNorm (c₀-v*m) (c₁+v-u*m) (c₂+u) a b=z) ↔
      b*(a+b*m) ∣ z-rowNorm c₀ c₁ c₂ a b := by
  obtain ⟨i,j,h⟩ := hab
  constructor
  · rintro ⟨u,v,rfl⟩
    exact ⟨v*b-u*a,by rw [rotate_norm]; ring⟩
  · rintro ⟨k,hk⟩
    refine ⟨-i*k,j*k,?_⟩
    rw [rotate_norm]
    linear_combination -hk + b*(a+b*m)*k*h

private theorem five_step (k : ℕ) : ∃ v : ℤ, (5:ℤ)^(2^k : ℕ)=1+2^(k+2)*(2*v+1) := by
  induction k with
  | zero => exact ⟨0,by norm_num⟩
  | succ k ih =>
    obtain ⟨v,hv⟩ := ih
    refine ⟨v+2^k*(2*v+1)^2,?_⟩
    rw [pow_succ (2:ℕ) k,pow_mul,hv]
    simp only [Nat.succ_eq_add_one,pow_add]
    ring
theorem dyadic_power {z : ℤ} (hz : 4∣z-1) (k : ℕ) :
    ∃ e : ℕ, e<2^k ∧ (2:ℤ)^(k+2)∣z-5^e := by
  induction k with
  | zero => exact ⟨0,by norm_num,by simpa using hz⟩
  | succ k ih =>
    obtain ⟨e,cap,a,ha⟩ := ih
    obtain ⟨v,hv⟩ := five_step k
    rcases Int.even_or_odd a with ⟨c,hc⟩ | odd
    · refine ⟨e,by rw [pow_succ]; omega,c,?_⟩
      rw [ha,hc,show k+1+2=k+2+1 by omega,pow_succ]
      ring
    · have xodd : Odd ((5:ℤ)^e*(2*v+1)) :=
        (show Odd (5:ℤ) by decide).pow.mul ⟨v,rfl⟩
      obtain ⟨c,hc⟩ := odd.sub_odd xodd
      refine ⟨e+2^k,by rw [pow_succ]; omega,c,?_⟩
      rw [pow_add,hv,show k+1+2=k+2+1 by omega,pow_succ]
      linear_combination ha + 2^(k+2)*hc


/-- Either sign of an odd integer is 1 modulo 4, so signed powers of 5
exhaust the invertible residues of every power of 2 at least 4. -/
theorem signed_five {z : ℤ} (odd : Odd z) (k : ℕ) :
    ∃ e : ℕ, e<2^k ∧ ((2:ℤ)^(k+2)∣z-5^e ∨ (2:ℤ)^(k+2)∣z+5^e) := by
  obtain ⟨i,hi⟩ := odd
  by_cases h : 4∣z-1
  · obtain ⟨e,cap,h⟩ := dyadic_power h k
    exact ⟨e,cap,Or.inl h⟩
  · have hz : 4∣-z-1 := by omega
    obtain ⟨e,cap,v,hv⟩ := dyadic_power hz k
    exact ⟨e,cap,Or.inr ⟨-v,by linear_combination -hv⟩⟩

noncomputable def eval₂ (c₀ c₁ c₂ : ℤ) (x : ZMod 2) : ZMod 2 := x^3+c₂*x^2+c₁*x+c₀

private theorem two_choices (c₀ c₁ c₂ m t k : ZMod 2)
    (ev : m+t=0) (n : m^3+c₂*m^2+c₁*m+c₀=1) :
    (∀ x : ZMod 2, x^3+c₂*x^2+c₁*x+c₀+k*(x-m)≠0) ∨
      (∀ x : ZMod 2, x^3+c₂*x^2+c₁*x+c₀+(x+k+t)*(x-m)≠0) := by decide +revert

theorem certified_rotation {c₀ c₁ c₂ m t : ℤ} (ev : Even (m+t))
    (odd : Odd (eval c₀ c₁ c₂ m)) (k : ℤ) :
    ∃ u v : ℤ, (u=0 ∨ u=1) ∧
      rowNorm (c₀-v*m) (c₁+v-u*m) (c₂+u) t 1 = rowNorm c₀ c₁ c₂ t 1+(m+t)*k ∧
      ∀ x : ZMod 2, eval₂ (c₀-v*m) (c₁+v-u*m) (c₂+u) x≠0 := by
  obtain ⟨i,hi⟩ := ev
  obtain ⟨j,hj⟩ := odd
  have h0 : (m:ZMod 2)+t=0 := by
    have h := congrArg (fun z : ℤ => (z:ZMod 2)) hi
    push_cast at h
    simpa only [←two_mul, show (2:ZMod 2)=0 by decide,zero_mul,zero_add] using h
  have h1 : (m:ZMod 2)^3+c₂*(m:ZMod 2)^2+c₁*(m:ZMod 2)+c₀=1 := by
    unfold eval at hj
    have h := congrArg (fun z : ℤ => (z:ZMod 2)) hj
    push_cast at h
    simpa only [←two_mul, show (2:ZMod 2)=0 by decide,zero_mul,zero_add] using h
  rcases two_choices c₀ c₁ c₂ m t k h0 h1 with zero | one
  · refine ⟨0,k,Or.inl rfl,by rw [rotate_norm]; ring,?_⟩
    intro x h
    apply zero x
    unfold eval₂ at h
    push_cast at h
    linear_combination h
  · refine ⟨1,k+t,Or.inr rfl,by rw [rotate_norm]; ring,?_⟩
    intro x h
    apply one x
    unfold eval₂ at h
    push_cast at h
    linear_combination h


/-- At a dyadic rational value of at least 4, unrestricted rotations can
always produce one jointly smooth row over an irreducible cubic. The norm
is a signed power of 5. Its exponent, not its bit length, is bounded here. -/
theorem dyadic_smooth_row {c₀ c₁ c₂ m t : ℤ} (k : ℕ) (anchor : m+t=2^(k+2))
    (odd : Odd (eval c₀ c₁ c₂ m)) :
    ∃ u v : ℤ, (u=0 ∨ u=1) ∧
      eval (c₀-v*m) (c₁+v-u*m) (c₂+u) m=eval c₀ c₁ c₂ m ∧
      (∀ x : ZMod 2, eval₂ (c₀-v*m) (c₁+v-u*m) (c₂+u) x≠0) ∧
      ∃ e : ℕ, e<2^k ∧
        (rowNorm (c₀-v*m) (c₁+v-u*m) (c₂+u) t 1=5^e ∨
         rowNorm (c₀-v*m) (c₁+v-u*m) (c₂+u) t 1= -(5^e)) := by
  have even : Even (m+t) := by
    refine ⟨2^(k+1),?_⟩
    rw [anchor,pow_succ]
    ring
  have div := row_divides c₀ c₁ c₂ m t 1
  simp only [one_mul,one_pow] at div
  rw [add_comm t m] at div
  have h2 : 2∣rowNorm c₀ c₁ c₂ t 1 + eval c₀ c₁ c₂ m := (even_iff_two_dvd.mp even).trans div
  have on : Odd (rowNorm c₀ c₁ c₂ t 1) := by
    obtain ⟨j,hj⟩ := odd
    exact ⟨(rowNorm c₀ c₁ c₂ t 1-1)/2,by omega⟩
  obtain ⟨e,cap,h | h⟩ := signed_five on k
  all_goals
    obtain ⟨b,hb⟩ := h
    obtain ⟨u,v,small,norm,prime⟩ := certified_rotation even odd (-b)
    refine ⟨u,v,small,by rw [rotate_eval]; ring,prime,e,cap,?_⟩
    rw [norm,anchor]
  · exact Or.inl (by linear_combination hb)
  · exact Or.inr (by linear_combination hb)
open Polynomial
/-- Transport the actual two-residue certificate to irreducibility over ℚ
using the monic cubic's integer-root criterion and Gauss's lemma. -/
theorem irreducible_of_certificate {c₀ c₁ c₂ : ℤ}
    (cert : ∀ x : ZMod 2, eval₂ c₀ c₁ c₂ x≠0) :
    Irreducible ((X^3+C c₂*X^2+C c₁*X+C c₀ : ℤ[X]).map (Int.castRingHom ℚ)) := by
  let f : ℤ[X] := X^3+C c₂*X^2+C c₁*X+C c₀
  have monic : f.Monic := by dsimp [f]; monicity!
  have deg : f.natDegree=3 := by dsimp [f]; compute_degree!
  apply (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast monic.isPrimitive).mp
  apply (monic.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)).mpr
  apply Multiset.eq_zero_of_forall_not_mem
  intro r member
  have ev := (Polynomial.mem_roots monic.ne_zero).mp member
  change Polynomial.eval r f=0 at ev
  simp [f] at ev
  have modtwo := congrArg (fun a : ℤ => (a:ZMod 2)) ev
  push_cast at modtwo
  exact cert r modtwo
end PrimeFactors.CubicSmoothBaseChoice
