import PrimeFactors.DivisorWindowThreshold
import PrimeFactors.ChebyshevDivisorWindow

namespace PrimeFactors.ChebyshevDivisorThreshold

/-- For radius 2U, U=2^u, take c=s*(2u+1). The extra factor 2^(4sk)
is the fourth power of the 2^k in the Chebyshev determinant, raised to s. -/
def passes (a b c s m k : ℕ) : Prop :=
  (k+1)^(2*s*(k+1)) * 2^(2*a*m*(m+1)+c*k*(k+1)+4*s*k) < 2^(4*b*m*(k+1))

private theorem necessary_pass {a b c s m k : ℕ} (h : passes a b c s m k) :
    DivisorWindowThreshold.passes a b c s m k := by
  exact lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 0<2)
    (Nat.le_add_right _ _))) h

private theorem sufficient_pass {a b c s m k : ℕ} (hk : 0<k)
    (h : DivisorWindowThreshold.passes a b c (3*s) m k) : passes a b c s m k := by
  have extra : 2^(4*s*k)≤(k+1)^(4*s*(k+1)) :=
    (Nat.pow_le_pow_left (by omega : 2≤k+1) _).trans (Nat.pow_le_pow_right (by omega)
      (Nat.mul_le_mul_left _ (Nat.le_succ k)))
  unfold passes
  rw [pow_add]
  calc
    _ ≤ (k+1)^(2*s*(k+1)) * (2^(2*a*m*(m+1)+c*k*(k+1))*(k+1)^(4*s*(k+1))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ extra)
    _ = (k+1)^(2*(3*s)*(k+1))*2^(2*a*m*(m+1)+c*k*(k+1)) := by
      rw [show 2*(3*s)*(k+1)=2*s*(k+1)+4*s*(k+1) by ring,pow_add (k+1)]
      ac_rfl
    _ < _ := h

/-- The 2^k paid by the Chebyshev determinant affects finite dimensions.
At some dimension the exact boundary is the monomial boundary at half the radius. -/
theorem threshold {a b c s : ℕ} (hb : 0<b) (ba : b≤a) :
    (∃ k m : ℕ, 0<m ∧ m≤k ∧ passes a b c s m k) ↔ a*c<2*b^2 := by
  constructor
  · rintro ⟨k,m,hm,mk,H⟩
    exact DivisorWindowThreshold.necessary (hb.trans_le ba) (hm.trans_le mk) mk (necessary_pass H)
  · intro gain
    obtain ⟨k,m,hm,mk,H⟩ := DivisorWindowThreshold.attainable (s:=3*s) (hb.trans_le ba) hb ba gain
    exact ⟨k,m,hm,mk,sufficient_pass (hm.trans_le mk) H⟩

private def scaled (n D s c m k : ℕ) : Prop :=
  (k+1)^(2*s*(k+1)) * 2^(c*k*(k+1)+4*s*k) * n^(2*m*(m+1)) < D^(4*m*(k+1))

/-- The numerical sufficient LLL inequality at actual integer input and divisor floor. -/
def actual (n D u m k : ℕ) : Prop :=
  (k+1)^(2*(k+1)) * 2^((2*u+1)*k*(k+1)+4*k) * n^(2*m*(m+1)) < D^(4*m*(k+1))

private theorem pass_scaled (a b c s m k : ℕ) :
    passes a b c s m k ↔ scaled (2^a) (2^b) s c m k := by
  unfold passes scaled
  simp only [←pow_mul,pow_add]
  ac_nf

private theorem actual_scaled (n D u s m k : ℕ) (hs : 0<s) :
    actual n D u m k ↔ scaled (n^s) (D^s) s (s*(2*u+1)) m k := by
  unfold actual scaled
  rw [← Nat.pow_lt_pow_iff_left hs.ne',mul_pow,mul_pow]
  simp only [←pow_mul]
  rw [show (2*(k+1))*s=2*s*(k+1) by ring,
    show ((2*u+1)*k*(k+1)+4*k)*s=s*(2*u+1)*k*(k+1)+4*s*k by ring]
  ac_nf

theorem of_upper {a b s n D u m k : ℕ} (hs : 0<s) (up : n^s≤2^a) (low : 2^b≤D^s)
    (p : passes a b (s*(2*u+1)) s m k) : actual n D u m k := by
  apply (actual_scaled n D u s m k hs).2
  exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left up _)).trans_lt
    (((pass_scaled _ _ _ _ _ _).1 p).trans_le (Nat.pow_le_pow_left low _))

private theorem finite_bound {a b c s m k j : ℕ} (dim : (k+1)^2≤2^j)
    (room : j*s*(k+1)+(2*a*m*(m+1)+c*k*(k+1)+4*s*k)<4*b*m*(k+1)) :
    passes a b c s m k := by
  have h : (k+1)^(2*s*(k+1)) ≤ 2^(j*s*(k+1)) := by
    rw [mul_assoc 2 s (k+1),pow_mul (k+1) 2 (s*(k+1)),mul_assoc j s (k+1),pow_mul 2 j (s*(k+1))]
    exact Nat.pow_le_pow_left dim _
  unfold passes
  apply lt_of_le_of_lt (Nat.mul_le_mul_right _ h)
  rw [←pow_add]
  exact Nat.pow_lt_pow_right (by decide) room

private theorem twice_choose (k : ℕ) : 2*(k+1).choose 2=k*(k+1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.choose_succ_succ (k+1) 1,Nat.choose_one_right]
    nlinarith only [ih]

private theorem twice_tag (m : ℕ) : 2*(m+m.choose 2)=m*(m+1) := by
  cases m with
  | zero => decide
  | succ m => nlinarith only [twice_choose m]

/-- Expand the degree-k scaled determinant and classical LLL shortness inequality
without logarithms. This is the numerical predicate, independently of the cost of reduction. -/
theorem actual_iff_determinant (n D u m k : ℕ) :
    actual n D u m k ↔ (k+1)^(2*(k+1))*2^(k*(k+1))*
      (n^(m+m.choose 2)*(2^k*(2^u)^((k+1).choose 2)))^4 < (D^m)^(4*(k+1)) := by
  unfold actual
  simp only [mul_pow,←pow_mul]
  have exp : (2*u+1)*k*(k+1)+4*k =
      k*(k+1)+k*4+(u*(k+1).choose 2)*4 := by
    nlinarith only [congrArg (u*·) (twice_choose k)]
  have tag : (m+m.choose 2)*4=2*m*(m+1) := by nlinarith only [twice_tag m]
  rw [exp,pow_add (2:ℕ) _ ((u*(k+1).choose 2)*4),pow_add (2:ℕ) (k*(k+1)) (k*4),tag]
  ac_nf

/-- In dimensions where the pigeonhole factor is bounded by the LLL factor,
the numerical success supplies a nonzero bounded-degree relation at any center. -/
theorem at_center {n D u m k : ℕ} (hn : 0<n) (hd : 0<D) (dim : (k+1)^2≤2^k)
    (pass : actual n D u m k) (t : ℤ) :
    ∃ F : Polynomial ℤ, F≠0 ∧ F.roots.toFinset.card≤k ∧ ∀ x d : ℤ, d∣(n:ℤ) → d∣x-t →
      (D:ℤ)≤d → |x|≤2*(2^u:ℤ) → F.eval x=0 := by
  simp only [← Nat.cast_ofNat (R:=ℤ) (n:=2),← Nat.cast_pow]
  apply ChebyshevDivisorWindow.relation_exists (m:=m) hn (Nat.pow_pos (by decide : 0<2)) hd _ t
  have small : (k+1)^(2*(k+1))≤2^(k*(k+1)) := by
    rw [pow_mul,pow_mul]
    exact Nat.pow_le_pow_left dim _
  apply (Nat.pow_lt_pow_iff_left (by decide : 4≠0)).mp
  rw [mul_pow,mul_pow]
  have fourth : ((k+1)^(k+1))^4 = (k+1)^(2*(k+1))*(k+1)^(2*(k+1)) := by
    rw [←pow_mul,←pow_add]
    congr 1
    ring
  rw [fourth]
  have lll := (actual_iff_determinant _ _ _ _ _).1 pass
  calc
    _ ≤ ((k+1)^(2*(k+1))*2^(k*(k+1))) *
        (n^(m+m.choose 2)*(2^k*(2^u)^((k+1).choose 2)))^4 := by
      simp only [mul_pow]
      convert Nat.mul_le_mul_right
        ((n^(m+m.choose 2))^4*((2^k)^4*((2^u)^(k+1).choose 2)^4))
        (Nat.mul_le_mul_left ((k+1)^(2*(k+1))) small) using 1
      ac_rfl
    _ < _ := by
      convert lll using 1
      simp only [←pow_mul]
      ac_rfl

set_option exponentiation.threshold 40000 in
set_option maxRecDepth 16384 in
/-- One explicit degree and depth works at radius 2*2^510 even at this product's
smallest public divisor floor. Only the numerical determinant criterion is checked. -/
theorem crossed_passes : actual ChebyshevQuarticScale.crossed
    (CoupledDivisorWindow.lower ChebyshevQuarticScale.crossed) 510 316 632 := by
  apply of_upper (a:=32755) (b:=16370) (s:=16) (by decide) (by decide +kernel) (by decide +kernel)
  exact finite_bound (j:=19) (by decide) (by decide)

set_option exponentiation.threshold 40000 in
set_option maxRecDepth 16384 in
/-- The same public floor on the fresh input allows the next dyadic radius,
2*2^511, at one explicit larger dimension. -/
theorem fresh_passes : actual ChebyshevQuarticScale.fresh
    (CoupledDivisorWindow.lower ChebyshevQuarticScale.fresh) 511 1293 2586 := by
  apply of_upper (a:=32763) (b:=16378) (s:=16) (by decide) (by decide +kernel) (by decide +kernel)
  exact finite_bound (j:=23) (by decide) (by decide)

/-- Removing the finite 2^(4k) determinant price gives the monomial comparison
at half the Chebyshev radius. -/
theorem half_radius {n D u m k : ℕ} (p : actual n D u m k) :
    DivisorWindowThreshold.actual n D u m k := by
  exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_add_right _ _)))) p

/-- At the same crossed-input floor even this basis cannot certify the next
dyadic radius in any dimension under this particular LLL inequality. -/
theorem crossed_512_fails {m k : ℕ} (hm : 0<m) (mk : m≤k) :
    ¬actual ChebyshevQuarticScale.crossed
      (CoupledDivisorWindow.lower ChebyshevQuarticScale.crossed) 511 m k :=
  fun p => DivisorWindowThreshold.crossed_fails hm mk (half_radius p)

end PrimeFactors.ChebyshevDivisorThreshold
