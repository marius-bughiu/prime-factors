import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Prod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace PrimeFactors.FrobeniusShiftCount

/-- At a split embedding, Frobenius fixes the base-field coordinate. -/
theorem split_power {p : ℕ} [Fact p.Prime] (q : ℕ) (a r k : ZMod p) :
    (a+r)^(p*q) = k*(a-r) ↔ (a+r)^q = k*(a+r) + (-2*k*r) := by
  rw [pow_mul, ZMod.pow_card]
  ring_nf

/-- On the quadratic field component the tested value becomes one fixed
power of the conjugate. Here n+1 is the partner prime. -/
theorem inert_power {E : Type*} [Field E] (n q : ℕ) {u v k : E}
    (frob : u^q=v) (nv : v≠0) : u^((n+1)*q)=k*v ↔ v^n=k := by
  rw [Nat.mul_comm (n+1) q, pow_mul, frob, pow_succ]
  exact ⟨fun h => mul_right_cancel₀ nv h, fun h => congrArg (fun z => z*v) h⟩

/-- A fixed nonidentity ratio of two roots of X^n = A X + B
uniquely specifies its denominator when both coefficients are nonzero. -/
theorem split_denominator {F : Type*} [Field F] {n : ℕ} {A B t y z : F}
    (hA : A ≠ 0) (hB : B ≠ 0) (ht : t ≠ 1)
    (hy : y^n = A*y+B) (hz : z^n = A*z+B)
    (hty : (t*y)^n = A*(t*y)+B) (htz : (t*z)^n = A*(t*z)+B) :
    y = z := by
  rw [mul_pow,hy] at hty
  rw [mul_pow,hz] at htz
  have same : (t^n-t)*A*(y-z) = 0 := by linear_combination hty - htz
  rcases mul_eq_zero.mp same with vanish | same
  · have fixed := sub_eq_zero.mp ((mul_eq_zero.mp vanish).resolve_right hA)
    rw [fixed] at hty
    exact False.elim (ht (sub_eq_zero.mp ((mul_eq_zero.mp
      (show (t-1)*B=0 by linear_combination hty)).resolve_right hB)))
  · exact sub_eq_zero.mp same

/-- The set of shifted roots at one split embedding has at most
one ordered off-diagonal pair for each value of the ratio. -/
theorem split_card {F : Type*} [Field F] [Fintype F] {n : ℕ} (hn : 0<n)
    {A B : F} (hA : A ≠ 0) (hB : B ≠ 0) (s : Finset F)
    (roots : ∀ x∈s, x^n=A*x+B) : s.card*s.card-s.card ≤ Fintype.card F := by
  classical
  have nz (x : F) (hx : x∈s) : x≠0 := by
    rintro rfl
    exact hB (by simpa [zero_pow hn.ne'] using (roots 0 hx).symm)
  let ratio := fun pair : F × F => pair.1/pair.2
  have inj : Set.InjOn ratio s.offDiag := by
    rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd eq
    obtain ⟨ha,hb,ne⟩ := Finset.mem_offDiag.mp hab
    obtain ⟨hc,hd,_⟩ := Finset.mem_offDiag.mp hcd
    let t := a/b
    have first : t*b=a := div_mul_cancel₀ _ (nz _ hb)
    have second : t*d=c := by
      change a/b*d=c
      rw [show a/b=c/d from eq, div_mul_cancel₀ _ (nz _ hd)]
    have ht : t ≠ 1 := by
      intro h
      exact ne (by simpa [h] using first.symm)
    have same := split_denominator hA hB ht (roots _ hb) (roots _ hd)
      (by simpa [first] using roots _ ha) (by simpa [second] using roots _ hc)
    have eqA : a=c := first.symm.trans ((congrArg (fun x => t*x) same).trans second)
    exact Prod.ext eqA same
  simpa only [Finset.card_image_of_injOn inj, Finset.offDiag_card] using
    (Finset.card_le_univ (s.offDiag.image ratio))

/-- A line through an element outside the base field has distinct ratios
for all ordered pairs of distinct points. -/
theorem line_ratio {F E : Type*} [Field F] [Field E] (i : F →+* E)
    {w : E} (outside : ∀ x, w ≠ i x) {a b c d : F} (ne : a ≠ b)
    (eq : (i a+w)*(i d+w)=(i c+w)*(i b+w)) : a=c ∧ b=d := by
  let u := a+d-c-b
  let v := c*b-a*d
  have rel : i u*w = i v := by
    simp only [u,v,map_sub,map_add,map_mul]
    linear_combination eq
  have u0 : u=0 := by
    by_contra h
    apply outside (v/u)
    rw [map_div₀,eq_div_iff (by simpa using h : i u ≠ 0),mul_comm,rel]
  have v0 : v=0 := i.injective (by simpa [u0] using rel.symm)
  dsimp [u] at u0
  dsimp [v] at v0
  have fac : (a-b)*(a-c)=0 := by linear_combination a*u0+v0
  have ac := sub_eq_zero.mp ((mul_eq_zero.mp fac).resolve_left (sub_ne_zero.mpr ne))
  exact ⟨ac, by linear_combination -u0 + ac⟩

/-- If the points on a translated line also lie in one power fiber, their
off-diagonal ratios are distinct h-th roots of unity. -/
theorem inert_card {F E : Type*} [Field F] [Field E] (i : F →+* E)
    {w : E} (outside : ∀ x, w ≠ i x) {h : ℕ} (hh : 0<h)
    {k : E} (hk : k≠0) (s : Finset F) (roots : ∀ x∈s, (i x+w)^h=k) :
    s.card*s.card-s.card ≤ h := by
  classical
  let point := fun x => i x+w
  have nz (x : F) : point x ≠ 0 := by
    intro zero
    exact outside (-x) (by rw [map_neg]; dsimp [point] at zero; linear_combination zero)
  let ratio := fun pair : F × F => point pair.1 / point pair.2
  have inj : Set.InjOn ratio s.offDiag := by
    rintro ⟨a,b⟩ hab ⟨c,d⟩ _ eq
    exact (Prod.ext_iff.mpr (line_ratio i outside (Finset.mem_offDiag.mp hab).2.2
      ((div_eq_div_iff (nz b) (nz d)).mp eq)))
  have subset : s.offDiag.image ratio ⊆ (Polynomial.nthRoots h (1:E)).toFinset := by
    intro r hr
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨ha,hb,_⟩ := Finset.mem_offDiag.mp hab
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_nthRoots hh).mpr
    change ((i a+w)/(i b+w))^h = 1
    rw [div_pow,roots a ha,roots b hb,div_self hk]
  have pairBound := (Finset.card_le_card subset).trans (Multiset.toFinset_card_le _)
  rw [Finset.card_image_of_injOn inj, Finset.offDiag_card] at pairBound
  exact pairBound.trans (Polynomial.card_nthRoots _ _)

/-- With s(s-1) strictly below the square of B, there are at most B shifts. -/
theorem from_pair_bound {s B : ℕ} (h : s*s-s < B*B) : s ≤ B := by
  by_contra! bigger
  obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s≠0)
  have bound := Nat.mul_le_mul (show B≤s by omega) (show B≤s+1 by omega)
  rw [Nat.succ_mul, Nat.add_sub_cancel] at h
  exact (not_lt_of_ge bound) h

set_option exponentiation.threshold 2048 in
set_option maxRecDepth 4000 in
/-- Count lifts from two split embeddings and one inert prime, allowing their
overlaps. This is the exact numerical range used for 1024-bit primes. -/
theorem fraction_2048 {p q s₁ s₂ t : ℕ}
    (pl : 2^1023 ≤ p) (ql : 2^1023 ≤ q) (pu : p < 2^1024)
    (split₁ : s₁*s₁-s₁ ≤ p) (split₂ : s₂*s₂-s₂ ≤ p)
    (inert : t*t-t ≤ p-1) :
    2^509*((s₁+s₂)*q+t*p) < p*q := by
  have sq : (2:ℕ)^1024 = 2^512*2^512 := by decide
  have fourth : 4*2^509*2^512 = (2:ℕ)^1023 := by decide
  have bound (s : ℕ) (h : s*s-s≤p) : s≤2^512 :=
    from_pair_bound ((h.trans_lt pu).trans_eq sq)
  have small (s : ℕ) (h : s*s-s≤p) : 4*2^509*s≤2^1023 :=
    (Nat.mul_le_mul_left _ (bound s h)).trans_eq fourth
  have h₁ := Nat.mul_le_mul_right q ((small _ split₁).trans pl)
  have h₂ := Nat.mul_le_mul_right q ((small _ split₂).trans pl)
  have h₃ := Nat.mul_le_mul_right p ((small _ (inert.trans (Nat.sub_le _ _))).trans ql)
  have pq := Nat.mul_pos (by omega : 0<p) (by omega : 0<q)
  nlinarith only [h₁,h₂,h₃,pq]

/-- The quadratic power for a unit shift with a nontrivial resultant gcd. -/
theorem example_power {R : Type*} [CommRing R] (w : R)
    (root : w^2+1=0) (modulus : (899:R)=0) : (8+w)^899 = 285+655*w := by
  have p3 : (8+w)^3 = 488+191*w := by
    linear_combination (24+w)*root
  have p7 : (8+w)^7 = 175+174*w := by
    rw [show 7 = 3*2+1 by decide, pow_succ, pow_mul, p3]
    linear_combination (478264+36481*w)*root + (1587+1883*w)*modulus
  have p14 : (8+w)^14 = 349+667*w := by
    rw [show 14 = 7*2 by decide, pow_mul, p7]
    linear_combination 30276*root + (67*w)*modulus
  have p28 : (8+w)^28 = 552+783*w := by
    rw [show 28 = 14*2 by decide, pow_mul, p14]
    linear_combination 444889*root + (-360+517*w)*modulus
  have p56 : (8+w)^56 = 871+493*w := by
    rw [show 56 = 28*2 by decide, pow_mul, p28]
    linear_combination 613089*root + (-344+961*w)*modulus
  have p112 : (8+w)^112 = 465+261*w := by
    rw [show 112 = 56*2 by decide, pow_mul, p56]
    linear_combination 243049*root + (573+955*w)*modulus
  have p224 : (8+w)^224 = 668 := by
    rw [show 224 = 112*2 by decide, pow_mul, p112]
    linear_combination 68121*root + (164+270*w)*modulus
  have p449 : (8+w)^449 = 762+320*w := by
    rw [show 449 = 224*2+1 by decide, pow_succ, pow_mul, p224]
    linear_combination (3970+496*w)*modulus
  rw [show 899 = 449*2+1 by decide, pow_succ, pow_mul, p449]
  linear_combination (1306880+102400*w)*root + (3713+4871*w)*modulus

theorem example_gcd : Nat.gcd ((285-8)^2+(655+1)^2) 899 = 29 ∧
    Nat.Prime 29 ∧ Nat.Prime 31 ∧ (29:ℕ)*31=899 := by decide

end PrimeFactors.FrobeniusShiftCount
