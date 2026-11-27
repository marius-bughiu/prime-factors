import PrimeFactors.ProjectiveWordMoments
import Mathlib.Tactic

/-! # Exact counts of two Jacobi signs with a shared root

Writing the common argument as x, the two discriminants become x(x−4) and x(x+4).
Their first two character moments suffice to count every nonzero sign pair over a
product of two distinct odd primes.
-/

namespace PrimeFactors.NeighboringJacobiSamples
open Finset
noncomputable def J (n : ℕ) (t : ℤ) := jacobiSym (t^2-4) n

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
noncomputable def a (c x : F) := quadraticChar F (x*(x-c))
noncomputable def b (c x : F) := quadraticChar F (x*(x+c))

/-- Local moments of the two signs centered at their common root 0.
    The outputs hold for every nonzero scale in every odd finite field. -/
theorem local_moments (odd : ringChar F ≠ 2) {c : F} (c0 : c≠0) :
    (∑ x:F, a c x ^ 2 * b c x ^ 2) = (Fintype.card F:ℤ)-3 ∧
    (∑ x:F, a c x * b c x ^ 2) = -1-quadraticChar F 2 ∧
    (∑ x:F, a c x ^ 2 * b c x) = -1-quadraticChar F 2 ∧
    (∑ x:F, a c x * b c x) = -1-quadraticChar F (-1) := by
  classical
  have two : (2:F)≠0 := Ring.two_ne_zero odd
  have opposite : c ≠ -c := by
    intro eqn
    apply mul_ne_zero two c0
    linear_combination eqn
  have an (x : F) (x0 : x ≠ 0) (xc : x ≠ c) : a c x ^ 2 = 1 :=
    quadraticChar_sq_one (mul_ne_zero x0 (sub_ne_zero.mpr xc))
  have bn (x : F) (x0 : x ≠ 0) (xc : x ≠ -c) : b c x ^ 2 = 1 :=
    quadraticChar_sq_one (mul_ne_zero x0 (by intro eqn; apply xc; linear_combination eqn))
  have az : a c 0 = 0 := by simp [a]
  have bz : b c 0 = 0 := by simp [b]
  have ac : a c c = 0 := by simp [a]
  have bc : b c (-c) = 0 := by simp [b]
  have ac' : a c (-c) = quadraticChar F 2 := by
    rw [a, show (-c)*(-c-c)=(2:F)*c^2 by ring, map_mul, quadraticChar_sq_one' c0, mul_one]
  have bc' : b c c = quadraticChar F 2 := by
    rw [b, show c*(c+c)=(2:F)*c^2 by ring, map_mul, quadraticChar_sq_one' c0, mul_one]
  have sumA : ∑ x:F, a c x = -1 := by
    simpa only [a, add_zero, sub_eq_add_neg] using
      (PrimeFactors.phaseCharacters_shift_sum odd (a:=0) (b:=-c) (Ne.symm (neg_ne_zero.mpr c0)))
  have sumB : ∑ x:F, b c x = -1 := by
    simpa only [b, add_zero] using (PrimeFactors.phaseCharacters_shift_sum odd (a:=0) (b:=c) c0.symm)
  have leftx (x : F) : a c x * b c x ^ 2 =
      a c x - if x= -c then quadraticChar F 2 else 0 := by
    by_cases z : x=0
    · subst x; simp [az,bz,c0]
    by_cases d : x= -c
    · subst x; simp [bc,ac']
    simp [bn x z d,d]
  have rightx (x : F) : a c x ^ 2 * b c x =
      b c x - if x=c then quadraticChar F 2 else 0 := by
    by_cases z : x=0
    · subst x; simp [az,bz,c0.symm]
    by_cases d : x=c
    · subst x; simp [ac,bc']
    simp [an x z d,d]
  have both (x : F) : a c x ^ 2 * b c x ^ 2 =
      1-(if x=0 then 1 else 0)-(if x=c then 1 else 0)-(if x= -c then 1 else 0) := by
    by_cases z : x=0
    · subst x; simp [az,bz,c0,c0.symm]
    by_cases u : x=c
    · subst x; simp [ac,c0,opposite]
    by_cases v : x= -c
    · subst x; simp [bc,c0,opposite.symm]
    simp [an x z u,bn x z v,z,u,v]
  have pair (x : F) : a c x * b c x =
      quadraticChar F ((x+(-c))*(x+c)) - if x=0 then quadraticChar F (-1) else 0 := by
    by_cases z : x=0
    · subst x
      simp only [az,bz,zero_mul,zero_add,if_true]
      rw [show -c*c = (-1:F)*c^2 by ring,map_mul,quadraticChar_sq_one' c0,mul_one,sub_self]
    rw [a,b,←map_mul,show x*(x-c)*(x*(x+c))=x^2*((x+(-c))*(x+c)) by ring,
        map_mul,quadraticChar_sq_one' z,one_mul,if_neg z,sub_zero]
  refine ⟨?_,?_,?_,?_⟩
  · simp [both,Finset.sum_sub_distrib]; ring
  · simp [leftx,Finset.sum_sub_distrib,sumA]
  · simp [rightx,Finset.sum_sub_distrib,sumB]
  · simp_rw [pair]
    rw [Finset.sum_sub_distrib, PrimeFactors.phaseCharacters_shift_sum odd opposite.symm]
    simp


private theorem crt_sum {p q : ℕ} [NeZero p] [NeZero q] (cop : p.Coprime q)
    (f : ZMod p → ℤ) (g : ZMod q → ℤ) :
    (∑ t : ZMod (p*q), f (ZMod.chineseRemainder cop t).1 * g (ZMod.chineseRemainder cop t).2)
        = (∑ u : ZMod p, f u)*(∑ v : ZMod q, g v) := by
  let e := ZMod.chineseRemainder cop
  calc
    _ = ∑ t : ZMod p × ZMod q, f t.1 * g t.2 := Fintype.sum_equiv e.toEquiv _ _ (fun _ => rfl)
    _ = _ := by rw [Fintype.sum_prod_type]; simp only [← mul_sum, ← sum_mul]

private theorem by_coordinates {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (t : ZMod (p*q)) :
    J (p*q) ((t.val:ℤ)-2) =
       a 4 (ZMod.chineseRemainder cop t).1 * a 4 (ZMod.chineseRemainder cop t).2 ∧
    J (p*q) ((t.val:ℤ)+2) =
       b 4 (ZMod.chineseRemainder cop t).1 * b 4 (ZMod.chineseRemainder cop t).2 := by
  have cast : ZMod.chineseRemainder cop t = ((t.val : ZMod p),(t.val : ZMod q)) := by
    conv_lhs => arg 2; rw [← ZMod.natCast_zmod_val t]
    rw [map_natCast]
    rfl
  constructor
  all_goals
    rw [J,jacobiSym.mul_right, ← jacobiSym.legendreSym.to_jacobiSym, ← jacobiSym.legendreSym.to_jacobiSym,cast]
  · simp only [legendreSym,a,Int.cast_sub,Int.cast_pow,Int.cast_natCast,Int.cast_ofNat]
    congr 2 <;> ring
  · simp only [legendreSym,b,Int.cast_sub,Int.cast_add,Int.cast_pow,Int.cast_natCast,Int.cast_ofNat]
    congr 2 <;> ring

noncomputable def moment (p q i j : ℕ) [Fact p.Prime] [Fact q.Prime] : ℤ :=
   ∑ t : ZMod (p*q), J (p*q) ((t.val:ℤ)-2)^i * J (p*q) ((t.val:ℤ)+2)^j

private theorem moment_crt {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q) (i j : ℕ) :
    moment p q i j = (∑ t:ZMod p, a 4 t ^i * b 4 t ^j) * (∑ t:ZMod q, a 4 t ^i * b 4 t ^j) := by
  unfold moment
  rw [←crt_sum cop]
  apply sum_congr rfl
  intro t _
  rw [(by_coordinates cop t).1,(by_coordinates cop t).2]
  simp only [mul_pow]; ring

noncomputable def bias (z : ℤ) (p q : ℕ) [Fact p.Prime] [Fact q.Prime] : ℤ :=
    (1+quadraticChar (ZMod p) (z:ZMod p))*(1+quadraticChar (ZMod q) (z:ZMod q))

theorem moments {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p ≠ 2) (hq : q ≠ 2) :
    moment p q 2 2 = ((p:ℤ)-3)*((q:ℤ)-3) ∧
    moment p q 1 2 = bias 2 p q ∧ moment p q 2 1 = bias 2 p q ∧
    moment p q 1 1 = bias (-1) p q := by
  have local4 {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) :=
    local_moments (F:=ZMod l) (c:=4) (by rwa [ZMod.ringChar_zmod_n]) (by
      have h : (2:ZMod l) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
      simpa only [show (4:ZMod l) = 2*2 by ring] using mul_ne_zero h h)
  obtain ⟨ap,bp,cp,dp⟩ := local4 hp
  obtain ⟨aq,bq,cq,dq⟩ := local4 hq
  simp only [moment_crt cop,pow_one,ap,bp,cp,dp,aq,bq,cq,dq,bias,ZMod.card,
    Int.cast_ofNat,Int.cast_neg,Int.cast_one]
  constructor <;> try (constructor <;> try constructor) <;> ring

noncomputable def cells (n : ℕ) [NeZero n] (u v : ℤ) : ℕ :=
  (univ.filter (fun t : ZMod n => J n ((t.val:ℤ)-2) = u ∧ J n ((t.val:ℤ)+2) = v)).card

/-- Counts each of the four nonzero sign patterns using only the two local character bits. -/
theorem histogram {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p ≠ 2) (hq : q ≠ 2) {u v : ℤ} (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) :
    4*(cells (p*q) u v : ℤ) = ((p:ℤ)-3)*((q:ℤ)-3)+(u+v)*bias 2 p q+u*v*bias (-1) p q := by
  classical
  have indicator {a b u v : ℤ} (ha : a=0 ∨ a=1 ∨ a= -1) (hb : b=0 ∨ b=1 ∨ b= -1)
      (us : u=1 ∨ u= -1) (vs : v=1 ∨ v= -1) :
      (if a=u ∧ b=v then (4:ℤ) else 0) = a^2*b^2 + u*(a*b^2) + v*(a^2*b) + (u*v)*(a*b) := by
    rcases ha with h|h|h <;> rcases hb with e|e|e <;> rcases us with f|f <;> rcases vs with g|g <;> subst_vars <;> decide
  have point (t : ZMod (p*q)) := indicator
    (jacobiSym.trichotomy (((t.val:ℤ)-2)^2-4) (p*q)) (jacobiSym.trichotomy (((t.val:ℤ)+2)^2-4) (p*q)) hu hv
  change ∀ t : ZMod (p*q), (if J (p*q) ((t.val:ℤ)-2)=u ∧ J (p*q) ((t.val:ℤ)+2)=v then (4:ℤ) else 0) = _ at point
  have h := Finset.sum_congr (rfl : (univ : Finset (ZMod (p*q))) = univ) (fun x _ => point x)
  simp only [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, nsmul_eq_mul,
    add_zero, Finset.sum_add_distrib, ←Finset.mul_sum] at h
  obtain ⟨h22,h12,h21,h11⟩ := moments cop hp hq
  unfold moment at h22 h12 h21 h11
  simp only [pow_one] at h12 h21 h11
  change ((cells (p*q) u v:ℤ)*4) = _ at h
  change _ = (∑ t : ZMod (p*q), J (p*q) ((t.val:ℤ)-2)^2 * J (p*q) ((t.val:ℤ)+2)^2) +
      u*(∑ t : ZMod (p*q), J (p*q) ((t.val:ℤ)-2) * J (p*q) ((t.val:ℤ)+2)^2) +
      v*(∑ t : ZMod (p*q), J (p*q) ((t.val:ℤ)-2)^2 * J (p*q) ((t.val:ℤ)+2)) +
      (u*v)*(∑ t : ZMod (p*q), J (p*q) ((t.val:ℤ)-2) * J (p*q) ((t.val:ℤ)+2)) at h
  rw [h22,h12,h21,h11] at h
  linear_combination h

private theorem local_squares {c : F} (c0 : c≠0) :
    (∑ x : F, a c x ^ 2) = (Fintype.card F : ℤ)-2 ∧
    (∑ x : F, b c x ^ 2) = (Fintype.card F : ℤ)-2 := by
  have loc {c : F} (h : c≠0) : ∑ x : F, a c x ^ 2 = (Fintype.card F : ℤ)-2 := by
    have at_x (x : F) : a c x ^ 2 = 1-(if x=0 then 1 else 0)-(if x=c then 1 else 0) := by
      by_cases z : x=0
      · subst x; simp [a,h.symm]
      by_cases e : x=c
      · subst x; simp [a,h]
      rw [if_neg z,if_neg e,sub_zero,sub_zero]
      exact quadraticChar_sq_one (mul_ne_zero z (sub_ne_zero.mpr e))
    simp_rw [at_x]
    simp [sum_sub_distrib]; ring
  exact ⟨loc c0, by simpa only [a,b,sub_neg_eq_add] using loc (neg_ne_zero.mpr c0)⟩

/-- The simultaneous-zero count yields p+q after subtracting one. -/
theorem both_zero {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : p ≠ 2) (hq : q ≠ 2) : cells (p*q) 0 0 = p+q+1 := by
  have marg {l : ℕ} [Fact l.Prime] (hl : l≠2) :=
    local_squares (F:=ZMod l) (c:=4) (by
      have h : (2:ZMod l) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
      simpa only [show (4:ZMod l) = 2*2 by ring] using mul_ne_zero h h)
  obtain ⟨ap,bp⟩ := marg hp
  obtain ⟨aq,bq⟩ := marg hq
  have mx := moment_crt cop 2 0
  have my := moment_crt cop 0 2
  simp only [pow_zero,mul_one,one_mul,ap,bp,aq,bq,ZMod.card] at mx my
  have both := (moments cop hp hq).1
  unfold moment at mx my both
  simp only [pow_zero,mul_one,one_mul] at mx my
  have zero {x y : ℤ} (hx : x=0 ∨ x=1 ∨ x= -1) (hy : y=0 ∨ y=1 ∨ y= -1) :
      (if x=0 ∧ y=0 then (1:ℤ) else 0) = 1-x^2-y^2+x^2*y^2 := by
    rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl <;> decide
  have val (t : ZMod (p*q)) := zero (jacobiSym.trichotomy (((t.val:ℤ)-2)^2-4) (p*q))
       (jacobiSym.trichotomy (((t.val:ℤ)+2)^2-4) (p*q))
  have tally := sum_congr (rfl : (univ : Finset (ZMod (p*q)))=univ) (fun t _ => val t)
  simp only [sum_boole,sum_add_distrib,sum_sub_distrib,sum_const,card_univ,ZMod.card,
    nsmul_eq_mul,mul_one,Nat.cast_mul] at tally
  change (cells (p*q) 0 0 : ℤ) = (p:ℤ)*q - (∑ t : ZMod (p*q), J (p*q) ((t.val:ℤ)-2)^2) -
      (∑ t : ZMod (p*q), J (p*q) ((t.val:ℤ)+2)^2) +
      (∑ t : ZMod (p*q), J (p*q) ((t.val:ℤ)-2)^2 * J (p*q) ((t.val:ℤ)+2)^2) at tally
  rw [mx,my,both] at tally
  exact_mod_cast (show (cells (p*q) 0 0:ℤ) = (p:ℤ)+q+1 by linarith)

end PrimeFactors.NeighboringJacobiSamples
