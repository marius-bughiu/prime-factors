import PrimeFactors.DiscriminantPencil
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.LinearCombination

namespace PrimeFactors

/-- In the balanced Fermat window the square part of a discriminant is
small compared with its midpoint. -/
private theorem midpoint_class_small {n d h z : ℕ} (hd : 0 < d)
    (eqn : h^2 = n+d*z^2) (bound : 8*h^2 ≤ 9*n) : 3*z ≤ h := by
  apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
  have hz := Nat.mul_le_mul_right (z^2) (show 1 ≤ d by omega)
  nlinarith only [eqn, bound, hz]

/-- The sum of the two cross products lies strictly below the modulus. -/
private theorem midpoint_cross_small {n d a b u v : ℕ} (hn : 0 < n) (hd : 0 < d)
    (ha : a^2=n+d*u^2) (hb : b^2=n+d*v^2)
    (ba : 8*a^2 ≤ 9*n) (bb : 8*b^2 ≤ 9*n) : a*v+b*u < n := by
  have hu := midpoint_class_small hd ha ba
  have hv := midpoint_class_small hd hb bb
  have h₁ := Nat.mul_le_mul_left a hv
  have h₂ := Nat.mul_le_mul_left b hu
  have amgm : 2*a*b ≤ a^2+b^2 := by
    rcases le_total a b with h | h
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le h
      nlinarith only [Nat.zero_le (k^2)]
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le h
      nlinarith only [Nat.zero_le (k^2)]
  nlinarith only [h₁,h₂,amgm,ba,bb,hn]

private theorem midpoint_cross_equal {n d a b u v : ℕ} (hn : 0 < n)
    (ha : a^2=n+d*u^2) (hb : b^2=n+d*v^2) (same : a*v=b*u) : a=b := by
  have h := congrArg (·^2) same
  simp only [mul_pow,ha,hb] at h
  have z : n*v^2=n*u^2 := by nlinarith only [h]
  have vu := Nat.eq_of_mul_eq_mul_left hn z
  have squares : a^2=b^2 := by rw [ha,hb,vu]
  exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp squares

/-- A witness for a square class has invertible denominator at either
prime of a squarefree semiprime. -/
private theorem midpoint_unit {p q d a u : ℕ} (hp : p.Prime) (other : ¬p ∣ q)
    (ha : a^2=p*q+d*u^2) : (u : ZMod p) ≠ 0 := by
  intro zero
  have pu := (ZMod.natCast_zmod_eq_zero_iff_dvd u p).mp zero
  obtain ⟨v,rfl⟩ := pu
  have pa : p ∣ a^2 := ha ▸ dvd_add (dvd_mul_right p q)
    (dvd_mul_of_dvd_right (dvd_pow (dvd_mul_right p v) (by decide : 2 ≠ 0)) _)
  obtain ⟨b,rfl⟩ := hp.dvd_of_dvd_pow pa
  have eqn : p*(p*b^2)=p*(q+p*(d*v^2)) := by nlinarith only [ha]
  have eq' := Nat.eq_of_mul_eq_mul_left hp.pos eqn
  have dvd : p ∣ q+p*(d*v^2) := eq' ▸ dvd_mul_right p (b^2)
  exact other ((Nat.dvd_add_iff_left (dvd_mul_right p (d*v^2))).mpr dvd)

private theorem midpoint_slope {p q d a u : ℕ} [Fact p.Prime]
    (ha : a^2=p*q+d*u^2) (unit : (u : ZMod p) ≠ 0) :
    ((a : ZMod p)/u)^2 = d := by
  have cast := congrArg (fun v : ℕ => (v : ZMod p)) ha
  push_cast at cast
  simp only [ZMod.natCast_self,zero_mul,zero_add] at cast
  rw [div_pow,cast, mul_div_cancel_right₀ _ (pow_ne_zero _ unit)]

/-- In the public balanced interval each positive square class of h²−pq
occurs at most twice. The integer d itself need not be squarefree. -/
theorem midpoint_class_card_le_two {p q d : ℕ} (hp : p.Prime) (hq : q.Prime) (ne : p≠q)
    (hd : 0 < d) (s : Finset ℕ) (z : ℕ → ℕ)
    (inside : ∀ h ∈ s, h^2=p*q+d*(z h)^2 ∧ 0 < z h ∧ 8*h^2 ≤ 9*(p*q)) :
    s.card ≤ 2 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  have cop := (Nat.coprime_primes hp hq).mpr ne
  let A (x : ℕ) := (x : ZMod p)/(z x : ℕ)
  let B (x : ℕ) := (x : ZMod q)/(z x : ℕ)
  have podat {x : ℕ} (hx : x ∈ s) : (z x : ZMod p) ≠ 0 ∧ (A x)^2=d := by
    have H := (inside x hx).1
    have u := midpoint_unit hp (hp.coprime_iff_not_dvd.mp cop) H
    exact ⟨u,midpoint_slope H u⟩
  have qdat {x : ℕ} (hx : x ∈ s) : (z x : ZMod q) ≠ 0 ∧ (B x)^2=d := by
    have H := (inside x hx).1
    rw [mul_comm p q] at H
    have u := midpoint_unit hq (hq.coprime_iff_not_dvd.mp cop.symm) H
    exact ⟨u,midpoint_slope H u⟩
  rcases s.eq_empty_or_nonempty with empty | ⟨base,hbase⟩
  · simp [empty]
  -- Choose the sign at p; the remaining coordinate has only two choices.
  let key (x : ℕ) := if A x = A base then B x else -B x
  have sign {x : ℕ} (hx : x ∈ s) : A x = A base ∨ A x = -A base :=
    sq_eq_sq_iff_eq_or_eq_neg.mp ((podat hx).2.trans (podat hbase).2.symm)
  have signB {x : ℕ} (hx : x ∈ s) : B x = B base ∨ B x = -B base :=
    sq_eq_sq_iff_eq_or_eq_neg.mp ((qdat hx).2.trans (qdat hbase).2.symm)
  have two : (insert (-B base) ({B base} : Finset (ZMod q))).card ≤ 2 :=
    (Finset.card_insert_le _ _).trans (by simp)
  apply le_trans _ two
  apply Finset.card_le_card_of_injOn key
  · intro x hx
    by_cases same : A x = A base <;> rcases signB hx with h|h <;> simp [key,h,same]
  · intro x hx y hy heq
    have data : (A x=A y ∧ B x=B y) ∨ (A x= -A y ∧ B x= -B y) := by
      by_cases a : A x=A base <;> by_cases b : A y=A base
      · exact Or.inl ⟨a.trans b.symm,by simpa [key,a,b] using heq⟩
      · have by' := (sign hy).resolve_left b
        exact Or.inr ⟨by rw [a,by',neg_neg],by simpa [key,a,b] using heq⟩
      · have ax := (sign hx).resolve_left a
        exact Or.inr ⟨by rw [ax,b],by simpa [key,a,b, neg_eq_iff_eq_neg] using heq⟩
      · exact Or.inl ⟨((sign hx).resolve_left a).trans ((sign hy).resolve_left b).symm,
          by simpa [key,a,b] using heq⟩
    have hn := Nat.mul_pos hp.pos hq.pos
    have ⟨ex,ux,bx⟩ := inside x hx
    have ⟨ey,uy,by'⟩ := inside y hy
    have bound := midpoint_cross_small hn hd ex ey bx by'
    rcases data with ⟨ap,bq⟩|⟨ap,bq⟩
    · have cross {m : ℕ} [Fact m.Prime] (zx : (z x : ZMod m) ≠ 0) (zy : (z y : ZMod m) ≠ 0)
          (h : (x : ZMod m)/z x=(y : ZMod m)/z y) : x*z y ≡ y*z x [MOD m] := by
        apply (ZMod.natCast_eq_natCast_iff ..).mp
        push_cast
        exact (div_eq_div_iff zx zy).mp h
      have eq := (Nat.modEq_and_modEq_iff_modEq_mul cop).mp ⟨cross (podat hx).1 (podat hy).1 ap,
        cross (qdat hx).1 (qdat hy).1 bq⟩
      exact midpoint_cross_equal hn ex ey (eq.eq_of_lt_of_lt (by omega) (by omega))
    · have cross {m : ℕ} [Fact m.Prime] (zx : (z x : ZMod m) ≠ 0) (zy : (z y : ZMod m) ≠ 0)
          (h : (x : ZMod m)/z x= -((y : ZMod m)/z y)) : m ∣ x*z y+y*z x := by
        apply (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp
        push_cast
        rw [← neg_div] at h
        have := (div_eq_div_iff zx zy).mp h
        linear_combination this
      have dvd := cop.mul_dvd_of_dvd_of_dvd (cross (podat hx).1 (podat hy).1 ap)
        (cross (qdat hx).1 (qdat hy).1 bq)
      have xpos : 0 < x := by
        apply Nat.pos_of_ne_zero
        intro zero
        rw [zero,zero_pow (by decide : 2 ≠ 0)] at ex
        omega
      exact (Nat.not_dvd_of_pos_of_lt (by positivity : 0 < x*z y+y*z x) bound dvd).elim

end PrimeFactors
