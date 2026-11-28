import PrimeFactors.QuarticOddLocalPoints
import PrimeFactors.QuarticTwoLocalPoints
import Mathlib.Data.Nat.Factorization.Induction

/-! Classification of the finite congruence tests for the cleared quartic.
At a prime dividing the modulus, at least one numerator coordinate is a unit.
The positive denominator can vary with the modulus. -/
namespace PrimeFactors.QuarticLocalClassification

def Point (n m : ℕ) : Prop := ∃ a b d : ℕ, 0<d ∧
  (∀ p, p.Prime → p∣m → ¬p∣a ∨ ¬p∣b) ∧ a^4+4*b^4 ≡ n*d^4 [MOD m]

def Tests (n : ℕ) := ∀ m>0,Point n m

private theorem transport {a b d x y z n m : ℕ} (hx : x ≡ a [MOD m])
    (hy : y ≡ b [MOD m]) (hz : z ≡ d [MOD m])
    (ok : a^4+4*b^4 ≡ n*d^4 [MOD m]) : x^4+4*y^4 ≡ n*z^4 [MOD m] :=
  (((hx.pow 4).add ((hy.pow 4).mul_left 4)).trans ok).trans ((hz.pow 4).mul_left n).symm

private theorem crt {n h k : ℕ} (hp : 0<h) (kp : 0<k) (cop : h.Coprime k)
    (left : Point n h) (right : Point n k) : Point n (h*k) := by
  obtain ⟨a,b,d,_,lu,leq⟩ := left
  obtain ⟨u,v,t,_,ru,req⟩ := right
  let x := Nat.chineseRemainder cop a u
  let y := Nat.chineseRemainder cop b v
  let z := Nat.chineseRemainder cop d t
  have dh : z.val+h*k ≡ d [MOD h] := by
    simpa only [add_zero] using z.property.1.add (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right h k))
  have dk : z.val+h*k ≡ t [MOD k] := by
    simpa only [add_zero] using z.property.2.add (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left k h))
  refine ⟨x.val,y.val,z.val+h*k,Nat.add_pos_right _ (Nat.mul_pos hp kp),?_,
    (Nat.modEq_and_modEq_iff_modEq_mul cop).mp
      ⟨transport x.property.1 y.property.1 dh leq,transport x.property.2 y.property.2 dk req⟩⟩
  intro p prime div
  rcases prime.dvd_mul.mp div with l|r
  · exact (lu p prime l).imp (mt (x.property.1.dvd_iff l).mp) (mt (y.property.1.dvd_iff l).mp)
  · exact (ru p prime r).imp (mt (x.property.2.dvd_iff r).mp) (mt (y.property.2.dvd_iff r).mp)

private theorem prime_power {n p e : ℕ} (prime : p.Prime)
    (h : QuarticOddLocalPoints.Local n p e) : Point n (p^e) := by
  obtain ⟨a,b,d,dp,unit,form⟩ := h
  refine ⟨a,b,d,dp,?_,form⟩
  intro r rp div
  have eq := (Nat.prime_dvd_prime_iff_eq rp prime).mp (rp.dvd_of_dvd_pow div)
  exact eq.symm ▸ unit

theorem all_iff {n : ℕ} (odd : Odd n) : Tests n ↔
    (n%16=1 ∨ n%16=5) ∧ ∀ p, p.Prime → p∣n → p%4=1 := by
  constructor
  · intro ok
    obtain ⟨a,b,d,_,unit,form⟩ := ok 16 (by decide)
    refine ⟨QuarticTwoLocalPoints.class_of_mod16 odd (unit 2 Nat.prime_two (by decide)) form,?_⟩
    intro p prime div
    have other : p≠2 := by rintro rfl; exact (Nat.not_even_iff_odd.mpr odd) (even_iff_two_dvd.mpr div)
    have mod4 : p%4=1 ∨ p%4=3 := by
      have parity := prime.eq_two_or_odd.resolve_left other
      omega
    rcases mod4 with good|bad
    · exact good
    obtain ⟨x,y,z,_,unit,point⟩ := ok p prime.pos
    have both := QuarticOddLocalPoints.inert_coordinates prime bad div point
    exact False.elim ((unit p prime dvd_rfl).elim (fun h => h both.1) (fun h => h both.2))
  · rintro ⟨good,support⟩ m
    induction m using Nat.recOnPrimeCoprime with
    | h0 => omega
    | hp p e prime =>
      intro _
      apply prime_power prime
      by_cases two : p=2
      · subst p
        obtain ⟨a,b,ap,_,eq⟩ := QuarticTwoLocalPoints.affine_point good e
        exact ⟨a,b,1,by decide,Or.inl (fun div => (Nat.not_even_iff_odd.mpr ap) (even_iff_two_dvd.mpr div)),
          by simpa only [one_pow,mul_one] using eq⟩
      · apply (QuarticOddLocalPoints.all_iff prime two).mpr _ e
        by_cases div : p∣n
        · exact Or.inl (support p prime div)
        · exact Or.inr div
    | h a b ha hb cop l r => exact fun _ => crt (by omega) (by omega) cop (l (by omega)) (r (by omega))

/-- On a semiprime the only odd-prime local obstructions are the residue
classes of its two factors. Checking the product modulo 16 requires no factors. -/
theorem semiprime {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (po : Odd p) (qo : Odd q) :
    Tests (p*q) ↔ p%4=1 ∧ q%4=1 ∧ ((p*q)%16=1 ∨ (p*q)%16=5) := by
  rw [all_iff (po.mul qo)]
  constructor
  · exact fun ⟨four,s⟩ => ⟨s p pp (dvd_mul_right p q),s q qp (dvd_mul_left q p),four⟩
  · rintro ⟨a,b,good⟩
    refine ⟨good,?_⟩
    intro l lp div
    rcases lp.dvd_mul.mp div with left|right
    · exact (Nat.prime_dvd_prime_iff_eq lp pp).mp left ▸ a
    · exact (Nat.prime_dvd_prime_iff_eq lp qp).mp right ▸ b

/-- Four products of two six-bit primes. 2501 and 2773 have the same
remainder modulo sixteen but opposite results over all moduli. -/
theorem examples : Tests 2501 ∧ ¬Tests 2773 ∧ ¬Tests 2173 ∧ Tests 2257 := by
  have at_pair (p q : ℕ) (pp : p.Prime) (qp : q.Prime) (oddP : Odd p) (oddQ : Odd q) :=
    semiprime pp qp oddP oddQ
  exact ⟨(at_pair 41 61 (by decide) (by decide) (by decide) (by decide)).mpr (by decide),
    fun h => (by decide : ¬((47:ℕ)%4=1)) ((at_pair 47 59 (by decide) (by decide) (by decide) (by decide)).mp h).1,
    fun h => (by decide : ¬(((41*53:ℕ)%16=1) ∨ (41*53:ℕ)%16=5))
      ((at_pair 41 53 (by decide) (by decide) (by decide) (by decide)).mp h).2.2,
    (at_pair 37 61 (by decide) (by decide) (by decide) (by decide)).mpr (by decide)⟩

/-- For 2257 the local condition is satisfied but even zero coordinates
cannot give an integral representation at denominator one. -/
theorem integer_examples : 2501=1^4+4*5^4 ∧ ¬∃ x y : ℕ, x^4+4*y^4=2257 := by
  refine ⟨by decide,?_⟩
  rintro ⟨x,y,eq⟩
  have xl : x<7 := by
    by_contra! h
    have := Nat.pow_le_pow_left h 4
    omega
  have yl : y<5 := by
    by_contra! h
    have := Nat.pow_le_pow_left h 4
    omega
  have table : ∀ a : Fin 7, ∀ b : Fin 5, a.val^4+4*b.val^4≠2257 := by decide +kernel
  exact table ⟨x,xl⟩ ⟨y,yl⟩ eq

end PrimeFactors.QuarticLocalClassification
