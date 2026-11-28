import PrimeFactors.QuarticLocalClassification

/-! For a product passing the test modulo sixteen, a single modulus rejects
precisely when its gcd with the product has a prime divisor equal to three
modulo four. The same description applies to every odd modulus. -/
namespace PrimeFactors.QuarticSingleModulus

open QuarticLocalClassification
open private PrimeFactors.QuarticLocalClassification.prime_power
  PrimeFactors.QuarticLocalClassification.crt from PrimeFactors.QuarticLocalClassification

private theorem one (n : ℕ) : Point n 1 := by
  exact ⟨1,0,1,by decide,fun p hp _ => Or.inl hp.not_dvd_one,by simp [Nat.ModEq,Nat.mod_one]⟩

private theorem common_odd {n m p : ℕ} (two : Odd m ∨ n%16=1 ∨ n%16=5)
    (pm : p∣m) (pn : p∣n) : p≠2 := by
  rintro rfl
  rcases two with odd | h | h
  · exact (Nat.not_even_iff_odd.mpr odd) (even_iff_two_dvd.mpr pm)
  · omega
  · omega

/-- If the input passes modulo sixteen, or the modulus is odd, only
primes common to the modulus and the input enter the remaining test. -/
theorem point_iff {n m : ℕ} (pos : 0<m) (two : Odd m ∨ n%16=1 ∨ n%16=5) :
    Point n m ↔ ∀ p, p.Prime → p∣m → p∣n → p%4=1 := by
  constructor
  · rintro ⟨a,b,d,_,primitive,form⟩ p prime pm pn
    by_contra bad
    have parity := prime.eq_two_or_odd.resolve_left (common_odd two pm pn)
    have both := QuarticOddLocalPoints.inert_coordinates prime (by omega) pn (form.of_dvd pm)
    exact (primitive p prime pm).elim (fun u => u both.1) (fun u => u both.2)
  · intro support
    suffices build : ∀ t, t∣m → 0<t → Point n t from build m dvd_rfl pos
    intro t
    induction t using Nat.recOnPrimeCoprime with
    | h0 => omega
    | hp p e prime =>
      intro div _
      cases e with
      | zero => simpa only [pow_zero] using one n
      | succ e =>
        have pm := (dvd_pow_self p (Nat.succ_ne_zero e)).trans div
        apply PrimeFactors.QuarticLocalClassification.prime_power prime
        by_cases eq : p=2
        · subst p
          have good := two.resolve_left (fun odd =>
            (Nat.not_even_iff_odd.mpr odd) (even_iff_two_dvd.mpr pm))
          obtain ⟨a,b,odd,_,hit⟩ := QuarticTwoLocalPoints.affine_point good (e+1)
          exact ⟨a,b,1,by decide,Or.inl (fun pa =>
            (Nat.not_even_iff_odd.mpr odd) (even_iff_two_dvd.mpr pa)),by simpa using hit⟩
        · apply (QuarticOddLocalPoints.all_iff prime eq).mpr _ (e+1)
          by_cases pn : p∣n
          · exact Or.inl (support p prime pm pn)
          · exact Or.inr pn
    | h a b ha hb cop left right =>
      intro div _
      exact PrimeFactors.QuarticLocalClassification.crt (by omega) (by omega) cop
        (left ((dvd_mul_right a b).trans div) (by omega))
        (right ((dvd_mul_left b a).trans div) (by omega))

/-- The gcd contains an inert prime exactly when the modulus rejects. -/
theorem failure_iff {n m : ℕ} (pos : 0<m) (two : Odd m ∨ n%16=1 ∨ n%16=5) :
    ¬Point n m ↔ ∃ p, p.Prime ∧ p∣m.gcd n ∧ p%4=3 := by
  rw [point_iff pos two]
  constructor
  · intro bad
    push_neg at bad
    obtain ⟨p,prime,pm,pn,fail⟩ := bad
    have parity := prime.eq_two_or_odd.resolve_left (common_odd two pm pn)
    exact ⟨p,prime,Nat.dvd_gcd pm pn,by omega⟩
  · rintro ⟨p,prime,dvd,inert⟩ support
    have good := support p prime (dvd.trans (Nat.gcd_dvd_left m n))
      (dvd.trans (Nat.gcd_dvd_right m n))
    omega

theorem coprime_passes {n m : ℕ} (pos : 0<m) (two : Odd m ∨ n%16=1 ∨ n%16=5)
    (cop : m.Coprime n) : Point n m := by
  apply (point_iff pos two).mpr
  intro p prime pm pn
  exact ((Nat.Prime.not_coprime_iff_dvd.mpr ⟨p,prime,pm,pn⟩) cop).elim

/-- A failing positive modulus smaller than the input exhibits a proper
common divisor. The gcd can be calculated directly from the two integers. -/
theorem failure_gcd {n m : ℕ} (pos : 0<m) (below : m<n)
    (two : Odd m ∨ n%16=1 ∨ n%16=5) (fail : ¬Point n m) :
    1<m.gcd n ∧ m.gcd n<n ∧ m.gcd n∣n := by
  obtain ⟨p,prime,pd,_⟩ := (failure_iff pos two).mp fail
  exact ⟨prime.one_lt.trans_le (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left n pos) pd),
    (Nat.gcd_le_left n pos).trans_lt below,Nat.gcd_dvd_right ..⟩

/-- The product 47·59 passes at sixteen and fails at 47. -/
theorem example_2773 : Point 2773 16 ∧ ¬Point 2773 47 ∧ Nat.gcd 47 2773=47 := by
  have good : 2773%16=1 ∨ 2773%16=5 := by decide
  exact ⟨coprime_passes (by decide) (Or.inr good) (by decide),
    (failure_iff (by decide) (Or.inr good)).mpr ⟨47,by decide,by decide,by decide⟩,by decide⟩

end PrimeFactors.QuarticSingleModulus
