import PrimeFactors.InverseCyclotomicMeasurements
import PrimeFactors.QuarticLocalSquareCriterion

/-! The single value at i has only three possibilities on odd semiprimes.
Its sign distinguishes the two-squares predicate and gives the prime sum
modulo eight together with the public product. -/
namespace PrimeFactors.CyclotomicGaussianReading

open Polynomial Complex InverseCyclotomicMeasurements

noncomputable def reading (N : ℕ) : ℂ :=
  (polynomial N).eval₂ (Int.castRingHom ℂ) I

private theorem odd_classes {n : ℕ} (odd : Odd n) : n%4=1 ∨ n%4=3 := by
  obtain ⟨k,h⟩ := odd
  omega

theorem value {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p<q)
    (op : Odd p) (oq : Odd q) :
    reading (p*q) = if p%4=1 ∧ q%4=1 then -2*I else
      if p%4=3 ∧ q%4=3 then 2*I else 2 := by
  rw [reading,sparse pp qp ord]
  simp only [eval₂_mul,eval₂_sub,eval₂_one,eval₂_pow,eval₂_X,
    I_pow_eq_pow_mod p,I_pow_eq_pow_mod q]
  rcases odd_classes op with a|a <;> rcases odd_classes oq with b|b <;>
    norm_num [a,b,Complex.ext_iff,Complex.mul_re,Complex.mul_im]

/-- For odd semiprimes, a negative imaginary reading is equivalent to
the existence of a square root of -1 modulo the product. -/
theorem negative_iff_square {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p<q)
    (op : Odd p) (oq : Odd q) :
    reading (p*q) = -2*I ↔ IsSquare (-1 : ZMod (p*q)) := by
  rw [value pp qp ord op oq,QuarticLocalSquareCriterion.square_iff (op.mul oq)]
  have support : (∀ r, Nat.Prime r → r∣p*q → r%4=1) ↔ p%4=1 ∧ q%4=1 := by
    constructor
    · intro h
      exact ⟨h p pp (dvd_mul_right p q),h q qp (dvd_mul_left q p)⟩
    · rintro ⟨a,b⟩ r prime divides
      rcases prime.dvd_mul.mp divides with rp|rq
      · exact ((Nat.prime_dvd_prime_iff_eq prime pp).mp rp) ▸ a
      · exact ((Nat.prime_dvd_prime_iff_eq prime qp).mp rq) ▸ b
  rw [support]
  split_ifs <;> norm_num [*,Complex.ext_iff]

theorem negative_iff_two_squares {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p<q)
    (op : Odd p) (oq : Odd q) :
    reading (p*q) = -2*I ↔ ∃ a b : ℕ, p*q=a^2+b^2 := by
  rw [negative_iff_square pp qp ord op oq]
  refine ⟨Nat.eq_sq_add_sq_of_isSquare_mod_neg_one,?_⟩
  intro h
  obtain ⟨a,b,eq,square⟩ := Nat.eq_sq_add_sq_iff_eq_sq_mul.mp h
  have sf := (Nat.squarefree_mul ((Nat.coprime_primes pp qp).mpr ord.ne)).mpr
    ⟨pp.squarefree,qp.squarefree⟩
  have unit : IsUnit a := sf a ⟨b,by simpa [sq] using eq⟩
  rw [Nat.isUnit_iff.mp unit,one_pow,one_mul] at eq
  exact eq ▸ square

/-- The ordinary product remainder and the sign of the supplied Gaussian
reading give the sum of the two primes modulo eight. -/
noncomputable def sumResidue (N : ℕ) (y : ℂ) : ℕ :=
  if y=2*I then (3*(N+1))%8 else (N+1)%8

private theorem residue_table (p q : ℕ) (op : Odd p) (oq : Odd q) :
    (p+q)%8 = (if p%4=3 ∧ q%4=3 then 3*(p*q+1) else p*q+1)%8 := by
  have h : ∀ a b : Fin 8, a.val%2=1 → b.val%2=1 →
      (a.val+b.val)%8=(if a.val%4=3 ∧ b.val%4=3 then 3*(a.val*b.val+1) else a.val*b.val+1)%8 := by
    decide +kernel
  have t := h ⟨p%8,Nat.mod_lt _ (by decide)⟩ ⟨q%8,Nat.mod_lt _ (by decide)⟩
  simp only [Nat.mod_mod_of_dvd _ (by decide : 2∣8),Nat.mod_mod_of_dvd _ (by decide : 4∣8),
    Nat.odd_iff.mp op,Nat.odd_iff.mp oq,forall_const] at t
  have pm := Nat.mod_modEq p 8
  have qm := Nat.mod_modEq q 8
  have plus := (pm.mul qm).add (Nat.ModEq.refl 1)
  by_cases both : p%4=3 ∧ q%4=3
  · rw [if_pos both] at t ⊢
    exact (pm.add qm).symm.trans ((show _ ≡ _ [MOD 8] from t).trans (plus.mul_left 3))
  · rw [if_neg both] at t ⊢
    exact (pm.add qm).symm.trans ((show _ ≡ _ [MOD 8] from t).trans plus)

theorem sum_mod_eight {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p<q)
    (op : Odd p) (oq : Odd q) : sumResidue (p*q) (reading (p*q))=(p+q)%8 := by
  rw [sumResidue,value pp qp ord op oq,residue_table p q op oq]
  rcases odd_classes op with a|a <;> rcases odd_classes oq with b|b <;>
    norm_num [a,b,Complex.ext_iff]

/-- The products share eight low bits and both have two seven-bit primes. -/
theorem matched : 9017%256=8249%256 ∧ reading 9017=2*I ∧ reading 8249= -2*I ∧
    (71+127)%8=6 ∧ (73+113)%8=2 ∧ 8249=32^2+85^2 ∧
    ¬∃ a b : ℕ, 9017=a^2+b^2 := by
  have x := value (p:=71) (q:=127) (by decide) (by decide) (by decide) (by decide) (by decide)
  have y := value (p:=73) (q:=113) (by decide) (by decide) (by decide) (by decide) (by decide)
  norm_num at x y
  refine ⟨by decide,x,by simpa only [neg_mul] using y,by decide,by decide,by decide,?_⟩
  intro h
  have bad := (negative_iff_two_squares (p:=71) (q:=127) (by decide) (by decide)
    (by decide) (by decide) (by decide)).mpr h
  change reading 9017= -2*I at bad
  rw [x] at bad
  norm_num [Complex.ext_iff] at bad

end PrimeFactors.CyclotomicGaussianReading
