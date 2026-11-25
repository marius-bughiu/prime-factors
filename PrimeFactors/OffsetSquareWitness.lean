import PrimeFactors.OffsetSquareSplit

namespace PrimeFactors.OffsetSquareWitness
open CompleteOffsetSearch OffsetSquareSplit

private theorem coprime_of_factors {A B C L : ℕ} (cop : A.Coprime B)
    (ca : C ∣ A) (lb : L ∣ B) : C.Coprime L := by
  apply Nat.coprime_of_dvd
  intro l prime lc ll
  exact prime.not_dvd_one (cop.gcd_eq_one ▸ Nat.dvd_gcd (lc.trans ca) (ll.trans lb))

/-- Assign p to A and q to B. Coprimality of A and B makes their remaining
coefficients coprime squares and makes their positive square roots primitive. -/
private theorem oriented {p q T j k A B : ℕ} (pp : 0<p) (qp : 0<q) (kp : 0<k)
    (cop : A.Coprime B) (pa : p∣A) (qb : q∣B)
    (sum : A+B=j+2*T*k) (prod : A*B=(p*q)*k^2) :
    ∃ s v : ℕ, 0<s ∧ 0<v ∧ s.Coprime v ∧ k=s*v ∧ j+2*T*k=p*s^2+q*v^2 := by
  obtain ⟨C,ac⟩ := pa
  obtain ⟨L,bl⟩ := qb
  have pair : C*L=k^2 := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos pp qp)
    (calc (p*q)*(C*L)=(p*C)*(q*L) := by ring
          _=(p*q)*k^2 := by rwa [←ac,←bl])
  have cc : C.Coprime L := coprime_of_factors cop (ac ▸ dvd_mul_left C p) (bl ▸ dvd_mul_left L q)
  obtain ⟨s,v,sp,vp,ks,sc,lv⟩ := square_coefficients kp cc pair
  have prim : s.Coprime v := coprime_of_factors cc (sc ▸ dvd_pow_self s (by decide : 2≠0))
    (lv ▸ dvd_pow_self v (by decide : 2≠0))
  exact ⟨s,v,sp,vp,prim,ks,by rw [←sum,ac,bl,sc,lv]⟩

/-- Every successful primitive slot on a product of distinct primes gives
a positive primitive vector, with the first coordinate assigned to p. -/
theorem exists_vector_of_hit {p q T j k f : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (kp : 0<k) (primitive : j.Coprime k) (hit : probe (p*q) T j k=some f) :
    ∃ s v : ℕ, 0<s ∧ 0<v ∧ s.Coprime v ∧ k=s*v ∧ j+2*T*k=p*s^2+q*v^2 := by
  let N := p*q
  let S := j+2*T*k
  let d := (S^2-4*k^2*N).sqrt
  let A := (S+d)/2
  let B := (S-d)/2
  have good : 4*k^2*N≤S^2 ∧ d^2=S^2-4*k^2*N ∧ 1<N.gcd B ∧ N.gcd B<N := by
    unfold probe at hit
    dsimp only at hit
    split at hit
    next passed => exact passed
    next => contradiction
  have square : S^2=4*k^2*N+d^2 := by omega
  obtain ⟨sum,prod⟩ := root_identities square
  change A+B=j+2*T*k at sum
  change A*B=(p*q)*k^2 at prod
  have cop := (Nat.coprime_primes pp qp).mpr ne
  have sf := (Nat.squarefree_mul cop).mpr ⟨pp.squarefree,qp.squarefree⟩
  have roots := roots_coprime sf primitive sum prod
  have hitp : p∣A*B := prod ▸ dvd_mul_of_dvd_left (dvd_mul_right p q) _
  have hitq : q∣A*B := prod ▸ dvd_mul_of_dvd_left (dvd_mul_left q p) _
  rcases pp.dvd_mul.mp hitp with pa|pb <;> rcases qp.dvd_mul.mp hitq with qa|qb
  · have whole : N∣A := cop.mul_dvd_of_dvd_of_dvd pa qa
    have one := (coprime_of_factors roots whole (dvd_refl B)).gcd_eq_one
    exact False.elim ((Nat.ne_of_gt good.2.2.1) one)
  · exact oriented pp.pos qp.pos kp roots pa qb sum prod
  · exact oriented pp.pos qp.pos kp roots.symm pb qa (by rwa [add_comm]) (by rwa [mul_comm B A])
  · have whole : N∣B := cop.mul_dvd_of_dvd_of_dvd pb qb
    exact False.elim (good.2.2.2.ne (Nat.gcd_eq_left whole))

private theorem eq_or_eq_of_sum_prod {a b c d : ℕ} (sum : a+b=c+d) (prod : a*b=c*d) :
    a=c ∨ a=d := by
  zify at sum prod
  have zero : ((a:ℤ)-c)*((a:ℤ)-d)=0 := by
    nlinarith only [prod,congrArg (fun x:ℤ => (a:ℤ)*x) sum]
  rcases mul_eq_zero.mp zero with ac|ad
  · left; omega
  · right; omega

/-- Given a primitive slot on a product of distinct primes, there is at most
one oriented positive vector with its product and its weighted sum. -/
theorem vector_unique {p q T j k s₁ v₁ s₂ v₂ : ℕ}
    (pp : p.Prime) (qp : q.Prime) (ne : p≠q) (primitive : j.Coprime k)
    (ks₁ : k=s₁*v₁) (sum₁ : j+2*T*k=p*s₁^2+q*v₁^2)
    (ks₂ : k=s₂*v₂) (sum₂ : j+2*T*k=p*s₂^2+q*v₂^2) : s₁=s₂ ∧ v₁=v₂ := by
  have cop := (Nat.coprime_primes pp qp).mpr ne
  have sf := (Nat.squarefree_mul cop).mpr ⟨pp.squarefree,qp.squarefree⟩
  have prod₁ : (p*s₁^2)*(q*v₁^2)=(p*q)*k^2 := by rw [ks₁]; ring
  have prod₂ : (p*s₂^2)*(q*v₂^2)=(p*q)*k^2 := by rw [ks₂]; ring
  have roots := roots_coprime sf primitive sum₂.symm prod₂
  rcases eq_or_eq_of_sum_prod (sum₁.symm.trans sum₂) (prod₁.trans prod₂.symm) with same|swapped
  · have other : q*v₁^2=q*v₂^2 := by omega
    exact ⟨(Nat.pow_left_inj (by decide : 2≠0)).mp (Nat.eq_of_mul_eq_mul_left pp.pos same),
      (Nat.pow_left_inj (by decide : 2≠0)).mp (Nat.eq_of_mul_eq_mul_left qp.pos other)⟩
  · have both := Nat.dvd_gcd (dvd_mul_right p (s₂^2))
        (show p∣q*v₂^2 from swapped ▸ dvd_mul_right p (s₁^2))
    exact False.elim (pp.not_dvd_one (roots.gcd_eq_one ▸ both))

/-- Fixed oriented coordinates label at most one slot. -/
theorem indices_unique {p q T s v j₁ k₁ j₂ k₂ : ℕ}
    (k₁eq : k₁=s*v) (j₁eq : j₁+2*T*k₁=p*s^2+q*v^2)
    (k₂eq : k₂=s*v) (j₂eq : j₂+2*T*k₂=p*s^2+q*v^2) : j₁=j₂ ∧ k₁=k₂ := by
  rw [k₁eq] at j₁eq
  rw [k₂eq] at j₂eq
  omega

end PrimeFactors.OffsetSquareWitness
