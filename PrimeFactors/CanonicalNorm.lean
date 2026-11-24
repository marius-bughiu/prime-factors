import PrimeFactors.ShortNormBox

namespace PrimeFactors.CanonicalNorm

/-- The three disjoint sign and parity choices. The last condition chooses
the part of the indefinite hyperbola inside the square-root box. -/
def IsCanonical (p d t a : ℤ) : Prop :=
  0<t ∧ 0<a ∧ t%2=1 ∧
    ((d= -1 ∧ a%2=0 ∧ p=t^2+a^2) ∨
     (d= -2 ∧ a%2=1 ∧ p=t^2+2*a^2) ∨
     (d=2 ∧ a%2=0 ∧ t<a ∧ p=2*a^2-t^2))

theorem exists_canonical {p : ℕ} [Fact p.Prime] (odd : p≠2) :
    ∃ d t a : ℤ, IsCanonical p d t a := by
  obtain ⟨t,a,tp,ap,t2,_,toff,forms⟩ := ShortNormBox.prime_representation odd
  rcases forms with ⟨ae,norm⟩ | ⟨ao,norm⟩ | ⟨ae,norm⟩
  · exact ⟨-1,t,a,tp,ap,toff,Or.inl ⟨rfl,ae,norm⟩⟩
  · exact ⟨-2,t,a,tp,ap,toff,Or.inr (Or.inl ⟨rfl,ao,norm⟩)⟩
  · have lt : t<a := (sq_lt_sq₀ tp.le ap.le).mp (by linarith)
    exact ⟨2,t,a,tp,ap,toff,Or.inr (Or.inr ⟨rfl,ae,lt,norm⟩)⟩

private theorem square_residue (n : ℤ) :
    (n%2=0 → n^2%8=0 ∨ n^2%8=4) ∧ (n%2=1 → n^2%8=1) := by
  have lower := Int.emod_nonneg n (by decide : (8:ℤ)≠0)
  have upper := Int.emod_lt_of_pos n (by decide : (0:ℤ)<8)
  rw [pow_two,Int.mul_emod]
  interval_cases h : n%8 <;> norm_num at * <;> omega

private def discriminant (p : ℤ) : ℤ :=
  if p%4=1 then -1 else if p%8=3 then -2 else 2

private def sign (d : ℤ) : ℤ := if d=2 then -1 else 1

/-- The prime's residue determines the form, which determines the second
coordinate's parity. Both coordinate squares are strictly below p. -/
private theorem encode {p d t a : ℤ} (h : IsCanonical p d t a) :
    d=discriminant p ∧ a%2=(if d= -2 then 1 else 0) ∧ t^2<p ∧ a^2<p ∧
    t^2-d*a^2=sign d*p := by
  obtain ⟨tp,ap,toff,forms⟩ := h
  have t8 := (square_residue t).2 toff
  rcases forms with ⟨rfl,ae,norm⟩ | ⟨rfl,ao,norm⟩ | ⟨rfl,ae,order,norm⟩
  · have a8 := (square_residue a).1 ae
    have res : p%4=1 := by omega
    simp only [discriminant,res,if_true,sign]
    norm_num
    exact ⟨Int.dvd_of_emod_eq_zero ae,by nlinarith [sq_pos_of_pos ap],by nlinarith [sq_pos_of_pos tp],by linarith⟩
  · have a8 := (square_residue a).2 ao
    have res : p%8=3 := by omega
    have res4 : p%4≠1 := by omega
    simp only [discriminant,res4,res,if_false,if_true,sign]
    norm_num
    exact ⟨ao,by nlinarith [sq_pos_of_pos ap],by nlinarith [sq_pos_of_pos tp],by linarith⟩
  · have a8 := (square_residue a).1 ae
    have res : p%8=7 := by omega
    have res4 : p%4≠1 := by omega
    have ne : p%8≠3 := by omega
    have squares := (sq_lt_sq₀ tp.le ap.le).mpr order
    simp only [discriminant,res4,ne,if_false,sign,if_true]
    norm_num
    exact ⟨Int.dvd_of_emod_eq_zero ae,by linarith,by linarith,by linarith⟩

/-- A prime has at most one canonical triple. Positive cross products
are below p, and their sum has even parity. The only possible collision
modulo p is consequently equality of the two rational slopes. -/
theorem unique {p : ℕ} [Fact p.Prime] (odd : p≠2) {d e t a u b : ℤ}
    (one : IsCanonical p d t a) (two : IsCanonical p e u b) :
    d=e ∧ t=u ∧ a=b := by
  obtain ⟨dval,apar,t2,a2,first⟩ := encode one
  obtain ⟨eval,bpar,u2,b2,second⟩ := encode two
  have forms : e=d := eval.trans dval.symm
  clear dval eval
  subst e
  have pPrime : p.Prime := Fact.out
  have pos : 0<(p:ℤ) := by exact_mod_cast pPrime.pos
  have pOdd : (p:ℤ)%2=1 := by exact_mod_cast Nat.Prime.mod_two_eq_one_iff_ne_two.mpr odd
  obtain ⟨tp,ap,toff,_⟩ := one
  obtain ⟨up,bp,uoff,_⟩ := two
  have leftPos := mul_pos tp bp
  have rightPos := mul_pos up ap
  have left : t*b<p := by nlinarith [sq_nonneg (t-b)]
  have right : u*a<p := by nlinarith [sq_nonneg (u-a)]
  have det : (t*b-u*a)*(t*b+u*a)=(sign d*(p:ℤ))*(b^2-a^2) := by
    linear_combination b^2*first-a^2*second
  have dvd : (p:ℤ)∣(t*b-u*a)*(t*b+u*a) :=
    ⟨sign d*(b^2-a^2), by rw [det]; ring⟩
  have cross : t*b=u*a := by
    rcases (Nat.prime_iff_prime_int.mp pPrime).dvd_mul.mp dvd with hd | hs
    · apply sub_eq_zero.mp
      exact Int.eq_zero_of_abs_lt_dvd hd (abs_lt.mpr ⟨by linarith,by linarith⟩)
    · have whole : t*b+u*a=(p:ℤ) := sub_eq_zero.mp <|
        Int.eq_zero_of_abs_lt_dvd (dvd_sub hs dvd_rfl) (abs_lt.mpr ⟨by linarith,by linarith⟩)
      have parity := congrArg (fun v : ℤ => v%2) whole
      change (t*b+u*a)%2=(p:ℤ)%2 at parity
      rw [Int.add_emod,Int.mul_emod,Int.mul_emod u a,toff,uoff,pOdd,one_mul,one_mul] at parity
      have ab := apar.trans bpar.symm
      omega
  have signNonzero : sign d ≠ 0 := by unfold sign; split <;> decide
  have sqDiff : b^2-a^2=0 := by
    rw [cross,sub_self,zero_mul] at det
    exact (mul_eq_zero.mp det.symm).resolve_left (mul_ne_zero signNonzero pos.ne')
  have ba : b=a := (sq_eq_sq₀ bp.le ap.le).mp (sub_eq_zero.mp sqDiff)
  rw [ba] at cross
  exact ⟨rfl,mul_right_cancel₀ ap.ne' cross,ba.symm⟩

/-- Existence and uniqueness together, with triples ordered (d,t,a). -/
theorem exists_unique {p : ℕ} [Fact p.Prime] (odd : p≠2) :
    ∃! r : ℤ × ℤ × ℤ, IsCanonical p r.1 r.2.1 r.2.2 := by
  obtain ⟨d,t,a,h⟩ := exists_canonical odd
  refine ⟨(d,t,a),h,?_⟩
  rintro ⟨e,u,b⟩ other
  obtain ⟨rfl,rfl,rfl⟩ := unique odd other h
  rfl

end PrimeFactors.CanonicalNorm
