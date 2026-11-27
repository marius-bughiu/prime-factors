import PrimeFactors.RootIntervalSlope
import PrimeFactors.MaskedRelations
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.LinearCombination

/-! An integer Euclidean algorithm converts one supplied modular square root
of 2 or 3 into a primitive short representation of ±N. -/
namespace PrimeFactors.ShortRootNorm

set_option linter.unusedVariables false in
private def descend (N U V a b : ℕ) (s : ℤ) : ℤ × ℕ :=
  if stop : V^2 < 2*N ∨ V=0 then (s*V,b)
  else descend N V (U%V) b (a+U/V*b) (-s)
termination_by V
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => stop (Or.inr h))

/-- Start at Euclidean remainders N and r mod N, with the signed
coefficients of r alternating at each division. -/
def reduce (N r : ℕ) : ℤ × ℕ := descend N N (r%N) 0 1 1

private theorem descend_spec {N r U V a b : ℕ} {s : ℤ}
    (npos : 0<N) (prev : 2*N ≤ U^2) (ordered : V ≤ U) (bpos : 0<b)
    (cross : a*V+b*U=N) (sign : s^2=1)
    (old : -(s:ZMod N)*U=(r:ZMod N)*a) (now : (s:ZMod N)*V=(r:ZMod N)*b) :
    let v := descend N U V a b s
    0<v.2 ∧ v.1^2<2*(N:ℤ) ∧ 2*v.2^2≤N ∧ (v.1 : ZMod N)=(r:ZMod N)*v.2 := by
  induction V using Nat.strong_induction_on generalizing U a b s with
  | h V ih =>
    rw [descend]
    split_ifs with stop
    · have short : V^2<2*N := stop.elim id (by rintro rfl; simp; omega)
      have bu : b*U≤N := by omega
      have combo : (2*b^2)*N ≤ N*N := calc
        _ ≤ (b*U)^2 := by nlinarith only [Nat.mul_le_mul_left (b^2) prev]
        _ ≤ N*N := by simpa only [pow_two] using Nat.pow_le_pow_left bu 2
      refine ⟨bpos,?_,Nat.le_of_mul_le_mul_right combo npos,?_⟩
      · change (s*(V:ℤ))^2<2*(N:ℤ)
        rw [mul_pow,sign,one_mul]
        exact_mod_cast short
      · simpa using now
    · have vp : 0<V := Nat.pos_of_ne_zero fun h => stop (Or.inr h)
      have next := Nat.mod_lt U vp
      have quot : 0<U/V := Nat.div_pos ordered vp
      have rem : ((U%V : ℕ) : ZMod N) = (U:ZMod N)-((U/V:ℕ):ZMod N)*V := by
        have e := congrArg (fun z : ℕ => (z:ZMod N)) (Nat.div_add_mod' U V)
        push_cast at e
        linear_combination e
      apply ih _ next (le_of_not_gt fun h => stop (Or.inl h)) next.le (by positivity)
        (by rw [add_comm]; exact (rootIntervalSlope_euclidean_step U V a b).trans cross) (by simpa using sign)
      · simpa using now
      · push_cast
        rw [rem]
        linear_combination old+((U/V:ℕ):ZMod N)*now

theorem bounds {N : ℕ} (r : ℕ) (large : 2≤N) :
    let v := reduce N r
    0<v.2 ∧ v.1^2<2*(N:ℤ) ∧ 2*v.2^2≤N ∧ (v.1 : ZMod N)=(r:ZMod N)*v.2 := by
  apply descend_spec (by omega) (by simpa [pow_two] using Nat.mul_le_mul_right N large)
    (Nat.mod_lt r (by omega)).le (by decide) (by simp) (by decide) (by simp)
  simp

private theorem norm_nonzero {a : ℤ} {b D : ℕ} (bp : 0<b) (ns : ¬IsSquare D) :
    a^2 - D*(b:ℤ)^2 ≠ 0 := by
  intro zero
  have h : (a:ℚ)^2 = (D:ℚ)*(b:ℚ)^2 := by exact_mod_cast (sub_eq_zero.mp zero)
  apply ns <| Rat.isSquare_natCast_iff.mp <| (isSquare_iff_exists_sq _).mpr ?_
  exact ⟨(a:ℚ)/b,by rw [div_pow,h,mul_div_cancel_right₀ _ (pow_ne_zero 2 (by positivity))]⟩

/-- The signed norm is exactly ±N, even if N has repeated prime factors. -/
theorem norm {N D r : ℕ} (large : 2≤N) (small : D≤3) (ns : ¬IsSquare D)
    (root : (r:ZMod N)^2=D) :
    let v := reduce N r
    v.1^2 - D*(v.2:ℤ)^2 = N ∨ v.1^2 - D*(v.2:ℤ)^2 = -(N:ℤ) := by
  obtain ⟨bp,ah,bh,cong⟩ := bounds r large
  let v := reduce N r
  let z := v.1^2-D*(v.2:ℤ)^2
  have divides : (N:ℤ) ∣ z := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp
    dsimp only [z]
    push_cast
    rw [cong,mul_pow,root,sub_self]
  obtain ⟨m,hm⟩ := divides
  have npos : (0:ℤ)<N := by exact_mod_cast (show 0<N by omega)
  have bl : 2*(v.2:ℤ)^2≤N := by exact_mod_cast bh
  have cap : (D:ℤ)≤3 := by exact_mod_cast small
  have high : (N:ℤ)*m < N*2 := by
    rw [← hm]
    dsimp [z,v]
    nlinarith only [ah,mul_nonneg (Int.natCast_nonneg D) (sq_nonneg ((reduce N r).2:ℤ))]
  have low : (N:ℤ)*(-2)<N*m := by
    rw [← hm]
    dsimp only [z]
    nlinarith only [bl,npos,sq_nonneg v.1,mul_le_mul_of_nonneg_right cap (sq_nonneg (v.2:ℤ))]
  have sz₁ := (mul_lt_mul_left npos).mp high
  have sz₂ := (mul_lt_mul_left npos).mp low
  have nz : m≠0 := by rintro rfl; exact norm_nonzero bp ns (hm.trans (mul_zero _))
  rcases (show m=1 ∨ m= -1 by omega) with h | h
  · exact Or.inl (by simpa [h,z,v] using hm)
  · exact Or.inr (by simpa [h,z,v] using hm)

/-- A norm representative in the prescribed lattice is primitive; its
denominator is invertible modulo N. This works for nonsquarefree N too. -/
theorem primitive_of_norm {N D r : ℕ} {a : ℤ} {b : ℕ} (npos : 0<N)
    (root : (r:ZMod N)^2=D) (point : (a:ZMod N) = (r:ZMod N)*b)
    (exactNorm : a^2-D*(b:ℤ)^2=N ∨ a^2-D*(b:ℤ)^2= -(N:ℤ)) :
    IsCoprime a (b:ℤ) ∧ b.Coprime N := by
  have lift : (N:ℤ) ∣ a-r*(b:ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [point,sub_self]
  have rr : (N:ℤ) ∣ (r:ℤ)^2-D := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [root,sub_self]
  obtain ⟨h,hh⟩ := lift
  obtain ⟨m,hm⟩ := rr
  let c := (r:ℤ)*h+m*b
  have cancel : a^2-D*(b:ℤ)^2=N*(h*a+c*b) := by
    dsimp [c]
    linear_combination (a+r*b)*hh+((b:ℤ)^2)*hm
  have nn : (N:ℤ) ≠ 0 := by exact_mod_cast npos.ne'
  have prim : IsCoprime a (b:ℤ) := by
    rcases exactNorm with pos | neg
    · exact ⟨h,c,mul_left_cancel₀ nn ((cancel.symm.trans pos).trans (mul_one _).symm)⟩
    · have eq : h*a+c*b = -1 := mul_left_cancel₀ nn (by rw [← cancel,neg]; ring)
      exact ⟨-h,-c,by linear_combination -eq⟩
  refine ⟨prim,Nat.isCoprime_iff_coprime.mp ?_⟩
  obtain ⟨u,v,bez⟩ := prim
  exact ⟨u*r+v,u*h,by linear_combination bez-u*hh⟩

theorem primitive {N D r : ℕ} (large : 2≤N) (small : D≤3) (ns : ¬IsSquare D)
    (root : (r:ZMod N)^2=D) :
    IsCoprime (reduce N r).1 ((reduce N r).2:ℤ) ∧ (reduce N r).2.Coprime N :=
  primitive_of_norm (by omega) root (bounds r large).2.2.2 (norm large small ns root)

/-- The original root is recovered from the short representation by division
by its unit denominator. Passing to this representation preserves the root
and introduces no second choice of local signs. -/
theorem recover {N D r : ℕ} (large : 2≤N) (small : D≤3) (ns : ¬IsSquare D)
    (root : (r:ZMod N)^2=D) :
    ((reduce N r).1 : ZMod N)*((reduce N r).2:ZMod N)⁻¹ = r := by
  obtain ⟨_,unit⟩ := primitive large small ns root
  rw [(bounds r large).2.2.2,mul_assoc,ZMod.coe_mul_inv_eq_one _ unit,mul_one]

/-- Cross-multiplication gives exactly the gcd of the original two roots,
including for equal or opposite roots. -/
theorem cross_gcd {N D r t : ℕ} (large : 2≤N) (small : D≤3) (ns : ¬IsSquare D)
    (rr : (r:ZMod N)^2=D) (tr : (t:ZMod N)^2=D) :
    let u := reduce N r
    let v := reduce N t
    ((u.1:ZMod N)*v.2-(v.1:ZMod N)*u.2).val.gcd N = ((r:ZMod N)-t).val.gcd N := by
  letI : NeZero N := ⟨by omega⟩
  let u := reduce N r
  let v := reduce N t
  have un := (primitive large small ns rr).2
  have vn := (primitive large small ns tr).2
  let w := ZMod.unitOfCoprime (u.2*v.2) (Nat.coprime_mul_iff_left.mpr ⟨un,vn⟩)
  have wz : (w : ZMod N) = (u.2:ZMod N)*v.2 := by
    rw [show (w:ZMod N) = (↑(u.2*v.2):ZMod N) from ZMod.coe_unitOfCoprime ..,Nat.cast_mul]
  have eq : (u.1:ZMod N)*v.2-(v.1:ZMod N)*u.2 = (w:ZMod N)*r-w*t := by
    rw [(bounds r large).2.2.2,(bounds t large).2.2.2,wz]
    ring
  change ((u.1:ZMod N)*v.2-(v.1:ZMod N)*u.2).val.gcd N = _
  rw [eq, maskedRelations_unit_gcd]

/-- Two representations with unit denominator give the same root precisely
when their elements a+b√D and c+d√D differ by an integral unit of norm ±1.
Conjugating one representation compares opposite roots by the same test. -/
theorem same_root_iff_unit {N : ℕ} (np : 0<N) {D a b c d : ℤ} {r t : ZMod N}
    (square : t^2=D) (first : (a:ZMod N)=r*b) (second : (c:ZMod N)=t*d)
    (bu : IsUnit (b:ZMod N)) (na : a^2-D*b^2=N ∨ a^2-D*b^2= -(N:ℤ))
    (nc : c^2-D*d^2=N ∨ c^2-D*d^2= -(N:ℤ)) :
    r=t ↔ ∃ j v : ℤ, (j^2-D*v^2=1 ∨ j^2-D*v^2= -1) ∧
      a=j*c+D*v*d ∧ b=v*c+j*d := by
  constructor
  · rintro rfl
    have mult : (N:ℤ) ∣ a*c-D*b*d := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [first,second,← square]
      ring
    have det : (N:ℤ) ∣ b*c-a*d := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [first,second]
      ring
    let C := c^2-D*d^2
    have nz : C ≠ 0 := by rcases nc with h|h <;> dsimp [C] <;> omega
    have dvd {m : ℤ} (hm : (N:ℤ) ∣ m) : C ∣ m := by
      rcases nc with h|h <;> simpa [C,h] using hm
    obtain ⟨j,hj⟩ := dvd mult
    obtain ⟨v,hv⟩ := dvd det
    dsimp [C] at hj hv
    have aa : a=j*c+D*v*d := by
      apply mul_left_cancel₀ nz
      dsimp [C]
      linear_combination c*hj+D*d*hv
    have bb : b=v*c+j*d := by
      apply mul_left_cancel₀ nz
      dsimp [C]
      linear_combination d*hj+c*hv
    refine ⟨j,v,?_,aa,bb⟩
    have product : a^2-D*b^2 = C*(j^2-D*v^2) := by rw [aa,bb]; dsimp [C]; ring
    have opposite : a^2-D*b^2=C ∨ a^2-D*b^2= -C := by
      rcases na with h|h <;> rcases nc with e|e <;> simp [C,h,e]
    rw [product] at opposite
    rcases opposite with h|h
    · exact Or.inl (mul_left_cancel₀ nz (by simpa using h : C*_=C*1))
    · exact Or.inr (mul_left_cancel₀ nz (by simpa using h : C*_=C*(-1)))
  · rintro ⟨j,v,_,aa,bb⟩
    apply bu.mul_left_inj.mp
    have ax := congrArg (fun z : ℤ => (z:ZMod N)) aa
    have bx := congrArg (fun z : ℤ => (z:ZMod N)) bb
    push_cast at ax bx
    rw [← first,ax,bx,second,← square]
    ring

/-- Distinct roots up to global sign lead to a proper divisor by taking the
cross-coordinate gcd. This makes no classification assumption about N. -/
theorem split {N D r t : ℕ} (large : 2≤N) (small : D≤3) (ns : ¬IsSquare D)
    (rr : (r:ZMod N)^2=D) (tr : (t:ZMod N)^2=D)
    (diff : (r:ZMod N)≠t) (opposite : (r:ZMod N)≠-t) :
    let u := reduce N r
    let v := reduce N t
    let f := ((u.1:ZMod N)*v.2-(v.1:ZMod N)*u.2).val.gcd N
    1<f ∧ f<N := by
  letI : NeZero N := ⟨by omega⟩
  simpa only [cross_gcd large small ns rr tr] using
    (maskedRelations_split (rr.trans tr.symm) diff opposite)

end PrimeFactors.ShortRootNorm
