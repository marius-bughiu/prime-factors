import PrimeFactors.CircleMarkRationalCover

/-! Farey neighbors characterize the roots omitted by a rectangular ratio grid. -/
namespace PrimeFactors.CircleMarkRationalDeficit

open Finset CircleMarkRationalCover

/-- The two denominators of an order-`D` Farey bracket and their positive
residual magnitudes. The determinant is the modulus rather than one because
residuals measure the vertical errors after multiplication by `p`. -/
structure Bracket {p : ℕ} (r : ZMod p) (D b d X Y : ℕ) : Prop where
  bp : 0 < b
  dp : 0 < d
  bd : b ≤ D
  dd : d ≤ D
  span : D < b+d
  xp : 0 < X
  yp : 0 < Y
  det : d*X+b*Y = p
  left : (b : ZMod p)*r = X
  right : (d : ZMod p)*r = -(Y : ZMod p)

theorem Bracket.swap {p D b d X Y : ℕ} {r : ZMod p} (h : Bracket r D b d X Y) :
    Bracket (-r) D d b Y X := by
  refine ⟨h.dp,h.bp,h.dd,h.bd,by simpa [add_comm] using h.span,h.yp,h.xp,
    by simpa [add_comm] using h.det,?_,?_⟩
  · simp [h.right]
  · simp [h.left]

private theorem natCast_ne_zero {p n : ℕ} (pos : 0 < n) (small : n < p) :
    (n : ZMod p) ≠ 0 :=
  fun h => Nat.not_dvd_of_pos_of_lt pos small ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp h)

/-- Starting with the bracket `0/1,1/1`, insert its mediant exactly when its
denominator becomes affordable. A nonzero residue of prime modulus cannot be
the mediant while its denominator is below the modulus. -/
theorem exists_bracket {p : ℕ} [Fact p.Prime] {r : ZMod p} (nz : r ≠ 0)
    {D : ℕ} (dp : 0 < D) (short : D < p) : ∃ b d X Y, Bracket r D b d X Y := by
  induction D with
  | zero => omega
  | succ D ih =>
    by_cases zero : D = 0
    · subst D
      have rv : 0 < r.val := Nat.pos_of_ne_zero (fun h => nz ((ZMod.val_eq_zero r).mp h))
      have rs := r.val_lt
      refine ⟨1,1,r.val,p-r.val,by decide,by decide,by decide,by decide,by decide,
        rv,by omega,by simp; omega,by simp,?_⟩
      simp [Nat.cast_sub rs.le]
    · obtain ⟨b,d,X,Y,h⟩ := ih (by omega) (by omega)
      by_cases fitting : b+d ≤ D+1
      · have step : b+d = D+1 := by have := h.span; omega
        have distinct : X ≠ Y := by
          intro eqn
          have sum : ((b+d : ℕ) : ZMod p)*r = 0 := by push_cast; rw [add_mul,h.left,h.right,eqn]; simp
          exact mul_ne_zero (natCast_ne_zero (by omega) (by omega)) nz sum
        rcases lt_or_gt_of_ne distinct with lt|gt
        · refine ⟨b,b+d,X,Y-X,h.bp,by omega,by have := h.bd; omega,fitting,
            by have := h.bp; omega,h.xp,by omega,?_,h.left,?_⟩
          · have sub := Nat.sub_add_cancel lt.le
            have := h.det
            nlinarith only [sub,congrArg (fun n => b*n) sub,this]
          · push_cast [Nat.cast_sub lt.le]
            rw [add_mul,h.left,h.right]
            ring
        · refine ⟨b+d,d,X-Y,Y,by omega,h.dp,fitting,by have := h.dd; omega,
            by have := h.dp; omega,by omega,h.yp,?_,?_,h.right⟩
          · have sub := Nat.sub_add_cancel gt.le
            have := h.det
            nlinarith only [sub,congrArg (fun n => d*n) sub,this]
          · push_cast [Nat.cast_sub gt.le]
            rw [add_mul,h.left,h.right]
            ring
      · exact ⟨b,d,X,Y,h.bp,h.dp,h.bd.trans (Nat.le_succ _),h.dd.trans (Nat.le_succ _),by omega,h.xp,h.yp,h.det,h.left,h.right⟩

/-- Any positive residual with an affordable denominator is at least the left
residual. The two oriented determinants with a candidate point are multiples
of `p`; if both are positive its denominator is at least `b+d`. -/
theorem Bracket.left_minimal {p D b d X Y i j : ℕ} {r : ZMod p}
    (h : Bracket r D b d X Y) (ip : 0 < i) (jp : 0 < j) (jd : j ≤ D)
    (eqn : (j : ZMod p)*r = i) : X ≤ i := by
  by_contra! small
  have first : p ∣ j*Y+i*d := by
    apply (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp
    push_cast
    linear_combination (j : ZMod p)*h.right - (d : ZMod p)*eqn
  have bound := Nat.le_of_dvd (by have := h.yp; positivity : 0 < j*Y+i*d) first
  have bj : b ≤ j := by
    apply le_of_not_gt
    intro bad
    have one := Nat.mul_lt_mul_of_pos_right bad h.yp
    have two := Nat.mul_lt_mul_of_pos_right small h.dp
    have := h.det
    nlinarith only [one,two,bound,this]
  have delta : i*b < j*X := calc
    i*b < X*b := Nat.mul_lt_mul_of_pos_right small h.bp
    _ ≤ j*X := by simpa [mul_comm] using Nat.mul_le_mul_left X bj
  have second : p ∣ j*X-i*b := by
    apply (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp
    push_cast [Nat.cast_sub delta.le]
    linear_combination (b : ZMod p)*eqn - (j : ZMod p)*h.left
  have bound' := Nat.le_of_dvd (by omega : 0 < j*X-i*b) second
  have t := Nat.sub_add_cancel delta.le
  have combo : p*(b+d) ≤ p*j := calc
    p*(b+d) ≤ (j*Y+i*d)*b+(j*X-i*b)*d := by
      rw [mul_add]
      exact Nat.add_le_add (Nat.mul_le_mul_right b bound) (Nat.mul_le_mul_right d bound')
    _ = p*j := by
      rw [←h.det]
      nlinarith only [congrArg (fun n => n*d) t]
  have pp : 0 < p := by rw [←h.det]; have := h.dp; have := h.xp; positivity
  have := Nat.le_of_mul_le_mul_left combo pp
  have := h.span
  omega

/-- The least numerator over both signs is the smaller of the two bracket
residuals. -/
theorem Bracket.miss_iff {p D b d X Y H : ℕ} {r : ZMod p} (h : Bracket r D b d X Y) :
    ¬Represents r H D ↔ H < X ∧ H < Y := by
  constructor
  · intro miss
    constructor
    · by_contra! small
      exact miss ⟨X,mem_Icc.mpr ⟨h.xp,small⟩,b,mem_Icc.mpr ⟨h.bp,h.bd⟩,Or.inl h.left.symm⟩
    · by_contra! small
      exact miss ⟨Y,mem_Icc.mpr ⟨h.yp,small⟩,d,mem_Icc.mpr ⟨h.dp,h.dd⟩,Or.inr (by simp [h.right])⟩
  · rintro ⟨hx,hy⟩ ⟨i,hi,j,hj,same|opp⟩
    all_goals
      obtain ⟨ip,ih⟩ := mem_Icc.mp hi
      obtain ⟨jp,jd⟩ := mem_Icc.mp hj
    · have := h.left_minimal ip jp jd same.symm
      omega
    · have := h.swap.left_minimal ip jp jd (by simpa using opp.symm)
      omega

/-- A determinant solution supplies the omitted residue by dividing its left
residual by its denominator in the prime field. Coprimality of the two
denominators is unnecessary as an input. -/
theorem bracket_of_det {p D b d X Y : ℕ} [Fact p.Prime] (short : D < p)
    (bp : 0 < b) (dp : 0 < d) (bd : b ≤ D) (dd : d ≤ D) (span : D < b+d)
    (xp : 0 < X) (yp : 0 < Y) (det : d*X+b*Y = p) :
    let r : ZMod p := (X : ZMod p) / (b : ZMod p)
    r ≠ 0 ∧ Bracket r D b d X Y := by
  dsimp
  have bn := natCast_ne_zero bp (bd.trans_lt short)
  have little : X < p := by
    have low := Nat.le_mul_of_pos_left X dp
    have : 0 < b*Y := by positivity
    omega
  have xn := natCast_ne_zero xp little
  refine ⟨div_ne_zero xn bn,bp,dp,bd,dd,span,xp,yp,det,?_,?_⟩
  · field_simp
  · have moddet : (d : ZMod p)*X+b*Y=0 := by
      simpa using congrArg (fun n : ℕ => (n : ZMod p)) det
    field_simp
    linear_combination moddet

/-- If the modulus exceeds the endpoint area by `s`, each absent residue
splits `s` into three nonnegative costs. -/
theorem Bracket.deficit {p H D s b d X Y : ℕ} {r : ZMod p} (h : Bracket r D b d X Y)
    (eqn : p = (H+1)*(D+1)+s) (miss : ¬Represents r H D) :
    (b+d-(D+1))*(H+1) + d*(X-(H+1)) + b*(Y-(H+1)) = s := by
  obtain ⟨hx,hy⟩ := h.miss_iff.mp miss
  have span := h.span
  have w := Nat.sub_add_cancel (show D+1 ≤ b+d by omega)
  have x := Nat.sub_add_cancel (show H+1 ≤ X by omega)
  have y := Nat.sub_add_cancel (show H+1 ≤ Y by omega)
  nlinarith only [congrArg (fun n => n*(H+1)) w, congrArg (fun n => d*n) x,
    congrArg (fun n => b*n) y,h.det,eqn]

/-- Both residuals are minima. Below the modulus, each nonzero root determines
their denominators uniquely. -/
theorem Bracket.unique {p D b d X Y b' d' X' Y' : ℕ} [Fact p.Prime] {r : ZMod p}
    (nz : r ≠ 0) (short : D < p) (h : Bracket r D b d X Y)
    (k : Bracket r D b' d' X' Y') : b = b' ∧ d = d' ∧ X = X' ∧ Y = Y' := by
  have xx := le_antisymm (h.left_minimal k.xp k.bp k.bd k.left)
    (k.left_minimal h.xp h.bp h.bd h.left)
  have yy := le_antisymm (h.swap.left_minimal k.yp k.dp k.dd k.swap.left)
    (k.swap.left_minimal h.yp h.dp h.dd h.swap.left)
  subst X'
  subst Y'
  have be : (b : ZMod p) = b' := mul_right_cancel₀ nz (h.left.trans k.left.symm)
  have de : (d : ZMod p) = d' := mul_right_cancel₀ nz (h.right.trans k.right.symm)
  have bv := congrArg ZMod.val be
  have dv := congrArg ZMod.val de
  rw [ZMod.val_natCast_of_lt (h.bd.trans_lt short),ZMod.val_natCast_of_lt (k.bd.trans_lt short)] at bv
  rw [ZMod.val_natCast_of_lt (h.dd.trans_lt short),ZMod.val_natCast_of_lt (k.dd.trans_lt short)] at dv
  exact ⟨bv,dv,rfl,rfl⟩

theorem Bracket.coprime {p D b d X Y : ℕ} [hp : Fact p.Prime] {r : ZMod p}
    (h : Bracket r D b d X Y) (short : D < p) : b.Coprime d := by
  have divides : b.gcd d ∣ p := by
    rw [←h.det]
    exact dvd_add (dvd_mul_of_dvd_left (Nat.gcd_dvd_right ..) _)
      (dvd_mul_of_dvd_left (Nat.gcd_dvd_left ..) _)
  have bound := (Nat.le_of_dvd h.bp (Nat.gcd_dvd_left b d)).trans_lt (h.bd.trans_lt short)
  exact (hp.out.eq_one_or_self_of_dvd _ divides).resolve_right (Nat.ne_of_lt bound)

/-- Exact parametrization for every excess, including excesses above the side
lengths. The two offsets are the nonnegative residuals above the first excluded
numerator. Each solution yields its residue by one division in the field. -/
theorem miss_iff_deficit_solution {p H D s : ℕ} [Fact p.Prime] {r : ZMod p}
    (nz : r ≠ 0) (dp : 0 < D) (eqn : p = (H+1)*(D+1)+s) :
    ¬Represents r H D ↔ ∃ b d u v : ℕ, 0 < b ∧ 0 < d ∧ b ≤ D ∧ d ≤ D ∧
      D < b+d ∧ b.Coprime d ∧
      (b+d-(D+1))*(H+1) + d*u + b*v = s ∧
      r = ((H+1+u : ℕ) : ZMod p)/(b : ZMod p) := by
  have short : D < p := by nlinarith only [eqn,Nat.zero_le (H*D),Nat.zero_le H,Nat.zero_le s]
  constructor
  · intro miss
    obtain ⟨b,d,X,Y,h⟩ := exists_bracket nz dp short
    obtain ⟨hx,hy⟩ := h.miss_iff.mp miss
    refine ⟨b,d,X-(H+1),Y-(H+1),h.bp,h.dp,h.bd,h.dd,h.span,h.coprime short,h.deficit eqn miss,?_⟩
    rw [show H+1+(X-(H+1)) = X by omega]
    exact (eq_div_iff (natCast_ne_zero h.bp (h.bd.trans_lt short))).mpr (by simpa [mul_comm] using h.left)
  · rintro ⟨b,d,u,v,bp,ddp,bd,dd,span,_,budget,rfl⟩
    have w := Nat.sub_add_cancel (show D+1 ≤ b+d by omega)
    have det : d*(H+1+u)+b*(H+1+v) = p := by
      nlinarith only [budget,eqn,congrArg (fun n => n*(H+1)) w]
    obtain ⟨_,h⟩ := bracket_of_det short bp ddp bd dd span (by omega) (by omega) det
    exact h.miss_iff.mpr ⟨by omega,by omega⟩

/-- Below both side lengths, a missing root is a signed ratio with fixed
numerator `H+1` and a denominator dividing the excess `s`. -/
theorem divisor_of_miss {p H D s : ℕ} [Fact p.Prime] {r : ZMod p}
    (dp : 0 < D) (nz : r ≠ 0) (eqn : p = (H+1)*(D+1)+s) (_sp : 0 < s)
    (sa : s < H+1) (sb : s < D+1) (miss : ¬Represents r H D) :
    ∃ t : ℕ, t ∣ s ∧ ((t : ZMod p)*r = ((H+1 : ℕ) : ZMod p) ∨
      (t : ZMod p)*r = -((H+1 : ℕ) : ZMod p)) := by
  have short : D < p := by nlinarith only [eqn,Nat.zero_le (H*D),Nat.zero_le H,Nat.zero_le s]
  obtain ⟨b,d,X,Y,h⟩ := exists_bracket nz dp short
  have sum := h.deficit eqn miss
  obtain ⟨hx,hy⟩ := h.miss_iff.mp miss
  have span := h.span
  have tight : b+d-(D+1) = 0 := by
    by_contra bad
    have := Nat.le_mul_of_pos_left (H+1) (Nat.pos_of_ne_zero bad)
    omega
  rw [tight,zero_mul,zero_add] at sum
  have endpoint : X = H+1 ∨ Y = H+1 := by
    by_contra! both
    have left := Nat.le_mul_of_pos_right d (show 0 < X-(H+1) by omega)
    have right := Nat.le_mul_of_pos_right b (show 0 < Y-(H+1) by omega)
    omega
  rcases endpoint with left|right
  · rw [left,Nat.sub_self,mul_zero,zero_add] at sum
    exact ⟨b,⟨_,sum.symm⟩,Or.inl (left ▸ h.left)⟩
  · rw [right,Nat.sub_self,mul_zero,add_zero] at sum
    exact ⟨d,⟨_,sum.symm⟩,Or.inr (right ▸ h.right)⟩

end PrimeFactors.CircleMarkRationalDeficit
