import PrimeFactors.WeightedStride

namespace PrimeFactors.FareyWindow

/-- Two reduced fractions of determinant one enclosing the hidden ratio. -/
structure Bracket (p q K a b c d : ℕ) : Prop where
  bpos : 0 < b
  dpos : 0 < d
  bK : b ≤ K
  dK : d ≤ K
  leftLo : b ≤ a
  leftHi : a ≤ 2*b
  rightLo : d ≤ c
  rightHi : c ≤ 2*d
  det : b*c = a*d+1
  lo : a*p ≤ b*q
  hi : d*q ≤ c*p

/-- Subdivision by the mediant ends when the sum of denominators exceeds K.
The two endpoint fractions then both belong to the public schedule. -/
theorem terminal_bracket {p q K a b c d : ℕ} (B : Bracket p q K a b c d) :
    ∃ A B' C D, Bracket p q K A B' C D ∧ K < B'+D := by
  by_cases stop : K < b+d
  · exact ⟨a,b,c,d,B,stop⟩
  have den : b+d ≤ K := by omega
  have lo : b+d ≤ a+c := Nat.add_le_add B.leftLo B.rightLo
  have hi : a+c ≤ 2*(b+d) := by linarith only [B.leftHi,B.rightHi]
  by_cases left : (b+d)*q ≤ (a+c)*p
  · exact terminal_bracket (a := a) (b := b) (c := a+c) (d := b+d)
      ⟨B.bpos,by have := B.dpos; omega,B.bK,den,B.leftLo,B.leftHi,lo,hi,
        by nlinarith only [B.det],B.lo,left⟩
  · exact terminal_bracket (a := a+c) (b := b+d) (c := c) (d := d)
      ⟨by have := B.dpos; omega,B.dpos,den,B.dK,lo,hi,B.rightLo,B.rightHi,
        by nlinarith only [B.det],by omega,B.hi⟩
termination_by 2*K-(b+d)
decreasing_by all_goals have := B.bpos; have := B.dpos; have := B.bK; have := B.dK; omega

theorem exists_terminal {p q K : ℕ} (ordered : p ≤ q) (balanced : q ≤ 2*p) (hk : 0 < K) :
    ∃ a b c d, Bracket p q K a b c d ∧ K < b+d :=
  terminal_bracket (a := 1) (b := 1) (c := 2) (d := 1)
    ⟨by decide,by decide,hk,hk,by decide,by decide,by decide,by decide,by decide,
     by simpa using ordered,by simpa using balanced⟩

/-- The weighted errors on the two sides are nonnegative and satisfy
d*x+b*y=p. The smaller error supplies the approximation at scale b+d. -/
theorem bracket_errors {p q K a b c d : ℕ} (B : Bracket p q K a b c d) :
    ∃ x y, b*q=a*p+x ∧ c*p=d*q+y ∧ d*x+b*y=p ∧
        ((b+d)*x ≤ p ∨ (b+d)*y ≤ p) := by
  obtain ⟨x,hx⟩ := Nat.exists_eq_add_of_le B.lo
  obtain ⟨y,hy⟩ := Nat.exists_eq_add_of_le B.hi
  have id : d*x+b*y=p := by
    nlinarith only [congrArg (fun z : ℕ => z*d) hx, congrArg (fun z : ℕ => z*b) hy,
      congrArg (fun z : ℕ => z*p) B.det]
  refine ⟨x,y,hx,hy,id,?_⟩
  rcases le_total x y with h | h
  · left; nlinarith only [id,Nat.mul_le_mul_left b h]
  · right; nlinarith only [id,Nat.mul_le_mul_left d h]

/-- When a/b lies below q/p, the integer upper endpoint includes the
rounding cost at both ends. -/
theorem right_window {p q a b h x : ℕ} (ha : 0<a) (hh : 0<h)
    (eq : b*q=a*p+x) (close : h*x≤p) :
    let rad := 4*a*b*(p*q)
    let t := a*p+b*q
    ceilSqrt rad ≤ t ∧ t ≤ Nat.sqrt (rad+b*(p*q)/(h*(h*a+1))) := by
  have x2 : (h*x)^2 ≤ p^2 := Nat.pow_le_pow_left close 2
  have bound : x^2*(h*(h*a+1)) ≤ b*(p*q) := by
    nlinarith only [Nat.mul_le_mul_left a x2,Nat.mul_le_mul_right x close,
      congrArg (fun u : ℕ => u*p) eq]
  have div := (Nat.le_div_iff_mul_le (by positivity : 0<h*(h*a+1))).mpr bound
  have id : (a*p+b*q)^2=4*a*b*(p*q)+x^2 := by
    rw [show x = b*q-a*p by omega]
    rw [multiplier_sum_square, Nat.dist_eq_sub_of_le (by omega)]
  exact ⟨ceilSqrt_le_iff.mpr (by omega),Nat.le_sqrt'.mpr (by omega)⟩

/-- On the other side, the denominator changes by two units inside the
parentheses. This matters at the endpoints of the full ratio interval. -/
theorem left_window {p q a b h y : ℕ} (ha : 0<a) (hh : 1<h)
    (eq : a*p=b*q+y) (close : h*y≤p) :
    let rad := 4*a*b*(p*q)
    let t := a*p+b*q
    ceilSqrt rad ≤ t ∧ t ≤ Nat.sqrt (rad+b*(p*q)/(h*(h*a-1))) := by
  have ah : 1 < h*a := lt_of_lt_of_le hh (Nat.le_mul_of_pos_right _ ha)
  have pred := Nat.sub_add_cancel (by omega : 1≤h*a)
  obtain ⟨z,hz⟩ := Nat.exists_eq_add_of_le close
  have small : y ≤ a*(h*y) := calc
    y ≤ h*y := Nat.le_mul_of_pos_left y (by omega)
    _ ≤ _ := Nat.le_mul_of_pos_left _ ha
  have bound : y^2*(h*(h*a-1)) ≤ b*(p*q) := by
    have extra := Nat.mul_le_mul_right z small
    rw [hz] at eq ⊢
    nlinarith only [congrArg (fun u : ℕ => u*(h*y+z)) eq, extra,
      congrArg (fun u : ℕ => u*(h*y^2)) pred, Nat.zero_le (a*z^2),
      Nat.zero_le (a*h*y*z)]
  have div := (Nat.le_div_iff_mul_le (Nat.mul_pos (by omega : 0<h) (by omega : 0<h*a-1))).mpr bound
  have id : (a*p+b*q)^2=4*a*b*(p*q)+y^2 := by
    rw [show y = a*p-b*q by omega]
    rw [multiplier_sum_square, Nat.dist_eq_sub_of_le_right (by omega)]
  exact ⟨ceilSqrt_le_iff.mpr (by omega),Nat.le_sqrt'.mpr (by omega)⟩

/-- A common divisor of either endpoint's two coordinates divides the determinant. -/
theorem bracket_primitive {p q K a b c d : ℕ} (B : Bracket p q K a b c d) :
    a.Coprime b ∧ c.Coprime d := by
  have det := B.det
  constructor
  · apply Nat.eq_one_of_dvd_one
    apply (Nat.dvd_add_iff_right (dvd_mul_of_dvd_left (Nat.gcd_dvd_left a b) d)).mpr
    rw [← det]
    exact dvd_mul_of_dvd_left (Nat.gcd_dvd_right a b) c
  · apply Nat.eq_one_of_dvd_one
    apply (Nat.dvd_add_iff_right (dvd_mul_of_dvd_right (Nat.gcd_dvd_right c d) a)).mpr
    rw [← det]
    exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left c d) b

/-- If two candidates for the same neighboring denominator satisfy the
determinant congruence and both lie in the last b integers through K, they agree.
This explains why the executable can use just one modular inverse per slope. -/
theorem neighbor_unique {K b d e : ℕ} (hd : d≤K) (he : e≤K)
    (ld : K<b+d) (le' : K<b+e) (same : d ≡ e [MOD b]) : d=e :=
  same.eq_of_abs_lt (abs_lt.mpr ⟨by omega, by omega⟩)

/-- At least one compressed window in a terminal bracket contains the true
sum. Each branch uses only N, the public slope and its neighboring denominator
to specify both endpoints and the unique surviving residue class. -/
theorem compressed_cover {p q K : ℕ} (ordered : p ≤ q) (balanced : q ≤ 2*p)
    (hk : 0 < K) (unit : p.Coprime 6) :
    ∃ a b c d, Bracket p q K a b c d ∧ K<b+d ∧ a.Coprime b ∧ c.Coprime d ∧
      let h := b+d
      let n := p*q
      (ceilSqrt (4*a*b*n) ≤ a*p+b*q ∧
        a*p+b*q ≤ Nat.sqrt (4*a*b*n+b*n/(h*(h*a+1))) ∧
        a*p+b*q ≡ a+b*n [MOD weightedStride n a b]) ∨
      (ceilSqrt (4*c*d*n) ≤ c*p+d*q ∧
        c*p+d*q ≤ Nat.sqrt (4*c*d*n+d*n/(h*(h*c-1))) ∧
        c*p+d*q ≡ c+d*n [MOD weightedStride n c d]) := by
  obtain ⟨a,b,c,d,B,stop⟩ := exists_terminal ordered balanced hk
  obtain ⟨ab,cd⟩ := bracket_primitive B
  refine ⟨a,b,c,d,B,stop,ab,cd,?_⟩
  obtain ⟨x,y,hx,hy,_,left | right⟩ := bracket_errors B
  · have win := right_window (B.bpos.trans_le B.leftLo) (by omega) hx left
    exact Or.inl ⟨win.1,win.2, weighted_sum_congruent unit _ _ _⟩
  · have win := left_window (B.dpos.trans_le B.rightLo) (by omega) hy right
    exact Or.inr ⟨win.1,win.2, weighted_sum_congruent unit _ _ _⟩

end PrimeFactors.FareyWindow
