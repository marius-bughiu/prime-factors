import PrimeFactors.QuotientStripLevels
import PrimeFactors.FareyWindow

/-!
# Reusing a direction for moving quotient chords

For a chord of the reciprocal over [A,B], use S=A*B. The chord-slope
magnitude is N/S. An adjacent Farey bracket at order Q gives the best
direction for the integer cross-product error. A fixed direction meets
the five-level certificate on one exact interval of S.
-/

namespace PrimeFactors.QuotientStripFareyRuns

/-- The left endpoint wins ties at the mediant. -/
def choose (N S a b c d : ℤ) : ℤ × ℤ :=
  if (b+d)*N ≤ (a+c)*S then (a,b) else (c,d)

structure Bracket (N S Q a b c d : ℤ) : Prop where
  bpos : 0 < b
  dpos : 0 < d
  bcap : b ≤ Q
  dcap : d ≤ Q
  terminal : Q < b+d
  det : b*c-a*d = 1
  left : a*S ≤ b*N
  right : d*N ≤ c*S

/-- Reuse the repository's terminal-bracket construction when the chord slope
lies between one and two. -/
theorem exists_bracket {N S Q : ℕ} (low : S ≤ N) (high : N ≤ 2*S) (pos : 0 < Q) :
    ∃ a b c d : ℤ, Bracket N S Q a b c d := by
  obtain ⟨a,b,c,d,B,terminal⟩ := FareyWindow.exists_terminal low high pos
  refine ⟨a,b,c,d,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact_mod_cast B.bpos
  · exact_mod_cast B.dpos
  · exact_mod_cast B.bK
  · exact_mod_cast B.dK
  · exact_mod_cast terminal
  · have h : (b:ℤ)*c = (a:ℤ)*d+1 := by exact_mod_cast B.det
    omega
  · exact_mod_cast B.lo
  · exact_mod_cast B.hi

/-- The selected error is the smaller of the two endpoint errors. -/
theorem selected_error {N S Q a b c d : ℤ} (B : Bracket N S Q a b c d) :
    let z := choose N S a b c d
    |z.1*S-z.2*N| = min (b*N-a*S) (c*S-d*N) := by
  dsimp only
  unfold choose
  split <;> rename_i side
  · simp only [abs_of_nonpos (sub_nonpos.mpr B.left)]
    rw [min_eq_left (by linarith only [side])]
    ring
  · simp only [abs_of_nonneg (sub_nonneg.mpr B.right)]
    rw [min_eq_right (by linarith only [side])]

/-- The mediant selector meets the cross-product bound with a legal denominator. -/
theorem approximation {N S Q a b c d : ℤ} (B : Bracket N S Q a b c d) :
    let z := choose N S a b c d
    0 < z.2 ∧ z.2 ≤ Q ∧ |z.1*S-z.2*N| *(Q+1) ≤ S := by
  let x := b*N-a*S
  let y := c*S-d*N
  have xp : 0 ≤ x := sub_nonneg.mpr B.left
  have yp : 0 ≤ y := sub_nonneg.mpr B.right
  have terminal := B.terminal
  have identity : d*x+b*y = S := by
    dsimp only [x,y]
    linear_combination S*B.det
  have h : (b+d)*min x y ≤ S := by
    calc
      (b+d)*min x y = b*min x y + d*min x y := add_mul ..
      _ ≤ b*y+d*x := add_le_add (mul_le_mul_of_nonneg_left (min_le_right ..) B.bpos.le)
        (mul_le_mul_of_nonneg_left (min_le_left ..) B.dpos.le)
      _ = S := by linarith only [identity]
  have small := (mul_le_mul_of_nonneg_right (show Q+1 ≤ b+d by omega) (le_min xp yp)).trans h
  have legal : 0 < (choose N S a b c d).2 ∧ (choose N S a b c d).2 ≤ Q := by
    unfold choose
    split
    · exact ⟨B.bpos,B.bcap⟩
    · exact ⟨B.dpos,B.dcap⟩
  refine ⟨legal.1,legal.2,?_⟩
  rw [selected_error B,mul_comm]
  exact small

/-- No signed numerator and positive denominator within budget improves on
the chosen endpoint's absolute cross-product error, including at an endpoint
or a mediant tie. -/
theorem optimal {N S Q a b c d : ℤ} (B : Bracket N S Q a b c d) (u v : ℤ)
    (vp : 0 < v) (vcap : v ≤ Q) :
    let z := choose N S a b c d
    |z.1*S-z.2*N| ≤ |u*S-v*N| := by
  dsimp only
  rw [selected_error B]
  let X := b*N-a*S
  let Y := c*S-d*N
  let l := c*v-d*u
  let r := b*u-a*v
  have xp : 0 ≤ X := sub_nonneg.mpr B.left
  have yp : 0 ≤ Y := sub_nonneg.mpr B.right
  have den : b*l+d*r = v := by
    dsimp only [l,r]
    linear_combination v*B.det
  have signed : u*S-v*N = r*Y-l*X := by
    dsimp only [X,Y,l,r]
    linear_combination (v*N-u*S)*B.det
  change min X Y ≤ |u*S-v*N|
  rw [signed]
  have terminal := B.terminal
  by_cases lp : 1 ≤ l
  · have rn : r ≤ 0 := by
      by_contra! proper
      have bl := mul_le_mul_of_nonneg_left lp B.bpos.le
      have dr := mul_le_mul_of_nonneg_left (show 1≤r by omega) B.dpos.le
      nlinarith only [den, bl, dr, terminal, vcap]
    have bad := mul_nonpos_of_nonpos_of_nonneg rn yp
    have atLeast := mul_le_mul_of_nonneg_right lp xp
    apply (min_le_left X Y).trans
    exact (show X ≤ -(r*Y-l*X) by nlinarith only [bad,atLeast]).trans (neg_le_abs _)
  · have ln : l ≤ 0 := by omega
    have rp : 1 ≤ r := by
      by_contra! bad
      have first := mul_nonpos_of_nonneg_of_nonpos B.bpos.le ln
      have second := mul_nonpos_of_nonneg_of_nonpos B.dpos.le (show r≤0 by omega)
      linarith only [first,second,den,vp]
    have bad := mul_nonpos_of_nonpos_of_nonneg ln xp
    have atLeast := mul_le_mul_of_nonneg_right rp yp
    apply (min_le_right X Y).trans
    exact (show Y ≤ r*Y-l*X by nlinarith only [bad,atLeast]).trans (le_abs_self _)

/-- Instead of selecting a fresh direction for every block, compute the
inclusive band of chord products S for which a direction is certified.
Signed Euclidean division accounts for the rounded lower endpoint. -/
theorem certificate_band {N S Q u v : ℤ} (up : 1 ≤ u) (qp : 1 ≤ Q) :
    |u*S-v*N| *(Q+1) ≤ S ↔
      -((-(v*N*(Q+1))) / (u*(Q+1)+1)) ≤ S ∧
      S ≤ (v*N*(Q+1)) / (u*(Q+1)-1) := by
  have kp : 0 < Q+1 := by omega
  have big := mul_le_mul_of_nonneg_right up kp.le
  have hp : 0 < u*(Q+1)+1 := by nlinarith only [big,qp]
  have hm : 0 < u*(Q+1)-1 := by nlinarith only [big,qp]
  have bot : -((-(v*N*(Q+1))) / (u*(Q+1)+1)) ≤ S ↔
      -(S*(u*(Q+1)+1)) ≤ -(v*N*(Q+1)) := by
    rw [show -((-(v*N*(Q+1))) / (u*(Q+1)+1)) ≤ S ↔
      -S ≤ (-(v*N*(Q+1))) / (u*(Q+1)+1) by omega,
      Int.le_ediv_iff_mul_le hp, neg_mul]
  rw [bot,Int.le_ediv_iff_mul_le hm, ← abs_of_pos kp, ← abs_mul, abs_of_pos kp, abs_le]
  constructor <;> rintro ⟨l,h⟩ <;> constructor <;> nlinarith only [l,h]

/-- Integer determinant separation. If the cross-product error is below
S/(2Q), every *distinct* slope within budget has strictly larger error. -/
theorem forces_slope {N S Q u v f g : ℤ} (sp : 0 < S) (vp : 0 < v) (vcap : v ≤ Q)
    (gp : 0 < g) (gcap : g ≤ Q) (different : u*g ≠ f*v)
    (small : 2*Q*|u*S-v*N| < S) : |u*S-v*N| < |f*S-g*N| := by
  let E := |u*S-v*N|
  let F := |f*S-g*N|
  have ep : 0 ≤ E := abs_nonneg _
  have unit : (1:ℤ) ≤ |u*g-f*v| := by
    have nonzero : u*g-f*v ≠ 0 := sub_ne_zero.mpr different
    have := abs_pos.mpr nonzero
    omega
  have ident : (u*g-f*v)*S = g*(u*S-v*N)-v*(f*S-g*N) := by ring
  have triangle : S ≤ g*E+v*F := calc
    S = 1*S := (one_mul S).symm
    _ ≤ |u*g-f*v| *S := mul_le_mul_of_nonneg_right unit sp.le
    _ = |(u*g-f*v)*S| := by rw [abs_mul,abs_of_pos sp]
    _ ≤ g*E+v*F := by
      rw [ident]
      have tri := abs_sub (g*(u*S-v*N)) (v*(f*S-g*N))
      simpa only [abs_mul,abs_of_pos gp,abs_of_pos vp,E,F] using tri
  change 2*Q*E < S at small
  change E < F
  by_contra! bad
  have first := mul_le_mul_of_nonneg_right gcap ep
  have second := (mul_le_mul_of_nonneg_left bad vp.le).trans (mul_le_mul_of_nonneg_right vcap ep)
  nlinarith only [triangle,small,first,second]

/-- A current and next pair of ordinary convergents bracket the input, have
unit determinant, and straddle the denominator budget at the stopping step.
Those three integer tests certify the current convergent as a minimizer. -/
theorem last_convergent_best {N S Q p q r s u v : ℤ}
    (qp : 0 < q) (qc : q ≤ Q) (over : Q < s)
    (det : |q*r-p*s| = 1) (sides : (p*S-q*N)*(r*S-s*N) ≤ 0)
    (vp : 0 < v) (vcap : v ≤ Q) : |p*S-q*N| ≤ |u*S-v*N| := by
  let D := q*r-p*s
  let l := (r*v-u*s)*D
  let t := (u*q-p*v)*D
  let E := p*S-q*N
  let F := r*S-s*N
  have d2 : D^2 = 1 := by
    change |D| = 1 at det
    rw [← sq_abs D,det,one_pow]
  have den : q*l+s*t = v := calc
    q*l+s*t = v*D^2 := by dsimp only [l,t,D]; ring
    _ = v := by rw [d2,mul_one]
  have err : u*S-v*N = l*E+t*F := calc
    u*S-v*N = (u*S-v*N)*D^2 := by rw [d2,mul_one]
    _ = l*E+t*F := by dsimp only [l,t,D,E,F]; ring
  have sp : 0 < s := by omega
  have signs : l ≠ 0 ∧ l*t ≤ 0 := by
    by_cases tp : 1 ≤ t
    · have lp : l < 0 := by
        apply lt_of_not_ge
        intro bad
        have a := mul_nonneg qp.le bad
        have b := mul_le_mul_of_nonneg_left tp sp.le
        nlinarith only [den,over,vcap,a,b]
      exact ⟨by omega,mul_nonpos_of_nonpos_of_nonneg lp.le (by omega)⟩
    · have tn : t ≤ 0 := by omega
      have lp : 0 < l := by
        apply lt_of_not_ge
        intro bad
        have a := mul_nonpos_of_nonneg_of_nonpos qp.le bad
        have b := mul_nonpos_of_nonneg_of_nonpos sp.le tn
        linarith only [den,vp,a,b]
      exact ⟨by omega,mul_nonpos_of_nonneg_of_nonpos lp.le tn⟩
  have nonzero : 1 ≤ |l| := by have := abs_pos.mpr signs.1; omega
  have sq : (1:ℤ)^2 ≤ l^2 := sq_le_sq.mpr (by simpa using nonzero)
  have cross := mul_nonneg_of_nonpos_of_nonpos signs.2 sides
  change 0 ≤ (l*t)*(E*F) at cross
  rw [err]
  change |E| ≤ |l*E+t*F|
  apply sq_le_sq.mp
  nlinarith only [mul_le_mul_of_nonneg_right sq (sq_nonneg E),cross,sq_nonneg (t*F)]

/-- A small-error candidate must equal the last convergent as a rational
direction, as certified either by exact termination or by the next convergent
crossing the budget. Unreduced directions can represent the same slope. -/
theorem forced_last {N S Q u v p q : ℤ} (sp : 0 < S) (vp : 0 < v) (vcap : v ≤ Q)
    (qp : 0 < q) (qc : q ≤ Q)
    (stop : p*S=q*N ∨ ∃ r s : ℤ, Q<s ∧ |q*r-p*s| =1 ∧ (p*S-q*N)*(r*S-s*N)≤0)
    (small : 2*Q*|u*S-v*N| < S) : u*q=p*v := by
  by_contra different
  have better := forces_slope sp vp vcap qp qc different small
  rcases stop with exactEnd | ⟨r,s,over,det,sides⟩
  · rw [exactEnd,sub_self,abs_zero] at better
    exact not_lt_of_ge (abs_nonneg _) better
  · exact not_lt_of_ge (last_convergent_best qp qc over det sides vp vcap) better

/-- The exact last full strip satisfying an upper bound on its chord product.
The first strip has lower endpoint A, adjacent starts differ by W, and d is
the common endpoint distance. The square root is taken once for the run. -/
theorem last_index {A W d U : ℕ} (wp : 0 < W) (start : A*(A+d) ≤ U) (j : ℕ) :
    (A+W*j)*(A+W*j+d) ≤ U ↔
      j ≤ ((4*U+d^2).sqrt-(2*A+d))/(2*W) := by
  have quad (z : ℕ) : z*(z+d) ≤ U ↔ 2*z+d ≤ (4*U+d^2).sqrt := by
    rw [Nat.le_sqrt']
    constructor <;> intro h <;> nlinarith only [h]
  have first := (quad A).mp start
  rw [quad,Nat.le_div_iff_mul_le (by omega : 0 < 2*W)]
  have cancel := Nat.sub_add_cancel first
  constructor <;> intro h <;> nlinarith only [h,cancel]

/-- For a certified first block the complete set of subsequent equal-width
blocks certified by the same direction is a prefix, with this exact last
index. A clipped final block may have a different cap and chord length. -/
theorem certified_run {N Q u v : ℤ} {A W d : ℕ} (up : 1 ≤ u) (qp : 1 ≤ Q) (wp : 0 < W)
    (first : |u*((A*(A+d):ℕ):ℤ)-v*N| * (Q+1) ≤ (A*(A+d):ℕ)) (j : ℕ) :
    let T := (A+W*j)*(A+W*j+d)
    let U := ((v*N*(Q+1))/(u*(Q+1)-1)).toNat
    |u*(T:ℤ)-v*N| * (Q+1) ≤ (T:ℤ) ↔
      j ≤ ((4*U+d^2).sqrt-(2*A+d))/(2*W) := by
  let T := (A+W*j)*(A+W*j+d)
  let U := v*N*(Q+1)/(u*(Q+1)-1)
  have init := (certificate_band up qp).mp first
  change _ ∧ ((A*(A+d):ℕ):ℤ) ≤ U at init
  have Upos : 0 ≤ U := (Int.natCast_nonneg _).trans init.2
  have castU : (U.toNat:ℤ) = U := Int.toNat_of_nonneg Upos
  have base : A*(A+d) ≤ U.toNat := by exact_mod_cast (init.2.trans_eq castU.symm)
  have monotone : A*(A+d) ≤ T := Nat.mul_le_mul (by omega) (by omega)
  have changeUpper : (T:ℤ) ≤ U ↔ T ≤ U.toNat := by rw [←castU]; exact_mod_cast Iff.rfl
  change |u*(T:ℤ)-v*N| * (Q+1) ≤ (T:ℤ) ↔ _
  rw [certificate_band up qp, and_iff_right (init.1.trans (by exact_mod_cast monotone)),
    changeUpper]
  exact last_index wp base j

/-- The same chosen direction covers the full factor arc in five consecutive
levels. Factor labels are certified on each block using its own endpoints. -/
theorem same_five_cover {N A B Q a b c d : ℤ} (ap : 0 < A) (length : A+2 ≤ B)
    (np : 0 < N) (balance : N ≤ 2*A^2) (width : (B-A)^6 ≤ 64*N)
    (budget : Q = (B-A)/2) (bracket : Bracket N (A*B) Q a b c d) :
    let z := choose N (A*B) a b c d
    ∃ L : ℤ, ∀ x y : ℤ, A ≤ x → x ≤ B → 0 ≤ y → N = x*y →
      L ≤ z.1*x+z.2*y ∧ z.1*x+z.2*y ≤ L+4 := by
  let z := choose N (A*B) a b c d
  obtain ⟨vp,vcap,approx⟩ := approximation bracket
  change 0 < z.2 at vp
  change z.2 ≤ Q at vcap
  let D := QuotientStripLevels.scale A B
  let R := QuotientStripLevels.tilt A B N z.1 z.2*(B-A)
  let O := QuotientStripLevels.origin A B N z.1 z.2
  let low := O+min 0 R-z.2*N*(B-A)^2
  let high := O+max 0 R
  have span := QuotientStripLevels.width_lt_five (d:=B-A) (u:=z.1) (v:=z.2) (Q:=Q)
    ap rfl (by omega) np balance width (by omega) (by omega) approx
  have len : high-low = |R|+z.2*N*(B-A)^2 := by
    dsimp only [low,high]
    rcases le_total 0 R with side|side
    · rw [min_eq_left side,max_eq_right side,abs_of_nonneg side]; ring
    · rw [min_eq_right side,max_eq_left side,abs_of_nonpos side]; ring
  have bp : 0 < B := by omega
  have dp : 0 < D := by dsimp only [D,QuotientStripLevels.scale]; positivity
  refine ⟨-((-low)/D),?_⟩
  intro x y left right yp prod
  have fit := QuotientStripLevels.enclosure (u:=z.1) ap left right yp vp.le prod
  exact QuotientStripLevels.five_labels dp (len.trans_lt span) _ fit.1 fit.2

end PrimeFactors.QuotientStripFareyRuns
