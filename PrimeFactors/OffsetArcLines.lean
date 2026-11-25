import PrimeFactors.RootIntervalSlope
import Mathlib.Tactic.LinearCombination

namespace PrimeFactors.OffsetArcLines

/-- The extreme correction to a projected level comes from one of the two end indices. -/
theorem index_bounds {i W e : ℤ} (h₀ : 0 ≤ i) (hW : i ≤ W) :
    min 0 (e*W) ≤ e*i ∧ e*i ≤ max 0 (e*W) := by
  by_cases h : 0 ≤ e
  · exact ⟨(min_le_left ..).trans (mul_nonneg h h₀),
      (mul_le_mul_of_nonneg_left hW h).trans (le_max_right ..)⟩
  · exact ⟨(min_le_right ..).trans (mul_le_mul_of_nonpos_left hW (by omega)),
      (mul_nonpos_of_nonpos_of_nonneg (by omega) h₀).trans (le_max_left ..)⟩

/-- Public interval of integer levels for all lattice points of a rational strip. -/
theorem level_bounds {D A l u i y W p q : ℤ}
    (q₀ : 0 ≤ q) (i₀ : 0 ≤ i) (iW : i ≤ W)
    (lo : l ≤ D*y-A*i) (hi : D*y-A*i ≤ u) :
    q*l + min 0 ((q*A-p*D)*W) ≤ D*(q*y-p*i) ∧
    D*(q*y-p*i) ≤ q*u + max 0 ((q*A-p*D)*W) := by
  have eqn : D*(q*y-p*i) = q*(D*y-A*i)+(q*A-p*D)*i := by ring
  rw [eqn]
  have bounds := index_bounds (e := q*A-p*D) i₀ iW
  exact ⟨add_le_add (mul_le_mul_of_nonneg_left lo q₀) bounds.1,
    add_le_add (mul_le_mul_of_nonneg_left hi q₀) bounds.2⟩

/-- On one signed remainder class the rounded conic bounds give such a strip. -/
theorem signed_strip {a b M Sstep r β i y z l u : ℤ}
    (gap : z = r+β*i+M*y) (band : l ≤ b*z-a*Sstep*i ∧ b*z-a*Sstep*i ≤ u) :
    l-b*r ≤ (b*M)*y-(a*Sstep-b*β)*i ∧
    (b*M)*y-(a*Sstep-b*β)*i ≤ u-b*r := by
  rw [gap] at band
  constructor <;> linarith only [band.1,band.2]

theorem level_span {q p D A l u W : ℤ} (hW : 0 ≤ W) :
    (q*u + max 0 ((q*A-p*D)*W)) - (q*l + min 0 ((q*A-p*D)*W))
      = q*(u-l) + |q*A-p*D| *W := by
  by_cases h : 0 ≤ q*A-p*D
  · have hn := mul_nonneg h hW
    rw [max_eq_right hn,min_eq_left hn,abs_of_nonneg h]
    ring
  · have hn := mul_nonpos_of_nonpos_of_nonneg (by omega : q*A-p*D ≤ 0) hW
    rw [max_eq_left hn,min_eq_right hn,abs_of_nonpos (by omega : q*A-p*D ≤ 0)]
    ring

/-- The sole possible level is floor(upper/D), including when the strip is empty. -/
theorem unique_level {D lower upper t : ℤ} (hd : 0<D) (h : upper-lower<D)
    (lo : lower ≤ D*t) (hi : D*t ≤ upper) : t = upper / D := by
  apply le_antisymm
  · apply (Int.le_ediv_iff_mul_le hd).2
    simpa [mul_comm] using hi
  · have next : upper < (t+1)*D := by nlinarith only [lo,h]
    have := (Int.ediv_lt_iff_lt_mul hd).2 next
    omega

/-- A strip of normalized area at most 1/4 admits a publicly selected single line. -/
theorem small_strip {D W : ℕ} {A l u : ℤ}
    (hD : 0<D) (hW : 0<W) (hu : l≤u) (small : 4*(W:ℤ)*(u-l) ≤ (D:ℤ)) :
    ∃ (q : ℕ) (p : ℤ), 1 ≤ q ∧ q ≤ 2*W ∧
      (q:ℤ)*(u-l)+|(q:ℤ)*A-p*D| *W < D := by
  obtain ⟨q,low,high,p,h⟩ := PrimeFactors.boundedSlope_exists D (2*W) A hD (by omega)
  have err : |(q:ℤ)*A-p*D| * (2*(W:ℤ)+1) ≤ D := by
    simpa [mul_comm p (D:ℤ)] using h
  have qsmall : (q:ℤ)*(u-l) ≤ (2*(W:ℤ))*(u-l) := by
    apply mul_le_mul_of_nonneg_right _ (by omega)
    exact_mod_cast high
  have twice : 2*(|(q:ℤ)*A-p*D| *(W:ℤ)) < D := by
    by_cases hz : |(q:ℤ)*A-p*D|=0
    · rw [hz]; simpa using hD
    · have hp := abs_nonneg ((q:ℤ)*A-p*D)
      nlinarith only [err, show 0 < |(q:ℤ)*A-p*D| by omega]
  refine ⟨q,p,low,high,?_⟩
  linarith only [qsmall,small,twice]

/-- Both the direction and the sole possible level depend only on the public strip. -/
theorem public_line {D W : ℕ} {A l u : ℤ}
    (hD : 0<D) (hW : 0<W) (hu : l≤u) (small : 4*(W:ℤ)*(u-l) ≤ (D:ℤ)) :
    ∃ (q : ℕ) (p t : ℤ), 1≤q ∧ q≤2*W ∧
      ∀ i y : ℤ, 0 ≤ i → i ≤ W → l ≤ (D:ℤ)*y-A*i → (D:ℤ)*y-A*i ≤ u →
        (q:ℤ)*y-p*i=t := by
  obtain ⟨q,p,hq,qw,thin⟩ := small_strip (A:=A) hD hW hu small
  refine ⟨q,p,((q:ℤ)*u+max 0 (((q:ℤ)*A-p*D)*W))/D,hq,qw,?_⟩
  intro i y ilo ihi lo hi
  have bounds := level_bounds (p:=p) (q:= (q:ℤ)) (by positivity) ilo ihi lo hi
  apply unique_level (by exact_mod_cast hD) _ bounds.1 bounds.2
  rwa [level_span (by positivity : (0:ℤ) ≤ W)]

/-- A thicker strip admits a direction with normalized projection length at most
twice the square root of its normalized area. The numerator is squared to avoid real roots. -/
theorem square_root_width {D W H : ℕ} (A : ℤ) (hd : 0<D) (hh : 0<H) (size : H≤W*D) :
    ∃ (q : ℕ) (p : ℤ), 1≤q ∧ q≤(W*D/H).sqrt ∧
      ((q:ℤ)*H+(W:ℤ)*|((q:ℤ)*A-p*D)|)^2 ≤ 4*(W:ℤ)*D*H := by
  let B := (W*D/H).sqrt
  have s₁ : B^2*H≤W*D := (PrimeFactors.rootIntervalSlope_width (N:=W*D) hh).1
  have s₂ : W*D<(B+1)^2*H := (PrimeFactors.rootIntervalSlope_width (N:=W*D) hh).2
  have bpos : 0<B := by
    by_contra h
    have : B=0 := by omega
    simp [this] at s₂
    omega
  obtain ⟨q,qlo,qhi,p,approx⟩ := PrimeFactors.boundedSlope_exists D B A hd bpos
  let e : ℤ := |(q:ℤ)*A-p*D|
  have err : e*((B:ℤ)+1) ≤ D := by simpa [e,mul_comm p (D:ℤ)] using approx
  have qr : q^2*H≤W*D := (Nat.mul_le_mul_right H (Nat.pow_le_pow_left qhi 2)).trans s₁
  have qr' : (q:ℤ)^2*H≤(W:ℤ)*D := by exact_mod_cast qr
  have f₁ := mul_le_mul_of_nonneg_right qr' (by positivity : (0:ℤ)≤H)
  have scaled : ((W:ℤ)*e*((B:ℤ)+1))^2 ≤ ((W:ℤ)*D)^2 := by
    apply pow_le_pow_left₀ (by dsimp [e]; positivity)
    have x := mul_le_mul_of_nonneg_left err (by positivity : (0:ℤ)≤W)
    linarith only [x]
  have sz : (W:ℤ)*D≤((B:ℤ)+1)^2*H := by exact_mod_cast s₂.le
  have rhs := mul_le_mul_of_nonneg_left sz (by positivity : (0:ℤ)≤(W:ℤ)*D)
  have f₂ : ((W:ℤ)*e)^2 ≤ (W:ℤ)*D*H := by
    apply le_of_mul_le_mul_right ?_ (by positivity : (0:ℤ)<((B:ℤ)+1)^2)
    nlinarith only [scaled,rhs]
  refine ⟨q,p,qlo,qhi,?_⟩
  change ((q:ℤ)*H+(W:ℤ)*e)^2 ≤ 4*(W:ℤ)*D*H
  nlinarith only [f₁,f₂,sq_nonneg ((q:ℤ)*H-(W:ℤ)*e)]

/-- Every possible square on a line satisfies a quadratic with public coefficients. -/
theorem line_quadratic {i S Δ F G q w P : ℤ}
    (line : q*w=F+G*i) (square : w^2=(S+Δ*i)^2-P) :
    (G^2-(q*Δ)^2)*i^2+2*(F*G-q^2*S*Δ)*i+F^2-q^2*(S^2-P)=0 := by
  have h : (F+G*i)^2=q^2*((S+Δ*i)^2-P) := by rw [←line,mul_pow,square]
  linear_combination h

/-- The quadratic cannot vanish identically for a positive radicand product and nonzero step. -/
theorem line_nonzero {S Δ F G q P : ℤ} (hd : Δ≠0) (hq : q≠0) (hp : P≠0) :
    G^2-(q*Δ)^2≠0 ∨ 2*(F*G-q^2*S*Δ)≠0 ∨ F^2-q^2*(S^2-P)≠0 := by
  by_contra h
  push_neg at h
  have h1 : G^2=(q*Δ)^2 := by linarith only [h.1]
  have h2 : F*G=q^2*S*Δ := by linarith only [h.2.1]
  have h3 : F^2=q^2*(S^2-P) := by linarith only [h.2.2]
  have hz : (q^2*S*Δ)^2 = (q^2*(S^2-P))*(q*Δ)^2 := by
    rw [←h2,mul_pow,h1,h3]
  have hzero : q^4*Δ^2*P=0 := by linear_combination hz
  exact (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hq) (pow_ne_zero _ hd)) hp) hzero

private theorem difference_of_two_roots {a b c i j : ℤ} (ne : i≠j)
    (left : a*i^2+b*i+c=0) (right : a*j^2+b*j+c=0) :
    a*(i+j)+b=0 := by
  have eqn : (i-j)*(a*(i+j)+b)=0 := by linear_combination left-right
  exact (mul_eq_zero.mp eqn).resolve_left (sub_ne_zero.mpr ne)

/-- In particular a nonzero (possibly linear or constant) equation cannot contain three
distinct integer positions. Its coefficients can be supplied by line_quadratic and line_nonzero. -/
theorem at_most_two {a b c i j k : ℤ} (nonzero : a≠0 ∨ b≠0 ∨ c≠0)
    (first : a*i^2+b*i+c=0) (second : a*j^2+b*j+c=0) (third : a*k^2+b*k+c=0) :
    i=j ∨ i=k ∨ j=k := by
  by_contra h
  push_neg at h
  have h₁ := difference_of_two_roots h.1 first second
  have h₂ := difference_of_two_roots h.2.1 first third
  have hz : a*(j-k)=0 := by linear_combination h₁-h₂
  have ha := (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr h.2.2)
  simp [ha] at h₁
  simp [ha,h₁] at first
  simp [ha,h₁,first] at nonzero

/-- A single public square discriminant per projected line, already divided by (2q)^2. -/
theorem line_discriminant {S S₀ Δ i F G q w P : ℤ}
    (trace : S=S₀+Δ*i) (line : q*w=F+G*i) (square : w^2=S^2-P) :
    (G*w-q*Δ*S)^2 = (G*S₀-Δ*F)^2-P*(G^2-(q*Δ)^2) := by
  have hx : G*S-q*Δ*w=G*S₀-Δ*F := by rw [trace]; linear_combination -Δ*line
  rw [←hx]
  linear_combination (G^2-(q*Δ)^2)*square

/-- Recovery from a signed square root Y needs only this linear equation for the trace. -/
theorem reconstruct_trace (S w G q Δ : ℤ) :
    G*(G*S-q*Δ*w)+q*Δ*(G*w-q*Δ*S) = (G^2-(q*Δ)^2)*S := by ring

/-- Two distinct normal directions have determinant divisible by D in remainder coordinates. -/
theorem independent_width {q p q₀ p₀ D A : ℤ}
    (hd : 0<D) (nonparallel : q*p₀≠q₀*p) (hq : 0≤q) (hq₀ : 0≤q₀) :
    D ≤ q₀*|q*A-p*D|+q*|q₀*A-p₀*D| := by
  have eqn : q₀*(q*A-p*D)-q*(q₀*A-p₀*D)=D*(q*p₀-q₀*p) := by ring
  have habs : 1 ≤ |q*p₀-q₀*p| := by
    by_cases h : 0≤q*p₀-q₀*p
    · rw [abs_of_nonneg h]; omega
    · rw [abs_of_nonpos (by omega : q*p₀-q₀*p≤0)]; omega
  calc D ≤ D*|q*p₀-q₀*p| := by simpa using mul_le_mul_of_nonneg_left habs hd.le
       _ = |q₀*(q*A-p*D)-q*(q₀*A-p₀*D)| := by rw [eqn,abs_mul,abs_of_pos hd]
       _ ≤ _ := by simpa [abs_mul,abs_of_nonneg hq,abs_of_nonneg hq₀]
                     using abs_sub (q₀*(q*A-p*D)) (q*(q₀*A-p₀*D))

/-- A certificate giving a lower width for every integral choice of line direction.
The primitive reference direction is witnessed by its two Bézout coefficients. -/
theorem all_widths {q p q₀ p₀ D A W H m x y : ℤ}
    (hd : 0<D) (hq : 0<q) (hq₀ : 0<q₀) (hW : 0≤W) (hH : 0≤H) (hm : 0≤m)
    (bez : x*q₀+y*p₀=1) (rw : m*q₀≤W) (rh : m*|q₀*A-p₀*D| ≤H)
    (refwidth : m*D≤q₀*H+W*|q₀*A-p₀*D|) :
    m*D ≤ q*H+W*|q*A-p*D| := by
  by_cases parallel : q*p₀=q₀*p
  · let t := x*q+y*p
    have eqQ : q=q₀*t := by dsimp [t]; linear_combination -q*bez+y*parallel
    have eqP : p=p₀*t := by dsimp [t]; linear_combination -p*bez-x*parallel
    have ht : 1≤t := by
      by_contra h
      have := mul_nonpos_of_nonneg_of_nonpos hq₀.le (show t≤0 by omega)
      omega
    have e : q*A-p*D=t*(q₀*A-p₀*D) := by
      rw [eqQ,eqP]
      ring
    have width : q*H+W*|q*A-p*D| = t*(q₀*H+W*|q₀*A-p₀*D|) := by
      rw [e,abs_mul,abs_of_nonneg (by omega : 0≤t),eqQ]; ring
    rw [width]
    apply refwidth.trans
    have pos := add_nonneg (mul_nonneg hq₀.le hH) (mul_nonneg hW (abs_nonneg (q₀*A-p₀*D)))
    simpa using mul_le_mul_of_nonneg_right ht pos
  · have det := independent_width (A:=A) hd parallel hq.le hq₀.le
    have d := mul_le_mul_of_nonneg_left det hm
    have r₁ := mul_le_mul_of_nonneg_right rw (abs_nonneg (q*A-p*D))
    have r₂ := mul_le_mul_of_nonneg_left rh hq.le
    linarith only [d,r₁,r₂]

/-- An interval with width at least m in level units contains m successive levels. -/
theorem consecutive_levels {D l u m : ℤ} (d : 0<D) (len : m*D≤u-l) :
    ∃ t : ℤ, ∀ i : ℤ, 0 ≤ i → i < m → l ≤ D*(t+i) ∧ D*(t+i) ≤ u := by
  refine ⟨u/D-m+1,?_⟩
  intro i low high
  have upper := Int.ediv_mul_le u d.ne'
  have lower := Int.emod_lt_of_pos u d
  have quot := Int.emod_add_ediv u D
  have hmul := mul_le_mul_of_nonneg_right (show u/D-m+1+i≤u/D by omega) d.le
  have hlow := mul_nonneg d.le low
  constructor
  · nlinarith only [lower,len,hlow,quot]
  · simpa [mul_comm] using hmul.trans upper

/-- The negative signed-gap band containing the 49-bit winner has 40 offsets, all on
one public line if they pass this strip. -/
theorem holdout_band {i y : ℤ} (lo : 0 ≤ i) (hi : i ≤ 39)
    (lower : 64647442314≤90839092032*y-24892268478*i)
    (upper : 90839092032*y-24892268478*i≤64649408295) :
    770*y-211*i=548 := by
  have h := level_bounds (q:=770) (p:=211) (by decide) lo hi lower upper
  norm_num at h
  omega

/-- Intersecting the line with the conic recovers only index 12. -/
theorem holdout_index {i w : ℤ}
    (line : 770*w=12066767458+29327916*i)
    (square : w^2=(104051024105+6*i)^2-10826615372164287133104) : i=12 := by
  have h := line_quadratic line square
  have hz : 3105609984*(i-12)*(276959*i-7146558)=0 := by
    linear_combination h
  clear h line square
  rcases mul_eq_zero.mp hz with vanish | vanish
  · have hstep := (mul_eq_zero.mp vanish).resolve_left (by decide)
    omega
  · omega

end PrimeFactors.OffsetArcLines
