import PrimeFactors.MidpointWeightLattice
import Mathlib.Data.Nat.Sqrt

namespace PrimeFactors.HexagonalWeights

/-- Two diagonals at signed gaps i and i-c have a constant combined length
2m-c. This parametrizes an integer strip with no boundary correction. -/
private def point (m c : ℕ) (p : Fin c × Fin (2*m-c)) : ℤ × ℤ :=
  let i : ℤ := p.1
  let j : ℤ := p.2
  if j < m-i then (j+i,j) else (j-(m-i),j-(m-i)+(c-i))

private theorem point_bounds {m c : ℕ} (p : Fin c × Fin (2*m-c)) :
    let (x,y) := point m c p
    0≤x ∧ x<m ∧ 0≤y ∧ y<m ∧ -(c:ℤ)≤x-y ∧ x-y<c := by
  have i := p.1.isLt
  have j := p.2.isLt
  dsimp only [point]
  split <;> dsimp <;> omega

private theorem point_inj {m c : ℕ} : Function.Injective (point m c) := by
  intro p q eq
  have ip := p.1.isLt
  have iq := q.1.isLt
  by_cases hp : (p.2:ℤ) < m-(p.1:ℤ) <;> by_cases hq : (q.2:ℤ) < m-(q.1:ℤ) <;>
    simp only [point, hp, hq, ↓reduceIte, Prod.mk.injEq] at eq <;>
    apply Prod.ext <;> apply Fin.ext <;> omega

private theorem diamond_lt {x y r : ℤ} (plus : |x+y| < r) (minus : |x-y| < r) :
    |x| + |y| < r := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy <;>
    rw [abs_lt] at plus minus
  · rw [abs_of_nonneg hx, abs_of_nonneg hy]; omega
  · rw [abs_of_nonneg hx, abs_of_nonpos hy]; omega
  · rw [abs_of_nonpos hx, abs_of_nonneg hy]; omega
  · rw [abs_of_nonpos hx, abs_of_nonpos hy]; omega

/-- For every slope the smaller threshold supplies a nonzero stationary
weight in the open hexagon. Its three pairs of faces bound the trace. -/
theorem exists_weights (H G R : ℕ) (hh : 0<H) (hg : 3*H<G) (hr : 0<R)
    (area : 4*H*G^2 < (G+3*H)*R^3) (s : ℤ) :
    ∃ A B : ℤ, (A≠0 ∨ B≠0) ∧ B ≡ s*A [ZMOD (R:ℤ)] ∧
      (G:ℤ)*|A-B| < (R:ℤ)^2 ∧ H*|A+B| + (G-3*H:ℤ)*|A-B| < (R:ℤ)^2 := by
  let D := G-3*H
  have dpos : 0<D := Nat.sub_pos_of_lt hg
  have dg : D+3*H=G := Nat.sub_add_cancel hg.le
  have gpos : 0<G := by omega
  let m := G*R^2
  let c := D*R^2
  have two : 2*m-c = (G+3*H)*R^2 := by
    have h : 2*m = c+(G+3*H)*R^2 := by
      dsimp only [m,c]; nlinarith [congrArg (·*R^2) dg]
    omega
  have size : 4*(H*G)*(D*G)*R < Fintype.card (Fin c × Fin (2*m-c)) := by
    simp only [Fintype.card_prod, Fintype.card_fin, two, c]
    have growth := Nat.mul_lt_mul_of_pos_right area (Nat.mul_pos dpos hr)
    nlinarith only [growth]
  obtain ⟨p,q,ne,A,B,lane,dx,dy⟩ :=
    MidpointWeightLattice.lattice_collision (point m c) (H*G) (D*G) R
      (Nat.mul_pos hh gpos) (Nat.mul_pos dpos gpos) hr size s
  have bp := point_bounds p
  have bq := point_bounds q
  change 0≤(point m c p).1 ∧ _ ∧ 0≤(point m c p).2 ∧ _ ∧
    -(c:ℤ)≤(point m c p).1-(point m c p).2 ∧ (point m c p).1-(point m c p).2<c at bp
  change 0≤(point m c q).1 ∧ _ ∧ 0≤(point m c q).2 ∧ _ ∧
    -(c:ℤ)≤(point m c q).1-(point m c q).2 ∧ (point m c q).1-(point m c q).2<c at bq
  have pmax : (point m c p).1<m ∧ (point m c p).2<m := ⟨bp.2.1,bp.2.2.2.1⟩
  have qmax : (point m c q).1<m ∧ (point m c q).2<m := ⟨bq.2.1,bq.2.2.2.1⟩
  have plus : |(point m c p).1-(point m c q).1| < m := abs_lt.mpr (by omega)
  have minus : |(point m c p).2-(point m c q).2| < m := abs_lt.mpr (by omega)
  have strip : |((point m c p).1-(point m c q).1)-
      ((point m c p).2-(point m c q).2)| < 2*c := abs_lt.mpr (by omega)
  rw [dx] at plus strip
  rw [dy] at minus strip
  have diamond := diamond_lt plus minus
  push_cast at diamond strip
  have dz : (D:ℤ)+3*H=G := by exact_mod_cast dg
  have deq : (D:ℤ) = (G:ℤ)-3*H := by omega
  have hm : (m:ℤ)=(G:ℤ)*(R:ℤ)^2 := by simp [m]
  have hc : (c:ℤ)=(D:ℤ)*(R:ℤ)^2 := by simp [c]
  rw [show (H:ℤ)*G*(A+B)+(D:ℤ)*G*(A-B)-((H:ℤ)*G*(A+B)-(D:ℤ)*G*(A-B)) =
    (2*(D:ℤ)*G)*(A-B) by ring, abs_mul, abs_of_nonneg (by positivity : 0≤2*(D:ℤ)*G)] at strip
  simp only [abs_mul, abs_of_nonneg (Int.natCast_nonneg H),
    abs_of_nonneg (Int.natCast_nonneg D), abs_of_nonneg (Int.natCast_nonneg G)] at diamond
  refine ⟨A,B,?_,lane,?_,?_⟩
  · by_contra! zeros
    rw [zeros.1, zeros.2] at dx dy
    simp only [add_zero, sub_zero, mul_zero] at dx dy
    exact ne (point_inj (Prod.ext (by omega) (by omega)))
  · apply (mul_lt_mul_left (by positivity : (0:ℤ)<2*D)).mp
    nlinarith only [strip,hc]
  · rw [←deq]
    apply (mul_lt_mul_left (by positivity : (0:ℤ)<G)).mp
    nlinarith only [diamond,hm]

/-- The tangent at the endpoints of the balanced arc is valid even after
rounding the upper midpoint and the maximum gap to integers. -/
theorem integer_tangent {h d N u g : ℤ} (balanced : 3*|d|≤h) (curve : h^2-d^2=N)
    (hi : 8*u^2 ≤ 9*N) (round : u < 3*(g+1)) :
    |d| ≤ g-3*(u-h) := by
  have non : 0 ≤ 3*h-|d| := by linarith [abs_nonneg d]
  have sq : (8*u)^2 ≤ (3*(3*h-|d|))^2 := by nlinarith [sq_nonneg (h-3*|d|), sq_abs d]
  have size : 8*u ≤ 3*(3*h-|d|) := by
    by_contra! bad
    nlinarith [mul_pos (show 0<8*u-3*(3*h-|d|) by omega)
      (show 0<8*u+3*(3*h-|d|) by omega)]
  omega

/-- The rounded endpoints used in the search satisfy both the tangent
rounding hypothesis and the aspect ratio needed for the four-vector search. -/
theorem rounded_parameters (N : ℕ) :
    let u := (9*N/8).sqrt
    let g := (N/8).sqrt
    let l := (N-1).sqrt+1
    u < 3*(g+1) ∧ 3*(u-l) ≤ g ∧ 8*u^2 ≤ 9*N := by
  let u := (9*N/8).sqrt
  let g := (N/8).sqrt
  let l := (N-1).sqrt+1
  have us : u^2 ≤ 9*N/8 := Nat.le_sqrt'.mp le_rfl
  have gs : N/8 < (g+1)^2 := Nat.sqrt_lt'.mp (by dsimp only [g]; omega)
  have ls : N-1 < l^2 := Nat.sqrt_lt'.mp (by dsimp only [l]; omega)
  have cap : 8*u^2 ≤ 9*N := by omega
  have limit : u < 3*(g+1) := by
    by_contra! bad
    have grow := Nat.mul_self_le_mul_self bad
    nlinarith [show N < 8*(g+1)^2 by omega]
  have rel : 8*u ≤ 9*l := by
    by_contra! bad
    have grow := Nat.mul_self_lt_mul_self bad
    nlinarith [show N ≤ l^2 by omega]
  exact ⟨limit, by omega, cap⟩

/-- The gap bound and its tangent bound imply the new width uniformly for
all pairs of feasible midpoint/gap points. -/
theorem width {H g l u x y h k d e : ℤ} (x0 : 0≤x) (y0 : 0≤y)
    (height : u-l=H) (rangeH : l≤h ∧ h≤u ∧ l≤k ∧ k≤u)
    (capD : |d| ≤ g-3*(u-h)) (capE : |e| ≤ g-3*(u-k)) :
    |x*(h-k)+y*(d-e)| ≤ max (2*g*y) (H*x+(2*g-3*H)*y) := by
  have bound (h k d e : ℤ) (top : h≤u) (bottom : l≤k) (kTop : k≤u)
      (hd : |d|≤g-3*(u-h)) (he : |e|≤g-3*(u-k)) :
      x*(h-k)+y*(d-e) ≤ max (2*g*y) (H*x+(2*g-3*H)*y) := by
    have cap : d-e ≤ 2*g-3*(u-k) := by linarith [le_abs_self d, neg_abs_le e]
    have b := mul_le_mul_of_nonneg_left cap y0
    have hsh := mul_nonneg (sub_nonneg.mpr top) x0
    by_cases sign : x≤3*y
    · apply le_trans _ (le_max_left ..)
      nlinarith [mul_nonneg (sub_nonneg.mpr kTop) (sub_nonneg.mpr sign)]
    · apply le_trans _ (le_max_right ..)
      nlinarith [mul_nonneg (sub_nonneg.mpr bottom) (by omega : 0≤x-3*y),
        congrArg (·*x) height, congrArg (·*y) height]
  rw [abs_le]
  have fwd := bound h k d e rangeH.2.1 rangeH.2.2.1 rangeH.2.2.2 capD capE
  have rev := bound k h e d rangeH.2.2.2 rangeH.1 rangeH.2.1 capE capD
  constructor <;> linarith

/-- The same hexagon bounds arbitrary signed weights: reflecting the
half-gaps or the entire trace preserves all absolute bounds. -/
theorem signed_width {H g l u x y h k d e : ℤ}
    (height : u-l=H) (levels : l≤h ∧ h≤u ∧ l≤k ∧ k≤u)
    (capD : |d| ≤ g-3*(u-h)) (capE : |e| ≤ g-3*(u-k)) :
    |x*(h-k)+y*(d-e)| ≤ max (2*g*|y|) (H*|x|+(2*g-3*H)*|y|) := by
  have positive (x : ℤ) (x0 : 0≤x) (y : ℤ) :
      |x*(h-k)+y*(d-e)| ≤ max (2*g*|y|) (H*x+(2*g-3*H)*|y|) := by
    rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hy]
      exact width x0 hy height levels capD capE
    · rw [abs_of_nonpos hy]
      have w := width x0 (neg_nonneg.mpr hy) height levels
        (by simpa only [abs_neg] using capD : |-d| ≤ g-3*(u-h))
        (by simpa only [abs_neg] using capE : |-e| ≤ g-3*(u-k))
      rwa [show (-y)*(-d- -e)=y*(d-e) by ring] at w
  rcases le_total 0 x with hx | hx
  · simpa only [abs_of_nonneg hx] using positive x hx y
  · have w := positive (-x) (neg_nonneg.mpr hx) (-y)
    rwa [abs_neg, show -x*(h-k)+ -y*(d-e) = -(x*(h-k)+y*(d-e)) by ring,
      abs_neg, ← abs_of_nonpos hx] at w

/-- The rounded aspect ratio implies V≤W and 2Z+V≤2W, where Z,V
are the two weighted coordinates and W is the hexagon score. -/
theorem score_bounds {H G a b : ℤ} (aspect : 6*H≤G) :
    let z := H*|a+b|
    let v := G*|a-b|
    let w := max v (z+(G-3*H)*|a-b|)
    v≤w ∧ 2*z+v≤2*w := by
  dsimp only
  constructor
  · exact le_max_left ..
  · have face := le_max_right (G*|a-b|) (H*|a+b|+(G-3*H)*|a-b|)
    nlinarith [mul_nonneg (sub_nonneg.mpr aspect) (abs_nonneg (a-b))]

/-- Every candidate whose hexagon score is no worse than the first
reduced basis vector has coefficients bounded by one. The old four
directions therefore also minimize the new objective. -/
theorem gauss_four_of_hex {U V T i j z v w : ℤ}
    (positive : 0<U) (ordered : U≤V) (reduced : |T|≤U)
    (z0 : 0≤z) (v0 : 0≤v) (cap : v≤w) (face : 2*z+v≤2*w)
    (first : w^2≤U) (norm : U*i^2+T*i*j+V*j^2 = 2*(z^2+v^2)) :
    |i|≤1 ∧ |j|≤1 := by
  have w0 : 0≤w := by omega
  have d0 : 0≤2*z := by omega
  have d1 : 2*z ≤ 2*w-v := by omega
  have d := mul_self_le_mul_self d0 d1
  have pr := mul_nonneg (sub_nonneg.mpr cap) v0
  have pr' := mul_nonneg (sub_nonneg.mpr cap) w0
  apply gauss_four_vectors positive ordered reduced
  nlinarith

end PrimeFactors.HexagonalWeights
