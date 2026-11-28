import PrimeFactors.QuarticFermatDistance
import PrimeFactors.ComplementaryQuarticPopulation

/-! The inclusive Fermat midpoint rank of the displayed Sophie Germain pair
on the strip below the next fourth power of the second coordinate. -/
namespace PrimeFactors.QuarticMidpointRank

open RecognizingQuarticProducts (factors)
open QuarticFermatDistance (rank midpoint_hit)

private theorem starts {x y : ℕ} (xp : 0<x) :
    2*y^2<ceilSqrt (x^4+4*y^4) ∧ ceilSqrt (x^4+4*y^4)≤x^2+2*y^2 := by
  constructor
  · apply lt_of_not_ge
    intro h
    have := ceilSqrt_le_iff.mp h
    nlinarith only [this,pow_pos xp 4]
  · apply ceilSqrt_le_iff.mpr
    nlinarith only [midpoint_hit x y,Nat.zero_le ((2*x*y)^2)]

/-- When the starting midpoint is exactly one above 2y², the rank is x².
The threshold x²≤2y is necessary and sufficient. -/
theorem rank_eq_square_iff {x y : ℕ} (xp : 0<x) (yp : 0<y) :
    rank x y=x^2 ↔ x^2≤2*y := by
  obtain ⟨low,high⟩ := starts (y:=y) xp
  have eq : rank x y=x^2 ↔ ceilSqrt (x^4+4*y^4)≤2*y^2+1 := by unfold rank; omega
  rw [eq,ceilSqrt_le_iff]
  constructor
  · intro h
    by_contra! big
    have sq := Nat.pow_le_pow_left (show 2*y+1≤x^2 from big) 2
    nlinarith only [h,sq,yp]
  · intro h
    nlinarith only [Nat.pow_le_pow_left h 2]

/-- A threshold for the displayed rank that uses integer arithmetic alone. -/
theorem rank_ge_iff {x y k : ℕ} (xp : 0<x) (fit : k≤x^2+2*y^2) :
    k+1≤rank x y ↔ 2*k*(x^2+2*y^2)≤(2*x*y)^2+k^2 := by
  have high := (starts (y:=y) xp).2
  have eq : k+1≤rank x y ↔ ceilSqrt (x^4+4*y^4)≤x^2+2*y^2-k := by unfold rank; omega
  rw [eq,ceilSqrt_le_iff]
  have difference : (x^2+2*y^2-k)^2+2*k*(x^2+2*y^2)=(x^2+2*y^2)^2+k^2 := by
    zify [fit]
    ring
  have square := midpoint_hit x y
  omega

/-- Only the first positive x-coordinate puts the displayed factor pair on
the initial midpoint, even without a strip or primality assumption. -/
theorem first_iff {x y : ℕ} (xp : 0<x) (yp : 0<y) : rank x y=1 ↔ x=1 := by
  constructor
  · intro first
    by_contra other
    obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le (show 2≤x by omega)
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (show 1≤y from yp)
    have later := (rank_ge_iff (x:=2+i) (y:=1+j) (k:=1) (by omega)
      (by ring_nf; omega)).mpr (by ring_nf; omega)
    omega
  · rintro rfl
    exact (rank_eq_square_iff (by decide : 0<1) yp).mpr (by omega)

/-- From x=3 and y=5 onward the displayed pair takes at least nine ordinary
midpoint tests, including the first test. -/
theorem nine_le {x y : ℕ} (hx : 3≤x) (hy : 5≤y) : 9≤rank x y := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le hx
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hy
  apply (rank_ge_iff (x:=3+i) (y:=5+j) (k:=8) (by omega) (by ring_nf; omega)).mpr
  ring_nf
  omega

/-- On the balanced y-first strip the threshold of nine tests already applies
to every x≥3. For prime outputs, QuarticFermatDistance.first excludes an
earlier square difference. -/
theorem balanced_nine {x y : ℕ} (hx : 3≤x) (yp : 0<y)
    (strip : x^4+4*y^4<4*(y+1)^4) (bal : (factors x y).2≤2*(factors x y).1) :
    9≤rank x y := by
  apply nine_le hx
  by_contra! small
  have xc : x<8 := by
    apply (Nat.pow_lt_pow_iff_left (by decide : 4≠0)).mp
    calc
      x^4 ≤ x^4+4*y^4 := Nat.le_add_right _ _
      _ < 4*(y+1)^4 := strip
      _ ≤ 4*5^4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left small 4)
      _ < _ := by decide
  have empty : ∀ u : Fin 8, ∀ v : Fin 5, 3≤u.val → 0<v.val →
      u.val^4+4*v.val^4<4*(v.val+1)^4 → (factors u.val v.val).2≤2*(factors u.val v.val).1 → False := by
    decide +kernel
  exact empty ⟨x,xc⟩ ⟨y,small⟩ hx yp strip bal

/-- The two fourth-power endpoints also bound the correction to x². -/
theorem strip_bounds {x y : ℕ} (xp : 0<x) (strip : x^4+4*y^4<4*(y+1)^4) :
    rank x y≤x^2 ∧ x^2≤rank x y+(4*y+1) := by
  obtain ⟨low,high⟩ := starts (y:=y) xp
  have upper : ceilSqrt (x^4+4*y^4)≤2*(y+1)^2 := ceilSqrt_le_iff.mpr (by nlinarith only [strip])
  unfold rank
  rw [show 2*(y+1)^2=2*y^2+4*y+2 by ring] at upper
  omega

set_option exponentiation.threshold 4096 in
/-- For full-width y-first representations, x through 2²⁵⁶ still has rank
exactly x². The additive bound and absolute upper bound hold across the strip. -/
theorem full_width {x y : ℕ} (xp : 0<x)
    (large : 2^2047≤x^4+4*y^4) (small : x^4+4*y^4<2^2048)
    (strip : x^4+4*y^4<4*(y+1)^4) :
    (x≤2^256 → rank x y=x^2) ∧ x^2-rank x y<2^514 ∧ rank x y<2^770 := by
  obtain ⟨yl,yu,xu⟩ := ComplementaryQuarticPopulation.parameters large small rfl strip
  obtain ⟨up,lo⟩ := strip_bounds xp strip
  have ylo : 0<19*(2:ℕ)^507 := by positivity
  constructor
  · intro h
    apply (rank_eq_square_iff xp (ylo.trans_le yl)).mpr
    exact (Nat.pow_le_pow_left h 2).trans ((by decide +kernel : ((2:ℕ)^256)^2≤2*(19*2^507)).trans
      (Nat.mul_le_mul_left 2 yl))
  · have err : 4*(23*(2:ℕ)^507)+1<2^514 := by decide +kernel
    have edge : (25*(2:ℕ)^380)^2<2^770 := by decide +kernel
    exact ⟨by omega,up.trans_lt ((Nat.pow_le_pow_left xu.le 2).trans_lt edge)⟩

/-- The first larger odd x attains the nine-test lower bound with balanced
prime factors. The second product falls just outside the exact x² regime. -/
theorem examples :
    factors 3 10=(149,269) ∧ Nat.Prime 149 ∧ Nat.Prime 269 ∧
    3^4+4*10^4<4*(10+1)^4 ∧ rank 3 10=9 ∧
    factors 7 20=(569,1129) ∧ Nat.Prime 569 ∧ Nat.Prime 1129 ∧
    7^4+4*20^4<4*(20+1)^4 ∧ rank 7 20=48 := by
  have r3 : rank 3 10=9 := (rank_eq_square_iff (by decide : 0<3) (by decide : 0<10)).mpr (by decide)
  have c : ceilSqrt (7^4+4*20^4)=802 := by
    have top := ceilSqrt_le_iff.mpr (by decide +kernel : 7^4+4*20^4≤802^2)
    have bot : ¬ceilSqrt (7^4+4*20^4)≤801 := fun h => (by decide +kernel : ¬7^4+4*20^4≤801^2)
      (ceilSqrt_le_iff.mp h)
    omega
  refine ⟨by decide,by norm_num,by norm_num,by decide,r3,by decide,by norm_num,by norm_num,by decide,?_⟩
  rw [rank,c]
  decide

/-- A 24-bit product with two 12-bit primes has its first square difference
on the ninth ordinary midpoint test. -/
theorem classroom :
    (10240081:ℕ)=2969*3449 ∧ factors 3 40=(2969,3449) ∧
    Nat.Prime 2969 ∧ Nat.Prime 3449 ∧ (2:ℕ)^11≤2969 ∧ (3449:ℕ)<2^12 ∧
    (2:ℕ)^23≤10240081 ∧ (10240081:ℕ)<2^24 ∧ (10240081:ℕ)<4*(40+1)^4 ∧
    ceilSqrt 10240081=3201 ∧ (3209:ℕ)^2=10240081+240^2 ∧
    ∀ i<8, ¬IsSquare ((3201+i)^2-(10240081:ℕ)) := by
  have shape : factors 3 40=(2969,3449) := by decide
  have pp : Nat.Prime 2969 := by norm_num
  have qp : Nat.Prime 3449 := by norm_num
  have upper := ceilSqrt_le_iff.mpr (by decide +kernel : (10240081:ℕ)≤3201^2)
  have lower : ¬ceilSqrt 10240081≤3200 := fun h => (by decide +kernel : ¬(10240081:ℕ)≤3200^2)
    (ceilSqrt_le_iff.mp h)
  have c : ceilSqrt 10240081=3201 := by omega
  refine ⟨by decide,shape,pp,qp,by decide,by decide,by decide,by decide,by decide,c,by decide,?_⟩
  intro i hi
  apply QuarticFermatDistance.first (x:=3) (y:=40) (shape ▸ pp) (shape ▸ qp)
  · change ceilSqrt 10240081≤3201+i
    omega
  · change 3201+i<3209
    omega

end PrimeFactors.QuarticMidpointRank
