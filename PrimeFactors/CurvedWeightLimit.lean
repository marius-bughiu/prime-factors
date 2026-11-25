import PrimeFactors.AdaptiveWeightLimit
import PrimeFactors.CongruenceInterval
import Mathlib.Data.Real.Sqrt

namespace PrimeFactors.CurvedWeightLimit

set_option exponentiation.threshold 4096

/-- An interval covering the weighted sum over the entire real balanced
factor curve. Both possible orders of the two factors are included. -/
def Covers (N : ℕ) (a b : ℤ) (l u : ℝ) : Prop :=
  ∀ x y : ℝ, 0 < x → 0 < y → x*y = N → x ≤ 2*y → y ≤ 2*x →
    (a:ℝ)*y+(b:ℝ)*x ∈ Set.Icc l u

/-- For all slopes, three points of the curve force a coefficient budget,
even if the factor curve is bounded with its exact extrema. -/
theorem coefficients_from_width {N R k : ℕ} {a b : ℤ} {l u : ℝ} (size : 2^2047 ≤ N)
    (cover : Covers N a b l u) (width : u-l < (k:ℝ)*(R:ℝ)^2) :
    2^1024*a.natAbs ≤ 17*(k*R^2) ∧ 2^1024*b.natAbs ≤ 17*(k*R^2) := by
  let c := Real.sqrt N
  let z := Real.sqrt ((N:ℝ)/8)
  have hN : (0:ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by decide +kernel : 0<(2:ℕ)^2047) size)
  have cp : 0<c := Real.sqrt_pos.mpr hN
  have zp : 0<z := Real.sqrt_pos.mpr (by positivity)
  have cs : c^2 = N := Real.sq_sqrt hN.le
  have zs : z^2 = (N:ℝ)/8 := Real.sq_sqrt (by positivity)
  have large : (2:ℝ)^2047 ≤ N := by exact_mod_cast size
  have zmin : (2:ℝ)^1022 ≤ z := by
    apply le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) zp.le
    rw [← pow_mul, zs]
    linarith only [large, (by norm_num : 8*(2:ℝ)^(1022*2) = 2^2047)]
  have delta : z ≤ 8*(3*z-c) := by
    have small : 8*c ≤ 23*z := by
      apply le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) (by positivity)
      nlinarith only [cs, zs, sq_nonneg z]
    linarith only [small]
  have dm : (2:ℝ)^1019 ≤ 3*z-c := by
    have eq : 8*(2:ℝ)^1019 = 2^1022 := by norm_num
    linarith only [zmin, delta, eq]
  have gm : (2:ℝ)^1023 ≤ 2*z := by
    rw [show (2:ℝ)^1023 = 2*2^1022 by norm_num]; linarith only [zmin]
  obtain ⟨cl,cu⟩ := cover c c cp cp (by nlinarith only [cs]) (by linarith only [cp]) (by linarith only [cp])
  obtain ⟨pl,pu⟩ := cover (2*z) (4*z) (by positivity) (by positivity) (by nlinarith only [zs])
    (by linarith only [zp]) (by linarith only [zp])
  obtain ⟨ml,mu⟩ := cover (4*z) (2*z) (by positivity) (by positivity) (by nlinarith only [zs])
    (by linarith only [zp]) (by linarith only [zp])
  have hmid : |((a:ℝ)+b)*(3*z-c)| ≤ u-l := abs_le.mpr (by constructor <;> linarith only [cl,cu,pl,pu,ml,mu])
  have hgap : |((a:ℝ)-b)*(2*z)| ≤ u-l := abs_le.mpr (by constructor <;> linarith only [pl,pu,ml,mu])
  rw [abs_mul, abs_of_nonneg (by linarith [show (0:ℝ) ≤ 2^1019 by positivity] : 0 ≤ 3*z-c)] at hmid
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*z)] at hgap
  have hm := (mul_le_mul_of_nonneg_left dm (abs_nonneg ((a:ℝ)+b))).trans hmid
  have hg := (mul_le_mul_of_nonneg_left gm (abs_nonneg ((a:ℝ)-b))).trans hgap
  have finish (x : ℤ) (hx : 2*|(x:ℝ)| ≤ |(a:ℝ)+b| + |(a:ℝ)-b|) :
      2^1024*x.natAbs ≤ 17*(k*R^2) := by
    have both : (2:ℝ)^1023 * (|(a:ℝ)+b| + |(a:ℝ)-b|) ≤ 17*(u-l) := by
      linarith only [hm, hg, (by ring : (2:ℝ)^1023 * (|(a:ℝ)+b| + |(a:ℝ)-b|) =
        (|(a:ℝ)+b|)*2^1023 + (|(a:ℝ)-b|)*2^1023)]
    have rr := (mul_le_mul_of_nonneg_left hx (by positivity : (0:ℝ) ≤ 2^1023)).trans both
    have hh : (2:ℝ)^1024*|(x:ℝ)| ≤ 17*((k:ℝ)*(R:ℝ)^2) := by
      rw [show (2:ℝ)^1024=2^1023*2 by norm_num, mul_assoc]
      linarith
    rw [← Int.cast_abs, ← Int.natCast_natAbs] at hh
    exact_mod_cast hh
  constructor
  · apply finish
    simpa [show (a:ℝ)+b+(a-b)=2*a by ring, abs_mul] using abs_add_le ((a:ℝ)+b) (a-b)
  · apply finish
    have e := abs_add_le ((a:ℝ)+b) (-(a-b))
    rw [show (a:ℝ)+b+ -(a-b)=2*b by ring, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2), abs_neg] at e
    exact e

/-- Even with a separately chosen optimum interval on the true balanced
curve for each stationary slope, a single common base must exceed 2^648. -/
theorem radix_lower {N R : ℕ} [NeZero R] (size : 2^2047 ≤ N) (c : (ZMod R)ˣ)
    (cover : ∀ s ∈ AffineSlopeClasses.slopes c, ∃ a b : ℤ, (a≠0 ∨ b≠0) ∧
      a*(s : ZMod R).val ≡ b [ZMOD R] ∧ ∃ l u, Covers N a b l u ∧ u-l < (R:ℝ)^2) :
    2^648 < R := by
  apply AdaptiveWeightLimit.radix_lower_of_curved_weights c
  intro s hs
  obtain ⟨a,b,nz,rel,l,u,curve,width⟩ := cover s hs
  refine ⟨a,b,nz,rel,?_⟩
  simpa using coefficients_from_width (k:=1) size curve (by simpa using width)

/-- The same global curve cannot yield at most one candidate for every slope
at a small radix, even when every slope chooses a favorable residue offset. -/
theorem offset_lower {N R : ℕ} [NeZero R] (size : 2^2047 ≤ N) (c : (ZMod R)ˣ)
    (cover : ∀ s ∈ AffineSlopeClasses.slopes c, ∃ a b r : ℤ, (a≠0 ∨ b≠0) ∧
      a*(s : ZMod R).val ≡ b [ZMOD R] ∧ ∃ l u, Covers N a b l u ∧
      ∀ x y : ℤ, x ≡ r [ZMOD (R:ℤ)^2] → y ≡ r [ZMOD (R:ℤ)^2] →
        (x:ℝ) ∈ Set.Icc l u → (y:ℝ) ∈ Set.Icc l u → x=y) :
    2^647 < R := by
  apply AdaptiveWeightLimit.radix_lower_of_offset_weights c
  intro s hs
  obtain ⟨a,b,r,nz,rel,l,u,curve,one⟩ := cover s hs
  have width := CongruenceInterval.width_of_unique (L:=l) (U:=u) (M:=R^2) r
    (pow_pos (NeZero.pos R) 2) (by push_cast; exact one)
  obtain ⟨ac,bc⟩ := coefficients_from_width (R:=R) (k:=2) size curve (by simpa using width)
  exact ⟨a,b,nz,rel,by linarith only [ac],by linarith only [bc]⟩

end PrimeFactors.CurvedWeightLimit
