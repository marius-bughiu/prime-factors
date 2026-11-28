import PrimeFactors.QuotientStripWideSlopeSurvivors

namespace PrimeFactors.QuotientStripWideSlopeGeometry.Band

/-- The retained intervals are ordered exactly as presumed by the branch-free
description, and are narrower than two units throughout this neighborhood. -/
theorem block_width {s r u v t L a b : ℝ} (G : Band s r u v t L)
    (low : t-L≤a) (full : b-a=2*r-1) (high : b≤t) :
    F s u v b ≤ F s u v a ∧ F s u v a-(F s u v b-pad s v a b)<2 := by
  obtain ⟨rp,vp,_,up,sp⟩ := G.basic
  have dp : 0<b-a := by linarith [G.rp]
  have ab : a≤b := by linarith
  have ap := (G.slope_at low (ab.trans high)).1
  have bp := ap.trans_le ab
  have sl := G.chord_slope low ab high
  have id : F s u v a-F s u v b=(b-a)*(v*s^2/(a*b)-u) := by
    unfold F
    field_simp
    ring
  have rise : F s u v a-F s u v b < 7/4 := by
    rw [id]
    calc
      _ < (b-a)*(7/(8*r)) := mul_lt_mul_of_pos_left sl.2 dp
      _ ≤ (2*r)*(7/(8*r)) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by field_simp; ring
  have al : s ≤ 2*a := by linarith [G.band_interior.1]
  have bl : s ≤ 2*b := by linarith
  have d2 := pow_le_pow_left₀ dp.le (by linarith only [full] : b-a≤2*r) 2
  have bprod := mul_le_mul (pow_le_pow_left₀ sp.le al 2) bl sp.le (sq_nonneg (2*a))
  have ds := mul_le_mul_of_nonneg_left d2 vp.le
  have cap := mul_le_mul_of_nonneg_right G.cap (sq_nonneg r)
  have small : 8*v*(b-a)^2 ≤ s := by
    norm_num1 at cap
    nlinarith only [ds,cap,G.rootLo,mul_nonneg vp.le (sq_nonneg r)]
  have scale := mul_le_mul_of_nonneg_left small (sq_nonneg s)
  have depth : pad s v a b ≤ 1/4 := by
    unfold pad
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [scale,bprod]
  constructor
  · linarith only [id,mul_nonneg dp.le sl.1]
  · linarith only [rise,depth]

/-- The two positive-discriminant labels occur on different supplied blocks,
even before the rest of the public search is taken into account. -/
theorem distinct_blocks {s r u v t L : ℝ} (G : Band s r u v t L)
    (A B : ℕ→ℝ) (k : ℕ) (c : ℤ)
    (blocks : ∀i≤k, t-L≤A i ∧ B i-A i=2*r-1 ∧ B i≤t)
    (next : ∀i<k, A (i+1)=B i+1)
    (first : A 0≤t-L+2*r) (last : t-4*r≤B k) :
    ∃ (z : ℤ) (i j : ℕ), z ≡ c [ZMOD 24] ∧ (z+24) ≡ c [ZMOD 24] ∧
      i≤k ∧ j≤k ∧ i≠j ∧ 0<(z:ℝ)^2-4*u*v*s^2 ∧ 0<((z:ℝ)+24)^2-4*u*v*s^2 ∧
      (F s u v (B i)-pad s v (A i) (B i)≤z ∧ (z:ℝ)≤F s u v (A i)) ∧
      F s u v (B j)-pad s v (A j) (B j)≤(z:ℝ)+24 ∧ (z:ℝ)+24≤F s u v (A j) := by
  obtain ⟨z,res,hz⟩ := G.band_survivors A B k c blocks next first last
  obtain ⟨dp,i,ik,zl,zu⟩ := hz z (by simp)
  obtain ⟨dp',j,jk,zl',zu'⟩ := hz (z+24) (by simp)
  push_cast at dp' zl' zu'
  have different : i≠j := by
    rintro rfl
    obtain ⟨h1,h2,h3⟩ := blocks i ik
    linarith only [(G.block_width h1 h2 h3).2,zl,zu']
  refine ⟨z,i,j,res,?_,ik,jk,different,dp,dp',⟨zl,zu⟩,zl',zu'⟩
  exact (show z+24 ≡ z [ZMOD 24] by rw [Int.modEq_iff_dvd]; exact ⟨-1,by ring⟩).trans res

end PrimeFactors.QuotientStripWideSlopeGeometry.Band
