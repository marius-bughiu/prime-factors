import PrimeFactors.QuotientStripWideSlopeSeparation

namespace PrimeFactors.QuotientStripWideSlopeGeometry.Band

theorem label_bounds {s r u v t L a b w : ℝ} (G : Band s r u v t L)
    (sl : 2^1023≤s) (uc : u≤9*2^327) (vc : v≤7*2^327)
    (low : t-L≤a) (full : b-a=2*r-1) (high : b≤t)
    (bot : F s u v b-pad s v a b≤w) (top : w≤F s u v a) :
    0≤w ∧ w<s^2 := by
  obtain ⟨_,vp,_,up,sp⟩ := G.basic
  have asmall : s≤2*a := by linarith [G.band_interior.1]
  have alarge : a≤s := by linarith [G.center.2,G.rp]
  have ap : 0<a := by linarith
  have divb : v*s^2/a ≤ 2*v*s := by
    apply (div_le_iff₀ ap).mpr
    nlinarith only [mul_le_mul_of_nonneg_left asmall (mul_nonneg vp.le sp.le)]
  have coeff : u+2*v < s := by linarith only [sl,uc,vc]
  have tot := mul_lt_mul_of_pos_right coeff sp
  have fa : 2≤F s u v a := by
    have a2 : 2≤a := by linarith only [sl,asmall]
    have u1 : 1≤u := by linarith [G.basic.2.2.1,G.vp]
    have q : 0≤v*s^2/a := by positivity
    unfold F
    nlinarith only [mul_le_mul u1 a2 (by norm_num) up.le,q]
  have small := (G.block_width low full high).2
  constructor
  · linarith only [fa,small,bot]
  · unfold F at top
    nlinarith only [top,divb,tot,mul_le_mul_of_nonneg_left alarge up.le]

/-- No extra lower bound on the bit length is needed once the band holds. -/
theorem own_certificate {s r u v t L a b : ℝ} (G : Band s r u v t L)
    (low : t-L≤a) (full : b-a=2*r-1) (high : b≤t) :
    0<v ∧ v≤r-1 ∧ |u-v*(s^2/(a*b))|≤1/r := by
  obtain ⟨rp,vp,_,_,_⟩ := G.basic
  obtain ⟨err,mag⟩ := G.chord_slope low (by linarith [G.rp]) high
  have one : 7/(8*r) ≤ 1/r := by
    apply (div_le_div_iff₀ (by positivity) rp).mpr
    linarith
  refine ⟨vp,by linarith [G.cap,G.vp],?_⟩
  rw [← mul_div_assoc,abs_of_nonpos (by linarith only [err])]
  linarith only [mag,one]

/-- Integer form of the public chord certificate with Q+1=r. -/
theorem own_cross_certificate {s r u v t L a b : ℝ} (G : Band s r u v t L)
    (low : t-L≤a) (full : b-a=2*r-1) (high : b≤t) :
    |u*(a*b)-v*s^2| * r ≤ a*b := by
  obtain ⟨rp,_,_,_,_⟩ := G.basic
  have ab : a≤b := by linarith [G.rp]
  have ap := (G.slope_at low (ab.trans high)).1
  have bp := ap.trans_le ab
  have certified := (G.own_certificate low full high).2.2
  have fit := (le_div_iff₀ rp).mp certified
  have eq : |u*(a*b)-v*s^2| = |u-v*(s^2/(a*b))| * (a*b) := by
    rw [← abs_of_pos (mul_pos ap bp), ← abs_mul, abs_of_pos (mul_pos ap bp)]
    congr 1
    field_simp
  nlinarith only [eq,mul_le_mul_of_nonneg_right fit (mul_nonneg ap.le bp.le),
    congrArg (fun z : ℝ => z*r) eq]

end PrimeFactors.QuotientStripWideSlopeGeometry.Band

namespace PrimeFactors.QuotientStripWideSlopeGeometry.Rounded
open Band

def den (a b : ℤ) := 4*a^2*b
def leftNum (N a b u v : ℤ) := 4*a*b*(u*a^2+v*N)
def rightNum (N a b u v : ℤ) := 4*a^2*(u*b^2+v*N)
def labelLow (N a b u v : ℤ) :=
  -((-(min (leftNum N a b u v) (rightNum N a b u v) - v*N*(b-a)^2))/den a b)
def labelHigh (N a b u v : ℤ) :=
  (max (leftNum N a b u v) (rightNum N a b u v))/den a b

theorem endpoints_iff {s : ℝ} {N a b u v z : ℤ} (sqN : s^2=N) (ap : 0<a) (bp : 0<b) :
    labelLow N a b u v ≤ z ∧ z ≤ labelHigh N a b u v ↔
      min (F s u v a) (F s u v b)-pad s v a b ≤ z ∧
        (z:ℝ) ≤ max (F s u v a) (F s u v b) := by
  have D : 0<den a b := by unfold den; positivity
  have RD : 0<(den a b:ℝ) := by exact_mod_cast D
  have ar : (a:ℝ)≠0 := by exact_mod_cast ap.ne'
  have br : (b:ℝ)≠0 := by exact_mod_cast bp.ne'
  have left : (leftNum N a b u v:ℝ)=F s u v a*(den a b:ℝ) := by
    unfold leftNum den F; rw [sqN]; push_cast; field_simp; ring
  have right : (rightNum N a b u v:ℝ)=F s u v b*(den a b:ℝ) := by
    unfold rightNum den F; rw [sqN]; push_cast; field_simp; ring
  have bottom : ((v*N*(b-a)^2:ℤ):ℝ)=pad s v a b*(den a b:ℝ) := by
    unfold pad den; rw [sqN]; push_cast; field_simp
  have L : -((-(min (leftNum N a b u v) (rightNum N a b u v)-v*N*(b-a)^2))/den a b)≤z ↔
      min (leftNum N a b u v) (rightNum N a b u v)-v*N*(b-a)^2 ≤ z*den a b := by
    rw [show -((-(min (leftNum N a b u v) (rightNum N a b u v)-v*N*(b-a)^2))/den a b)≤z ↔
      -z≤(-(min (leftNum N a b u v) (rightNum N a b u v)-v*N*(b-a)^2))/den a b by omega,
      Int.le_ediv_iff_mul_le D,neg_mul,neg_le_neg_iff]
  unfold labelLow labelHigh
  rw [L,Int.le_ediv_iff_mul_le D]
  have bridge : (min (leftNum N a b u v) (rightNum N a b u v)-v*N*(b-a)^2 ≤ z*den a b ∧
      z*den a b ≤ max (leftNum N a b u v) (rightNum N a b u v)) ↔
      min (leftNum N a b u v:ℝ) (rightNum N a b u v)-((v*N*(b-a)^2:ℤ):ℝ) ≤ (z:ℝ)*(den a b:ℝ) ∧
      (z:ℝ)*(den a b:ℝ) ≤ max (leftNum N a b u v:ℝ) (rightNum N a b u v) := by exact_mod_cast Iff.rfl
  rw [bridge,left,right,bottom,← min_mul_of_nonneg _ _ RD.le,← max_mul_of_nonneg _ _ RD.le,
    ← sub_mul]
  constructor
  · intro h
    exact ⟨le_of_mul_le_mul_right h.1 RD,le_of_mul_le_mul_right h.2 RD⟩
  · intro h
    exact ⟨mul_le_mul_of_nonneg_right h.1 RD.le,mul_le_mul_of_nonneg_right h.2 RD.le⟩

end PrimeFactors.QuotientStripWideSlopeGeometry.Rounded
