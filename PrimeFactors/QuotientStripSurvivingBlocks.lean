import PrimeFactors.QuotientStripSlopeRestart
import PrimeFactors.QuotientStripForcedLabels
import PrimeFactors.QuotientStripRectangularEnergy

/-!
# Blocks with surviving discriminants before an ascending factor search stops

A large family of different directions is forced on blocks inside the
balanced interval. Count two different blocks for every direction. The
argument also counts different discriminants when identical square tests
are shared across the entire scan.
-/

namespace PrimeFactors.QuotientStripSurvivingBlocks

open Finset QuotientStripScheduleCost QuotientStripSlopePopulation
open QuotientStripForcedLabels QuotientStripWideSlopeGeometry QuotientStripSlopeRestart
open QuotientStripDiscriminantMultiplicity
set_option exponentiation.threshold 4096
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

-- Keep the finite grid symbolic when a full-width side is instantiated.
attribute [local irreducible] directions

/-- Number of scheduled blocks through an inclusive stop, with an arbitrary origin. -/
noncomputable def visits (n origin cutoff : ℕ) :=
  if cutoff<origin then 0 else (cutoff-origin)/width n+1

noncomputable def owner (n origin j : ℕ) :=
  assigned n (roundedSixth n) (startAt n origin j) (stopAt n origin j)

/-- Count only complete blocks ending strictly before the cutoff. A retained
block has a positive-discriminant label in the class of the local pair (1,N). -/
noncomputable def kept (n origin cutoff : ℕ) : Finset ℕ := by
  classical
  exact (range (visits n origin cutoff)).filter fun j =>
    stopAt n origin j≤n.sqrt ∧ stopAt n origin j<cutoff ∧
    ∃ z, Survives n (startAt n origin j) (stopAt n origin j) (owner n origin j) z

structure Window (n origin cutoff : ℕ) : Prop where
  low : 2^2047≤n
  high : n<2^2048
  early : (origin:ℝ)≤17*Real.sqrt n/20
  late : 4*n≤5*cutoff^2

private theorem before_cutoff {n cutoff : ℕ} (late : 4*n≤5*cutoff^2)
    {d : ℕ×ℕ} {t L : ℝ} (G : Band (Real.sqrt n) (roundedSixth n) d.1 d.2 t L)
    (vp : 0<d.2) (steep : 5*d.2<4*d.1) : t<cutoff := by
  have v : (0:ℝ)<d.2 := by exact_mod_cast vp
  have ratio : 5*(d.2:ℝ)<4*d.1 := by exact_mod_cast steep
  have center := G.atCenter
  rw [Real.sq_sqrt (by positivity)] at center
  have cut : 4*(n:ℝ)≤5*(cutoff:ℝ)^2 := by exact_mod_cast late
  have tt : 5*t^2<4*n := by
    by_contra! bad
    nlinarith only [mul_le_mul_of_nonneg_left bad v.le,
      mul_lt_mul_of_pos_right ratio (sq_pos_of_pos G.tp),center]
  by_contra! bad
  nlinarith only [cut,tt,pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) cutoff) bad 2]

private theorem index_mem {n origin cutoff j : ℕ} (wp : 0<width n)
    (ends : stopAt n origin j<cutoff) : j ∈ range (visits n origin cutoff) := by
  have h : origin+j*width n≤stopAt n origin j := by unfold stopAt startAt; omega
  have o : origin≤cutoff := by omega
  have le : j≤(cutoff-origin)/width n := (Nat.le_div_iff_mul_le wp).mpr (by omega)
  simp only [visits,if_neg (not_lt.mpr o),mem_range]
  omega

/-- Two full blocks for each primitive direction, including an actual bounded
integer label from the first of those blocks. -/
theorem two_for_each_fits {n origin cutoff : ℕ} (nlo : 2^2047≤n) (nhi : n<2^2048)
    (stopBound : 4*n≤5*cutoff^2)
    {d : ℕ×ℕ} (hd : d ∈ directions (2^327))
    (fits : ∀ t L : ℝ, Band (Real.sqrt n) (roundedSixth n) d.1 d.2 t L → (origin:ℝ) ≤ t-L) :
    ∃ i ∈ kept n origin cutoff, ∃ j ∈ kept n origin cutoff, i≠j ∧
      owner n origin i=d ∧ owner n origin j=d ∧
      ∃ z, Survives n (startAt n origin i) (stopAt n origin i) d z := by
  classical
  obtain ⟨_,vmin,uc,vc,lo,hi,cop⟩ := QuotientStripSlopePopulation.properties (B:=2^327) (z:=d) hd
  let r := roundedSixth n
  let s := Real.sqrt (n:ℝ)
  have rbig := (QuotientStripTailCost.root_bounds nlo nhi).2.2.1
  change 2^341≤r at rbig
  have rp : 1≤r := by omega
  have wp : 0<width n := by change 0<2*r; omega
  have sl : (2:ℝ)^1023≤s := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast (show (2^1023)^2≤2^2047 by decide +kernel).trans nlo
  have cap : 2^11*d.2≤r := by omega
  obtain ⟨c₁,c₂⟩ := QuotientStripSlopeAlignment.rounded_comparability nlo nhi
  let G := Band.of_scale (s:=s) (r:=(r:ℝ)) (u:=(d.1:ℝ)) (v:=(d.2:ℝ))
    (by exact_mod_cast rp) (by exact_mod_cast vmin) (by exact_mod_cast lo.le)
    (by exact_mod_cast hi) (by exact_mod_cast cap) c₁ c₂
  let t := Real.sqrt ((d.2:ℝ)*s^2/d.1)
  let L := s/(4*d.2*r)
  change Band s r d.1 d.2 t L at G
  have timeBound : t<cutoff := before_cutoff stopBound G (by omega) lo
  obtain ⟨m,k,left,right,domain⟩ := aligned_from G origin (fits t L G)
  let A (j : ℕ) : ℝ := startAt n origin (m+j)
  let B (j : ℕ) : ℝ := stopAt n origin (m+j)
  have length (j : ℕ) : B j-A j=2*r-1 := by
    dsimp only [A,B,stopAt]
    rw [Nat.cast_sub (by omega : 1≤startAt n origin (m+j)+width n)]
    simp [width,r]
    ring
  have consecutive (j : ℕ) : A (j+1)=B j+1 := by
    dsimp only [A,B,stopAt,startAt]
    rw [Nat.cast_sub (by omega : 1≤origin+(m+j)*width n+width n)]
    push_cast
    ring
  have blocks (j : ℕ) (hj : j≤k) : t-L≤A j ∧ B j-A j=2*r-1 ∧ B j≤t :=
    ⟨(domain j hj).1,length j,(domain j hj).2.1⟩
  obtain ⟨z,i,j,res,res',ik,jk,ne,pos,pos',⟨low,high⟩,low',high'⟩ :=
    G.distinct_blocks A B k ((d.1:ℤ)+n*d.2) blocks (fun j _ => consecutive j)
      (by simpa [A] using left) right
  have localRow (j : ℕ) (hj : j≤k) (w : ℤ) (cls : w ≡ (d.1:ℤ)+n*d.2 [ZMOD 24])
      (dp : 0<(w:ℝ)^2-4*d.1*d.2*s^2)
      (bottom : Band.F s d.1 d.2 (B j)-Band.pad s d.2 (A j) (B j)≤w)
      (top : (w:ℝ)≤Band.F s d.1 d.2 (A j)) :
      m+j ∈ kept n origin cutoff ∧ owner n origin (m+j)=d ∧
        Survives n (startAt n origin (m+j)) (stopAt n origin (m+j)) d w := by
    obtain ⟨bl,bw,bh⟩ := blocks j hj
    have use := forced G cop bl bw bh
    have witness := integer_label G sl uc vc bl bw bh cls dp bottom top
    have below : stopAt n origin (m+j)<cutoff := by
      have endReal : (stopAt n origin (m+j):ℝ)<cutoff := bh.trans_lt timeBound
      exact_mod_cast endReal
    have ownerEq : owner n origin (m+j)=d := use
    exact ⟨mem_filter.mpr ⟨index_mem wp below,(domain j hj).2.2,below,by rw [ownerEq]; exact ⟨w,witness⟩⟩,
      ownerEq,witness⟩
  obtain ⟨ki,oi,wi⟩ := localRow i ik z res pos low high
  obtain ⟨kj,oj,_⟩ := localRow j jk (z+24) res' (by push_cast; exact pos') (by push_cast; exact low') (by push_cast; exact high')
  exact ⟨m+i,ki,m+j,kj,by omega,oi,oj,⟨z,wi⟩⟩

theorem two_for_each {n origin cutoff : ℕ} (W : Window n origin cutoff)
    {d : ℕ×ℕ} (hd : d ∈ directions (2^327)) :
    ∃ i ∈ kept n origin cutoff, ∃ j ∈ kept n origin cutoff, i≠j ∧
      owner n origin i=d ∧ owner n origin j=d ∧
      ∃ z, Survives n (startAt n origin i) (stopAt n origin i) d z :=
  two_for_each_fits W.low W.high W.late hd (fun _ _ G => W.early.trans (stationary_fits G))

theorem population {n origin cutoff : ℕ} (W : Window n origin cutoff) :
    2^654 < (kept n origin cutoff).card := by
  have witnesses (d : ℕ×ℕ) (hd : d∈directions (2^327)) := two_for_each (d:=d) W hd
  have count := two_blocks (directions (2^327)) (kept n origin cutoff) (owner n origin)
    (by
      intro d hd
      obtain ⟨i,ki,j,kj,diff,oi,oj,_⟩ := witnesses d hd
      exact ⟨i,ki,j,kj,diff,oi,oj⟩)
  have bound := many_directions
  omega

theorem full_window {n : ℕ} (low : 2^2047≤n) (high : n<2^2048) :
    Window n (first n) n.sqrt := by
  refine ⟨low,high,original_fits low,?_⟩
  have root := (QuotientStripTailCost.root_bounds low high).1
  have large : 9≤n.sqrt := by omega
  have ceiling := Nat.lt_succ_sqrt' n
  nlinarith only [ceiling,Nat.mul_le_mul_right n.sqrt large,large]

/-- More than one in 2^26 blocks of the ordinary full sweep has a retained label. -/
theorem full_share {n : ℕ} (low : 2^2047≤n) (high : n<2^2048) :
    visitsThrough n n.sqrt < 2^26 * (kept n (first n) n.sqrt).card := by
  have count := population (full_window low high)
  have upper := (full_2048 low high).2
  omega

theorem first_window {p q : ℕ} (low : 2^2047≤p*q) (high : p*q<2^2048) (ratio : 4*q≤5*p) :
    Window (p*q) (first (p*q)) p :=
  ⟨low,high,original_fits low,by nlinarith only [Nat.mul_le_mul_left p ratio]⟩

theorem clipped_window {p q D : ℕ} (low : 2^2047≤p*q) (high : p*q<2^2048) (ratio : 4*q≤5*p)
    (cut : 400*(p*q)≤289*(2^1024-4)^2) (partner : 2^1024-1≤D) :
    Window (p*q) (clippedStart (p*q) D) p :=
  ⟨low,high,clipped_fits low cut partner,(first_window low high ratio).late⟩

end PrimeFactors.QuotientStripSurvivingBlocks
