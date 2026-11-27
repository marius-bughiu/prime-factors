import PrimeFactors.HighWordSumRankingBounds
import Mathlib.Algebra.Order.Floor.Ring

/-! A row a full midpoint period later loses enough width to fit every
surviving half-gap into the earlier row by a period-preserving shift. -/

namespace PrimeFactors.HighWordSuffixTransfer

/-- Width of the real interval of half-gaps with squared values in [d,d+w]. -/
noncomputable def width (w d : ℝ) : ℝ := Real.sqrt (d+w)-Real.sqrt d

/-- The first representative of a midpoint residue loses at least one
period of possible half-gaps after a squared shift BP. -/
theorem drop {B P w x : ℝ} (p1 : 1≤P) (big : 4096*P^3≤B) (low : B/2≤w) (high : w≤B)
    (xn : 0≤x) (close : x≤2*(B*P)) :
    width w (x+B*P)+P ≤ width w x := by
  have pp : 0<P := by linarith
  have bp : 0<B := lt_of_lt_of_le (by positivity) big
  have wp : 0<w := by linarith
  let s := Real.sqrt (B*P)
  have sp : 0<s := Real.sqrt_pos.mpr (mul_pos bp pp)
  have ss : s^2=B*P := Real.sq_sqrt (mul_nonneg bp.le pp.le)
  have bq : B≤B*P := by nlinarith only [mul_le_mul_of_nonneg_left p1 bp.le]
  have cap : Real.sqrt (x+B*P+w)≤2*s := Real.sqrt_le_iff.mpr
    ⟨by positivity,by nlinarith only [ss,high,bq,close]⟩
  have aa := Real.sq_sqrt xn
  have bb := Real.sq_sqrt (by linarith : 0≤x+w)
  have cc := Real.sq_sqrt (by nlinarith [mul_pos bp pp] : 0≤x+B*P)
  have dd := Real.sq_sqrt (by nlinarith [mul_pos bp pp] : 0≤x+B*P+w)
  have h := HighWordSumRankingBounds.width_product_drop sp wp (Real.sqrt_nonneg x) (Real.sqrt_lt_sqrt xn (by linarith : x<x+w))
    (Real.sqrt_le_sqrt (by nlinarith [mul_pos bp pp] : x≤x+B*P))
    (Real.sqrt_le_sqrt (by nlinarith [mul_pos bp pp] : x+w≤x+B*P+w))
    (Real.sqrt_le_sqrt (by linarith : x+B*P≤x+B*P+w)) cap
    (by linarith only [aa,bb]) (by linarith only [cc,dd])
    (by linarith only [aa,cc,ss]) (by linarith only [bb,dd,ss])
  have bound : 64*s*P≤B := by
    have hh := mul_le_mul_of_nonneg_right big bp.le
    have sq : (64*s*P)^2≤B^2 := calc
      _ = (s^2)*(4096*P^2) := by ring
      _ = (B*P)*(4096*P^2) := by rw [ss]
      _ ≤ B^2 := by nlinarith only [hh]
    nlinarith only [sq,sp,pp,bp,mul_pos sp pp]
  dsimp [width]
  apply le_of_mul_le_mul_left (a:=64*s) _ (by positivity)
  nlinarith only [h,low,bound]

/-- The same separation bound applies to all subsequent rows in this
midpoint residue class once the squared endpoint has increased by BP. -/
theorem later {B P w x y : ℝ} (p1 : 1≤P) (big : 4096*P^3≤B) (low : B/2≤w)
    (high : w≤B) (xn : 0≤x) (close : x≤2*(B*P)) (shift : x+B*P≤y) :
    width w y+P ≤ width w x := by
  have pp : 0<P := by linarith
  have bp : 0<B := lt_of_lt_of_le (by positivity) big
  have decrease := HighWordSumRankingBounds.width_antitone (w:=w) (show 0≤x+B*P by positivity) shift (by linarith)
  exact (add_le_add_right decrease P).trans (drop p1 big low high xn close)

/-- Round the distance between left endpoints down to a multiple of P. The same
translation fits every integer point regardless of its residue class. -/
theorem shift {P : ℕ} {l₀ h₀ l₁ h₁ : ℝ} (pp : 0<P) (nonneg : 0≤l₀)
    (order : l₀≤l₁) (width : h₁-l₁+(P:ℝ)≤h₀-l₀) :
    ∃ D : ℕ, P∣D ∧ ∀ v : ℕ, l₁≤(v:ℝ) → (v:ℝ)≤h₁ →
      D≤v ∧ l₀≤((v-D:ℕ):ℝ) ∧ ((v-D:ℕ):ℝ)≤h₀ := by
  let a := (l₁-l₀)/(P:ℝ)
  let j := ⌊a⌋₊
  have pr : 0<(P:ℝ) := by exact_mod_cast pp
  have an : 0≤a := div_nonneg (sub_nonneg.mpr order) pr.le
  have bot : (j:ℝ)*(P:ℝ)≤l₁-l₀ := (le_div_iff₀ pr).mp (Nat.floor_le an)
  have top : l₁-l₀<((j:ℝ)+1)*(P:ℝ) := (div_lt_iff₀ pr).mp (Nat.lt_floor_add_one a)
  refine ⟨j*P,dvd_mul_left ..,?_⟩
  intro v vl vh
  have z : (j:ℝ)*P≤v := by linarith
  have bound : j*P≤v := by exact_mod_cast z
  refine ⟨bound,?_,?_⟩ <;> rw [Nat.cast_sub bound,Nat.cast_mul] <;> linarith

/-- A multiple of P can be subtracted without changing the gap residue. -/
theorem sub_mod {D P v : ℕ} (d : P∣D) (within : D≤v) : v-D ≡ v [MOD P] := by
  have same := (Nat.modEq_zero_iff_dvd.mpr d).add_left (v-D)
  simpa only [Nat.sub_add_cancel within,Nat.add_zero] using same.symm

end PrimeFactors.HighWordSuffixTransfer
