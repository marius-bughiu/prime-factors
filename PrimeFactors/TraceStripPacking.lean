import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace PrimeFactors.TraceStripPacking

/-- The oriented weighted trace on a product hyperbola. -/
noncomputable def trace (A B X d : ℝ) : ℝ := A*d + B*X^2/d

private theorem coeff {B X i j k : ℝ} (bp : 0 ≤ B) (ip : 0 < i) (jp : 0 < j) (kp : 0 < k)
    (il : i≤X) (jl : j≤X) (kl : k≤X) : B/X ≤ B*X^2/(i*j*k) := by
  have xp := ip.trans_le il
  apply (div_le_div_iff₀ xp (mul_pos (mul_pos ip jp) kp)).mpr
  calc
    B*(i*j*k) ≤ B*(X*X*X) := by gcongr
    _ = B*X^2*X := by ring

private theorem difference {A B X x y : ℝ} (xp : 0<x) (yp : 0<y) :
    trace A B X y - trace A B X x = (y-x)*(A-B*X^2/(x*y)) := by
  unfold trace
  field_simp
  ring

/-- Secant lower bound on an increasing branch, anchored anywhere before the two endpoints. -/
theorem increasing_secant {A B X z x y : ℝ} (bp : 0≤B) (zp : 0<z)
    (zx : z≤x) (xy : x≤y) (yu : y≤X) (inc : B*X^2≤A*z^2) :
    B*(y-x)*(x+y-2*z) ≤ X*(trace A B X y-trace A B X x) := by
  have xu := xy.trans yu
  have zu := zx.trans xu
  have xp := zp.trans_le zx
  have yp := xp.trans_le xy
  have h1 := mul_le_mul_of_nonneg_right (coeff bp zp zp xp zu zu xu) (sub_nonneg.mpr zx)
  have h2 := mul_le_mul_of_nonneg_right (coeff bp zp xp yp zu xu yu) (sub_nonneg.mpr (zx.trans xy))
  have ha : B*X^2/z^2≤A := (div_le_iff₀ (sq_pos_of_pos zp)).mpr inc
  have ident : B*X^2/(z*z*x)*(x-z) + B*X^2/(z*x*y)*(y-z) =
      B*X^2/z^2-B*X^2/(x*y) := by field_simp; ring
  have slope : B/X*(x+y-2*z) ≤ A-B*X^2/(x*y) := by linarith only [h1,h2,ident,ha]
  rw [difference xp yp]
  have scaled := mul_le_mul_of_nonneg_left slope (sub_nonneg.mpr xy)
  have up := zp.trans_le zu
  have := mul_le_mul_of_nonneg_left scaled up.le
  convert this using 1
  field_simp
  ring

/-- The corresponding decreasing branch bound, anchored after the two endpoints. -/
theorem decreasing_secant {A B X z x y : ℝ} (bp : 0≤B) (xp : 0<x)
    (xy : x≤y) (yz : y≤z) (zu : z≤X) (dec : A*z^2≤B*X^2) :
    B*(y-x)*(2*z-x-y) ≤ X*(trace A B X x-trace A B X y) := by
  have yp := xp.trans_le xy
  have zp := yp.trans_le yz
  have yu := yz.trans zu
  have xu := xy.trans yu
  have h1 := mul_le_mul_of_nonneg_right (coeff bp xp yp zp xu yu zu) (sub_nonneg.mpr (xy.trans yz))
  have h2 := mul_le_mul_of_nonneg_right (coeff bp yp zp zp yu zu zu) (sub_nonneg.mpr yz)
  have ha : A≤B*X^2/z^2 := (le_div_iff₀ (sq_pos_of_pos zp)).mpr dec
  have ident : B*X^2/(x*y*z)*(z-x) + B*X^2/(y*z*z)*(z-y) =
      B*X^2/(x*y)-B*X^2/z^2 := by field_simp; ring
  have slope : B/X*(2*z-x-y) ≤ B*X^2/(x*y)-A := by linarith only [h1,h2,ident,ha]
  have id := difference (A:=A) (B:=B) (X:=X) xp yp
  have scaled := mul_le_mul_of_nonneg_left slope (sub_nonneg.mpr xy)
  have up := zp.trans_le zu
  have hs := mul_le_mul_of_nonneg_left scaled up.le
  have swap : trace A B X x-trace A B X y = (y-x)*(B*X^2/(x*y)-A) := by linarith only [id]
  rw [swap]
  convert hs using 1
  field_simp
  ring

/-- Ordered intervals of distances moving away from an anchor. Their interiors are disjoint. -/
def OrderedFrom (t : ℝ) : List (ℝ × ℝ) → Prop
  | [] => True
  | (a,b)::tail => t≤a ∧ a≤b ∧ OrderedFrom b tail

/-- Sum of the interval lengths. -/
noncomputable def totalLength (windows : List (ℝ × ℝ)) : ℝ :=
  (windows.map (fun I => I.2-I.1)).sum

/-- Sum of changes of a function on the intervals in the list. -/
noncomputable def totalSpan (f : ℝ → ℝ) (windows : List (ℝ × ℝ)) : ℝ :=
  (windows.map (fun I => f I.2-f I.1)).sum

private theorem length_nonneg {windows : List (ℝ × ℝ)} {t : ℝ} (ord : OrderedFrom t windows) :
    0 ≤ totalLength windows := by
  induction windows generalizing t with
  | nil => simp [totalLength]
  | cons ab tail ih =>
    rcases ab with ⟨a,b⟩
    obtain ⟨_, le, next⟩ := ord
    simpa [totalLength] using add_nonneg (sub_nonneg.mpr le) (ih next)

private theorem accumulated {windows : List (ℝ × ℝ)} {B X t : ℝ} {f : ℝ → ℝ}
    (bp : 0≤B) (ord : OrderedFrom t windows)
    (sec : ∀ I ∈ windows, B*(I.2-I.1)*(I.1+I.2) ≤ X*(f I.2-f I.1)) :
    B*(totalLength windows ^ 2+2*t*totalLength windows) ≤ X*totalSpan f windows := by
  induction windows generalizing t with
  | nil => simp [totalLength,totalSpan]
  | cons ab tail ih =>
    rcases ab with ⟨a,b⟩
    obtain ⟨ta,ab,next⟩ := ord
    have step := sec (a,b) (by simp)
    change B*(b-a)*(a+b) ≤ X*(f b-f a) at step
    have rest := ih next (fun I hi => sec I (by simp [hi]))
    have slack := mul_nonneg (mul_nonneg (by positivity : 0≤2*B) (sub_nonneg.mpr ta))
        (add_nonneg (sub_nonneg.mpr ab) (length_nonneg next))
    change B*((b-a+totalLength tail)^2+2*t*(b-a+totalLength tail)) ≤
        X*(f b-f a+totalSpan f tail)
    nlinarith only [step,rest,slack]

/-- Packing on the increasing branch. The actual intervals are [z+l,z+r]
for the recorded pairs (l,r). Unused gaps between intervals are allowed. -/
theorem increasing_packing {A B X z : ℝ} {windows : List (ℝ × ℝ)} (bp : 0≤B)
    (zp : 0<z) (inc : B*X^2≤A*z^2) (ord : OrderedFrom 0 windows)
    (domain : ∀ I ∈ windows, 0≤I.1 ∧ I.1≤I.2 ∧ z+I.2≤X) :
    B*totalLength windows^2 ≤ X*totalSpan (fun t => trace A B X (z+t)) windows := by
  apply le_trans (b:=B*(totalLength windows^2+2*0*totalLength windows)) (by simp)
  apply accumulated bp ord
  intro I hi
  obtain ⟨h1,h2,h3⟩ := domain I hi
  convert increasing_secant bp zp (show z≤z+I.1 by linarith)
    (show z+I.1≤z+I.2 by linarith) h3 inc using 1
  ring

/-- Packing on the decreasing branch. The actual intervals are [z-r,z-l].
The list runs leftwards, away from the anchor, so the trace increases. -/
theorem decreasing_packing {A B X z : ℝ} {windows : List (ℝ × ℝ)} (bp : 0≤B)
    (zu : z≤X) (dec : A*z^2≤B*X^2) (ord : OrderedFrom 0 windows)
    (domain : ∀ I ∈ windows, 0≤I.1 ∧ I.1≤I.2 ∧ 0<z-I.2) :
    B*totalLength windows^2 ≤ X*totalSpan (fun t => trace A B X (z-t)) windows := by
  apply le_trans (b:=B*(totalLength windows^2+2*0*totalLength windows)) (by simp)
  apply accumulated bp ord
  intro I hi
  obtain ⟨h1,h2,h3⟩ := domain I hi
  convert decreasing_secant bp h3 (show z-I.2 ≤ z-I.1 by linarith)
    (show z-I.1≤z by linarith) zu dec using 1
  ring


private theorem span_le_count {windows : List (ℝ × ℝ)} {f : ℝ → ℝ}
    (narrow : ∀ I ∈ windows, f I.2-f I.1 ≤ 4) :
    totalSpan f windows ≤ 4*(windows.length : ℝ) := by
  induction windows with
  | nil => simp [totalSpan]
  | cons I tail ih =>
    have first := narrow I (by simp)
    have rest := ih (fun I hi => narrow I (by simp [hi]))
    simpa [totalSpan,add_mul,mul_add,add_comm] using add_le_add first rest

/-- Both monotone branches together, for m arbitrarily placed parity traces.
Each branch is represented by disjoint covered intervals, at most one per
trace, with trace variation at most four on each. The anchors may differ. -/
theorem four_width_packing {A B X zi zd : ℝ} {incWindows decWindows : List (ℝ × ℝ)}
    (m : ℕ) (bp : 0≤B) (zip : 0<zi) (zdu : zd≤X) (xp : 0≤X)
    (inc : B*X^2≤A*zi^2) (dec : A*zd^2≤B*X^2)
    (oi : OrderedFrom 0 incWindows) (od : OrderedFrom 0 decWindows)
    (di : ∀ I ∈ incWindows, 0≤I.1 ∧ I.1≤I.2 ∧ zi+I.2≤X)
    (dd : ∀ I ∈ decWindows, 0≤I.1 ∧ I.1≤I.2 ∧ 0<zd-I.2)
    (si : ∀ I ∈ incWindows, trace A B X (zi+I.2)-trace A B X (zi+I.1) ≤ 4)
    (sd : ∀ I ∈ decWindows, trace A B X (zd-I.2)-trace A B X (zd-I.1) ≤ 4)
    (ci : incWindows.length ≤ m) (cd : decWindows.length ≤ m) :
    B*(totalLength incWindows + totalLength decWindows)^2 ≤ 16*X*m := by
  have hi := increasing_packing bp zip inc oi di
  have hd := decreasing_packing bp zdu dec od dd
  have wi := span_le_count (f:=fun t => trace A B X (zi+t)) si
  have wd := span_le_count (f:=fun t => trace A B X (zd-t)) sd
  have ni : (incWindows.length : ℝ) ≤ m := by exact_mod_cast ci
  have nd : (decWindows.length : ℝ) ≤ m := by exact_mod_cast cd
  have hi' := hi.trans (mul_le_mul_of_nonneg_left
    (wi.trans (mul_le_mul_of_nonneg_left ni (by norm_num))) xp)
  have hd' := hd.trans (mul_le_mul_of_nonneg_left
    (wd.trans (mul_le_mul_of_nonneg_left nd (by norm_num))) xp)
  nlinarith only [hi',hd',mul_nonneg bp (sq_nonneg (totalLength incWindows-totalLength decWindows))]

end PrimeFactors.TraceStripPacking
