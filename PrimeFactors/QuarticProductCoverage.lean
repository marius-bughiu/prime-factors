import PrimeFactors.RecognizingQuarticProducts
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-! Counting the odd integers of the form x⁴ + 4y⁴ in the fourth-power
cell starting at x⁴, for positive x,y. No prime condition is imposed. -/
namespace PrimeFactors.QuarticProductCoverage

open Finset
open scoped Classical Interval

/-- `x=2j+1` is the odd positive base. Both endpoints for `y` are inclusive. -/
def Represented (n : ℕ) : Prop := ∃ j y : ℕ, 0<y ∧ n=(2*j+1)^4+4*y^4 ∧ n<(2*j+2)^4

noncomputable def values (X : ℕ) := (range (X+1)).filter Represented

private theorem member {X n : ℕ} : n∈values X ↔ n≤X ∧ Represented n := by
  simp only [values,mem_filter,mem_range,Nat.lt_succ_iff]

private theorem count_mono {X Y : ℕ} (le : X≤Y) : (values X).card≤(values Y).card :=
  card_le_card (fun _ h => member.mpr ⟨(member.mp h).1.trans le,(member.mp h).2⟩)

private theorem parity (x y : ℕ) : (x^4+4*y^4)%2=x%2 := by
  have h : x%2=0 ∨ x%2=1 := by omega
  calc
    _ = x^4%2 := by omega
    _ = (x%2)^4%2 := Nat.pow_mod ..
    _ = x%2 := by rcases h with h|h <;> rw [h]

/-- Membership agrees with the public recognizer restricted to odd inputs. -/
theorem mem_iff {X n : ℕ} : n∈values X ↔ n≤X ∧ Odd n ∧
    (RecognizingQuarticProducts.recognize n).isSome=true := by
  rw [member,RecognizingQuarticProducts.recognizes_iff]
  refine and_congr_right (fun _ => ⟨?_,?_⟩)
  · rintro ⟨j,y,yp,rfl,top⟩
    exact ⟨Nat.odd_iff.mpr (by rw [parity]; omega),2*j+1,y,by omega,yp,rfl,top⟩
  · rintro ⟨odd,x,y,xp,yp,rfl,top⟩
    have odd_x := Nat.odd_iff.mpr ((parity x y).symm.trans (Nat.odd_iff.mp odd))
    obtain ⟨j,rfl⟩ := odd_x
    exact ⟨j,y,yp,rfl,top⟩

private def room (x : ℕ) := (4*x^3+6*x^2+4*x)/4

def cap (x : ℕ) := (room x).sqrt.sqrt

private theorem root_le {y n : ℕ} : y≤n.sqrt.sqrt ↔ y^4≤n := by
  rw [Nat.le_sqrt',Nat.le_sqrt',←pow_mul]

private theorem cap_iff (x y : ℕ) : y≤cap x ↔ x^4+4*y^4<(x+1)^4 := by
  rw [cap,root_le,room,Nat.le_div_iff_mul_le (by decide),show (x+1)^4=x^4+4*x^3+6*x^2+4*x+1 by ring]
  omega

private noncomputable def fiber (x : ℕ) := (Icc 1 (cap x)).image (fun y => x^4+4*y^4)

private theorem fiber_card (x : ℕ) : (fiber x).card=cap x := by
  rw [fiber,card_image_of_injective, Nat.card_Icc]; omega
  intro a b same
  change x^4+4*a^4=x^4+4*b^4 at same
  obtain eq : a^4=b^4 := by omega
  exact (Nat.pow_left_inj (by decide : 4≠0)).mp eq

private theorem mem_fiber {x n : ℕ} : n∈fiber x ↔ ∃ y : ℕ, 0<y ∧ n=x^4+4*y^4 ∧ n<(x+1)^4 := by
  simp only [fiber,mem_image,mem_Icc]
  constructor
  · rintro ⟨y,⟨lo,hi⟩,rfl⟩
    exact ⟨y,lo,rfl,(cap_iff x y).mp hi⟩
  · rintro ⟨y,lo,rfl,hi⟩
    exact ⟨y,⟨lo,(cap_iff x y).mpr hi⟩,rfl⟩

private theorem cell_index {j m n : ℕ} (base : (2*j+1)^4<n) (top : n≤(2*m)^4) : j<m := by
  by_contra! rev
  have bad := Nat.pow_le_pow_left (show 2*m≤2*j+1 by omega) 4
  omega

private theorem endpoints (m : ℕ) : values ((2*m)^4) =
    (range m).biUnion (fun j => fiber (2*j+1)) := by
  ext n
  rw [member,mem_biUnion]
  constructor
  · rintro ⟨top,j,y,yp,h,hi⟩
    have positive : 0<y^4 := pow_pos yp _
    exact ⟨j,mem_range.mpr (cell_index (by omega) top),mem_fiber.mpr ⟨y,yp,h,hi⟩⟩
  · rintro ⟨j,hj,h⟩
    obtain ⟨y,yp,eq,hi⟩ := mem_fiber.mp h
    have jlt := mem_range.mp hj
    have top := Nat.pow_le_pow_left (show 2*j+1+1≤2*m by omega) 4
    exact ⟨hi.le.trans top,j,y,yp,eq,hi⟩

private theorem separate {i j : ℕ} (ij : i<j) : Disjoint (fiber (2*i+1)) (fiber (2*j+1)) := by
  apply disjoint_left.mpr
  intro n left right
  obtain ⟨_,_,_,low⟩ := mem_fiber.mp left
  obtain ⟨y,_,rfl,_⟩ := mem_fiber.mp right
  have order := Nat.pow_le_pow_left (show 2*i+1+1≤2*j+1 by omega) 4
  omega

/-- Exact count of distinct odd integers through every fourth power of an even base. -/
theorem exact_endpoint (m : ℕ) : (values ((2*m)^4)).card=∑ j∈range m,cap (2*j+1) := by
  rw [endpoints,card_biUnion (fun i _ j _ ne => (lt_or_gt_of_ne ne).elim separate (fun lt => (separate lt).symm))]
  simp only [fiber_card]

/-- At an odd fourth-power endpoint the new cell has not yet contributed
its first positive y. The same formula therefore covers every fourth power. -/
theorem exact_fourth (k : ℕ) : (values (k^4)).card=∑ j∈range (k/2),cap (2*j+1) := by
  rw [←exact_endpoint]
  apply congrArg card
  ext n
  rw [member,member]
  constructor
  · rintro ⟨le,rep⟩
    obtain ⟨j,y,yp,eq,hi⟩ := rep
    have pos : 0<y^4 := pow_pos yp _
    have less : (2*j+1)^4<k^4 := by omega
    have base : 2*j+1<k := lt_of_not_ge (fun rev => (not_le_of_gt less) (Nat.pow_le_pow_left rev 4))
    exact ⟨hi.le.trans (Nat.pow_le_pow_left (by omega : 2*j+2≤2*(k/2)) 4),j,y,yp,eq,hi⟩
  · rintro ⟨le,rep⟩
    exact ⟨le.trans (Nat.pow_le_pow_left (by omega : 2*(k/2)≤k) 4),rep⟩

private theorem cap_eq {x y : ℕ} (lo : x^4+4*y^4<(x+1)^4)
    (hi : (x+1)^4≤x^4+4*(y+1)^4) : cap x=y := by
  have lower := (cap_iff x y).mpr lo
  have upper := (cap_iff x (y+1)).not.mpr (not_lt_of_ge hi)
  omega

theorem control : (values 65536).card=35 := by
  let counts : Fin 8 → ℕ := ![1,2,3,4,5,6,7,7]
  have cells (i : Fin 8) : cap (2*i.val+1)=counts i := by
    fin_cases i <;> apply cap_eq <;> decide +kernel
  calc
    (values 65536).card = ∑ j∈range (16/2),cap (2*j+1) := exact_fourth 16
    _ = ∑ i : Fin 8, cap (2*i.val+1) := (Fin.sum_univ_eq_sum_range _ _).symm
    _ = ∑ i : Fin 8, counts i := Finset.sum_congr rfl (fun i _ => cells i)
    _ = 35 := by decide +kernel

private theorem cap_powers (x : ℕ) : (cap x)^4≤(x+1)^3 ∧ x^3<(cap x+1)^4 := by
  have low : x^3≤room x := by rw [room,Nat.le_div_iff_mul_le (by decide)]; omega
  have hi : room x≤(x+1)^3 := by
    rw [room,show (x+1)^3=x^3+3*x^2+3*x+1 by ring]; omega
  have le := root_le.mp (le_refl (cap x))
  have gt : room x<(cap x+1)^4 := by
    by_contra! bad
    have := root_le.mpr bad
    change cap x+1≤cap x at this
    omega
  exact ⟨le.trans hi,low.trans_lt gt⟩

private noncomputable def f (x : ℝ) := x^(3/4:ℝ)
private noncomputable def F (x : ℝ) := (2/7:ℝ)*x^(7/4:ℝ)

private theorem quarter (x : ℝ) (hx : 0≤x) (n : ℕ) :
    (x^n)^(1/4:ℝ)=x^((n:ℝ)/4) := by rw [←Real.rpow_natCast_mul hx]; congr 1; ring

private theorem cap_bounds (x : ℕ) : f x-1≤(cap x:ℝ) ∧ (cap x:ℝ)≤f (x+1) := by
  obtain ⟨hi,lo⟩ := cap_powers x
  have lower := Real.rpow_le_rpow (by positivity : 0≤(x:ℝ)^3)
    (by exact_mod_cast lo.le : (x:ℝ)^3≤((cap x:ℝ)+1)^4) (by norm_num : (0:ℝ)≤1/4)
  have upper := Real.rpow_le_rpow (by positivity : 0≤(cap x:ℝ)^4)
    (by exact_mod_cast hi : (cap x:ℝ)^4≤((x:ℝ)+1)^3) (by norm_num : (0:ℝ)≤1/4)
  rw [quarter _ (by positivity),quarter _ (by positivity)] at lower upper
  norm_num only [Nat.cast_ofNat,div_self (by norm_num : (4:ℝ)≠0),Real.rpow_one] at lower upper
  exact ⟨by unfold f; linarith only [lower],upper⟩

private theorem f_mono {a b : ℝ} (pos : 0≤a) (le : a≤b) : f a≤f b :=
  Real.rpow_le_rpow pos le (by norm_num)

private theorem integral_bounds (a : ℝ) (pos : 0≤a) :
    f a ≤ F (a+2)-F a ∧ F (a+2)-F a ≤ f (a+2) := by
  have le : a≤a+2 := by linarith
  have cont : Continuous f := Real.continuous_rpow_const (by norm_num : (0:ℝ)≤3/4)
  have lower := intervalIntegral.integral_mono_on (μ:=MeasureTheory.volume) (f:=fun _ => f a) (g:=f) le
    intervalIntegrable_const (cont.intervalIntegrable ..) (fun x hx => f_mono pos hx.1)
  have upper := intervalIntegral.integral_mono_on (μ:=MeasureTheory.volume) (f:=f) (g:=fun _ => f (a+2)) le
    (cont.intervalIntegrable ..) intervalIntegrable_const (fun x hx => f_mono (pos.trans hx.1) hx.2)
  have val : (∫ x in a..a+2, f x)=2*(F (a+2)-F a) := by
    change (∫ x in a..a+2, x^(3/4:ℝ))=_
    rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ)<3/4))]
    norm_num [F]; ring
  rw [intervalIntegral.integral_const,val] at lower
  rw [intervalIntegral.integral_const,val] at upper
  simp only [smul_eq_mul] at lower upper
  constructor <;> linarith

private noncomputable def total (m : ℕ) : ℝ := ∑ j∈range m,(cap (2*j+1):ℝ)

private theorem total_bounds (m : ℕ) :
    F (2*m)-(m+f (2*m))≤total m ∧ total m≤F (2*m)+f (2*m) := by
  induction m with
  | zero => norm_num [F,f,total,Real.zero_rpow]
  | succ m ih =>
    have step : total (m+1)=total m+cap (2*m+1) := sum_range_succ ..
    have edge : (2:ℝ)*((m:ℝ)+1)=2*m+2 := by ring
    have val := cap_bounds (2*m+1)
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at val
    rw [show (2:ℝ)*m+1+1=2*m+2 by ring] at val
    have geom := integral_bounds (2*m) (by positivity)
    have monot := f_mono (by positivity : 0≤(2:ℝ)*m) (show (2:ℝ)*m≤2*m+1 by linarith)
    rw [step,Nat.cast_succ,edge]
    constructor <;> linarith only [ih.1,ih.2,val.1,val.2,geom.1,geom.2,monot]

private theorem count_endpoint_real (m : ℕ) : ((values ((2*m)^4)).card:ℝ)=total m := by
  rw [exact_endpoint,total,Nat.cast_sum]

private theorem f_nat_le (k : ℕ) : f k≤k := by
  rcases k with _|k
  · norm_num [f,Real.zero_rpow]
  · exact Real.rpow_le_self_of_one_le (by exact_mod_cast Nat.succ_pos k) (by norm_num)

private theorem F_mono {a b : ℝ} (pos : 0≤a) (le : a≤b) : F a≤F b :=
  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow pos le (by norm_num)) (by norm_num)

/-- Uniform error for the cumulative count, including the final partial fourth-power cell. -/
theorem coverage (X : ℕ) :
    |((values X).card:ℝ)-(2/7:ℝ)*(X:ℝ)^(7/16:ℝ)| ≤ 3*(X:ℝ)^(1/4:ℝ)+4 := by
  let r := RecognizingQuarticProducts.fourthRoot X
  let m := r/2
  have endpoints := RecognizingQuarticProducts.fourthRoot_eq_iff.mp (show RecognizingQuarticProducts.fourthRoot X=r from rfl)
  have l : 2*m≤r := by dsimp [m]; omega
  have u : r+1≤2*(m+1) := by dsimp [m]; omega
  have low := (Nat.pow_le_pow_left l 4).trans endpoints.1
  have top := endpoints.2.le.trans (Nat.pow_le_pow_left u 4)
  have c1 : ((values ((2*m)^4)).card:ℝ)≤(values X).card := by exact_mod_cast count_mono low
  have c2 : ((values X).card:ℝ)≤(values ((2*(m+1))^4)).card := by exact_mod_cast count_mono top
  rw [count_endpoint_real] at c1 c2
  let z := (X:ℝ)^(1/4:ℝ)
  have left := Real.rpow_le_rpow (by positivity : 0≤((2:ℝ)*m)^4) (by exact_mod_cast low : ((2:ℝ)*m)^4≤X) (by norm_num : (0:ℝ)≤1/4)
  have right := Real.rpow_le_rpow (Nat.cast_nonneg X) (by exact_mod_cast top : (X:ℝ)≤((2:ℝ)*(m+1))^4) (by norm_num : (0:ℝ)≤1/4)
  rw [quarter _ (by positivity)] at left right
  norm_num only [Nat.cast_ofNat,div_self (by norm_num : (4:ℝ)≠0),Real.rpow_one] at left right
  change (2:ℝ)*m≤z at left
  have edge : (2:ℝ)*((m:ℝ)+1)=2*m+2 := by ring
  rw [edge] at right
  change z≤2*m+2 at right
  have model : F z=(2/7:ℝ)*(X:ℝ)^(7/16:ℝ) := by
    unfold F z
    rw [←Real.rpow_mul (Nat.cast_nonneg X)]
    norm_num
  rw [←model]
  change |((values X).card:ℝ)-F z|≤3*z+4
  have fl := F_mono (by positivity : 0≤(2:ℝ)*m) left
  have fu := F_mono ((by positivity : 0≤(2:ℝ)*m).trans left) right
  have inc := (integral_bounds (2*m) (by positivity)).2
  have lo := (total_bounds m).1.trans c1
  have hi := c2.trans (total_bounds (m+1)).2
  have f0 := f_nat_le (2*m)
  have f1 := f_nat_le (2*(m+1))
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,edge] at f0 f1 hi
  apply abs_le.mpr
  constructor <;> linarith only [fl,fu,inc,lo,hi,f0,f1,left,right]

end PrimeFactors.QuarticProductCoverage
