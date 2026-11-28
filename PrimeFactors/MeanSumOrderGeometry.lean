import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-! Rational rectangle bounds on the triangular region x ≤ y, xy > 1/2.
The two normalized lengths are D=(√y−√x)² before the true sum, and
G=(1−x)(1−y) after it. The grid counts each unordered pair once. -/

namespace PrimeFactors.MeanSumOrderGeometry

open Finset

set_option maxRecDepth 4096

abbrev mesh : ℕ := 256
abbrev scale : ℕ := 16777216
abbrev Q : ℕ := 281474976710656
noncomputable def indices : Finset ℕ := Ico 128 mesh

def possible (i j : ℕ) : Bool := i ≤ j && mesh^2<2*(i+1)*(j+1)
def full (i j : ℕ) : Bool := i<j && mesh^2 ≤ 2*i*j

noncomputable def D (x y : ℝ) := (Real.sqrt y - Real.sqrt x)^2
noncomputable def G (x y : ℝ) := (1-x)*(1-y)

private def roots : List ℕ := [
  11863283,11909533,11955605,12001500,12047221,12092768,12138144,12183352,12228392,12273267,
  12317978,12362528,12406918,12451150,12495225,12539145,12582912,12626527,12669992,12713308,
  12756477,12799501,12842380,12885117,12927713,12970168,13012485,13054665,13096710,13138619,
  13180395,13222040,13263553,13304937,13346193,13387322,13428324,13469202,13509956,13550588,
  13591098,13631488,13671758,13711910,13751945,13791863,13831667,13871356,13910932,13950396,
  13989748,14028990,14068123,14107147,14146063,14184873,14223576,14262175,14300670,14339061,
  14377349,14415536,14453622,14491608,14529495,14567283,14604973,14642566,14680064,14717465,
  14754772,14791984,14829104,14866130,14903065,14939908,14976660,15013323,15049896,15086381,
  15122778,15159087,15195309,15231446,15267497,15303462,15339344,15375142,15410856,15446489,
  15482039,15517507,15552895,15588202,15623430,15658578,15693648,15728640,15763553,15798390,
  15833150,15867834,15902442,15936975,15971433,16005817,16040128,16074365,16108530,16142622,
  16176642,16210591,16244469,16278277,16312014,16345682,16379280,16412810,16446271,16479665,
  16512991,16546250,16579442,16612568,16645627,16678622,16711551,16744415,16777216]

private def rootLo (i : ℕ) := roots[i-128]?.getD 0
private def rootHi (i : ℕ) :=
  let r := rootLo i
  if mesh*r^2 = i*Q then r else r+1

def dLo (i j : ℕ) := (rootLo j - rootHi (i+1))^2
def dHi (i j : ℕ) := (rootHi (j+1) - rootLo i)^2
def gLo (i j : ℕ) := 65536^2*(mesh-i-1)*(mesh-j-1)
def gHi (i j : ℕ) := 65536^2*(mesh-i)*(mesh-j)

private theorem root_cert {i : ℕ} (lo : 128 ≤ i) (hi : i ≤ mesh) :
    mesh*(rootLo i)^2 ≤ i*Q ∧ i*Q ≤ mesh*(rootHi i)^2 := by
  have all : ∀ k : Fin 129, let a := k.val+128
      mesh*(rootLo a)^2 ≤ a*Q ∧ a*Q ≤ mesh*(rootHi a)^2 := by decide +kernel
  change i ≤ 256 at hi
  have h : i-128 < 129 := by omega
  have cert := all ⟨i-128,h⟩
  dsimp only at cert
  rwa [Nat.sub_add_cancel lo] at cert

private theorem root_bounds {i : ℕ} (mem : i∈indices) {x : ℝ}
    (lo : i ≤ (mesh:ℝ)*x) (hi : (mesh:ℝ)*x ≤ i+1) :
    (rootLo i : ℝ) ≤ scale*Real.sqrt x ∧ scale*Real.sqrt x ≤ (rootHi (i+1):ℝ) := by
  obtain ⟨il,iu⟩ := mem_Ico.mp mem
  have a : (256:ℝ)*(rootLo i)^2 ≤ i*281474976710656 := by
    exact_mod_cast (root_cert il iu.le).1
  have b : ((i:ℝ)+1)*281474976710656 ≤ 256*(rootHi (i+1))^2 := by
    exact_mod_cast (root_cert (by omega : 128 ≤ i+1) iu).2
  change (i:ℝ) ≤ 256*x at lo
  change 256*x ≤ i+1 at hi
  have pos : 0 ≤ x := by linarith only [lo, Nat.cast_nonneg (α:=ℝ) i]
  constructor
  · apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt pos]
    change (rootLo i:ℝ)^2 ≤ (16777216:ℝ)^2*x
    linarith only [a,lo]
  · apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt pos]
    change (16777216:ℝ)^2*x ≤ (rootHi (i+1):ℝ)^2
    linarith only [b,hi]

set_option maxHeartbeats 800000 in
/-- Pointwise bounds with integer numerators and common denominator Q.
Both closed box edges are admitted to simplify applying this to integer bins. -/
theorem cell_bounds {i j : ℕ} (im : i∈indices) (jm : j∈indices) {x y : ℝ}
    (xl : i ≤ (mesh:ℝ)*x) (xu : (mesh:ℝ)*x ≤ i+1)
    (yl : j ≤ (mesh:ℝ)*y) (yu : (mesh:ℝ)*y ≤ j+1) (sorted : x ≤ y) :
    (dLo i j : ℝ) ≤ Q*D x y ∧ Q*D x y ≤ (dHi i j : ℝ) ∧
    (gLo i j : ℝ) ≤ Q*G x y ∧ Q*G x y ≤ (gHi i j : ℝ) := by
  obtain ⟨xa,xb⟩ := root_bounds im xl xu
  obtain ⟨ya,yb⟩ := root_bounds jm yl yu
  let d := (scale:ℝ)*(Real.sqrt y - Real.sqrt x)
  have dn : 0 ≤ d := mul_nonneg (by positivity) (sub_nonneg.mpr (Real.sqrt_le_sqrt sorted))
  have dl : ((rootLo j-rootHi (i+1):ℕ):ℝ) ≤ d := by
    by_cases ord : rootHi (i+1) ≤ rootLo j
    · rw [Nat.cast_sub ord]
      dsimp only [d]
      linarith only [xb,ya]
    · simpa [Nat.sub_eq_zero_of_le (le_of_not_ge ord)] using dn
  have ord : rootLo i ≤ rootHi (j+1) := by
    exact_mod_cast xa.trans ((mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt sorted)
      (by positivity : 0 ≤ (scale:ℝ))).trans yb)
  have du : d ≤ ((rootHi (j+1)-rootLo i:ℕ):ℝ) := by
    rw [Nat.cast_sub ord]
    dsimp only [d]
    linarith only [xa,yb]
  have ds : d^2=(Q:ℝ)*D x y := by dsimp [d,D,scale,Q]; ring
  have ic := (mem_Ico.mp im).2
  have jc := (mem_Ico.mp jm).2
  have il : ((mesh-i-1:ℕ):ℝ) ≤ mesh*(1-x) := by
    rw [Nat.sub_sub,Nat.cast_sub (by omega),Nat.cast_add,Nat.cast_one]; linarith only [xu]
  have jl : ((mesh-j-1:ℕ):ℝ) ≤ mesh*(1-y) := by
    rw [Nat.sub_sub,Nat.cast_sub (by omega),Nat.cast_add,Nat.cast_one]; linarith only [yu]
  have iu : (mesh:ℝ)*(1-x) ≤ ((mesh-i:ℕ):ℝ) := by rw [Nat.cast_sub ic.le]; linarith only [xl]
  have ju : (mesh:ℝ)*(1-y) ≤ ((mesh-j:ℕ):ℝ) := by rw [Nat.cast_sub jc.le]; linarith only [yl]
  have gl := mul_le_mul il jl (Nat.cast_nonneg _) ((Nat.cast_nonneg _).trans il)
  have gu := mul_le_mul iu ju ((Nat.cast_nonneg _).trans jl) (Nat.cast_nonneg _)
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [dLo,Nat.cast_pow,←ds] using pow_le_pow_left₀ (Nat.cast_nonneg _) dl 2
  · simpa only [dHi,Nat.cast_pow,←ds] using pow_le_pow_left₀ dn du 2
  · simp only [gLo,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,G]
    change _ ≤ 281474976710656*((1-x)*(1-y))
    change _ ≤ (256*(1-x))*(256*(1-y)) at gl
    nlinarith only [gl]
  · simp only [gHi,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,G]
    change 281474976710656*((1-x)*(1-y)) ≤ _
    change (256*(1-x))*(256*(1-y)) ≤ _ at gu
    nlinarith only [gu]

noncomputable def sumFull (f : ℕ → ℕ → ℕ) :=
  ∑ i ∈ indices, ∑ j ∈ indices, if full i j then f i j else 0

noncomputable def sumPossible (f : ℕ → ℕ → ℕ) :=
  ∑ i ∈ indices, ∑ j ∈ indices, if possible i j then f i j else 0

set_option maxRecDepth 16384 in
/-- Exact sums before multiplying by the common cell area 1/mesh² and
dividing by the common fixed-point denominator Q. -/
theorem grid_totals :
    sumFull dLo=18546979888483033 ∧ sumPossible dHi=20783259569430118 ∧
    sumFull gLo=37128158322884608 ∧ sumPossible gHi=41811592525905920 ∧
    sumFull (fun _ _ => 1)=4922 ∧ sumPossible (fun _ _ => 1)=5124 := by
  decide +kernel

end PrimeFactors.MeanSumOrderGeometry
