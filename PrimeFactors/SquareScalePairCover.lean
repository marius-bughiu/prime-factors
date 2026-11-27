import PrimeFactors.FareyWrap
import PrimeFactors.SquareScalePairCoordinates
import PrimeFactors.SquareScaleHarmonicBound

/-! Finite covering count for pairs of positive integers A,B ≤ H admitting
coordinates A=d*u*x² and B=d*v*z² with u*v ≤ L. -/
namespace PrimeFactors.SquareScalePairCover

open Finset

private def height (H d u : ℕ) := (H/(d*u)).sqrt

private noncomputable def block (H d u v : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 (height H d u)) ×ˢ (Icc 1 (height H d v))).image
    (fun (x,z) => (d*u*x^2,d*v*z^2))

/-- A pair can have more than one representation in this cover. -/
noncomputable def cover (H L : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 H).biUnion fun d => (Icc 1 L).biUnion fun u =>
    (Icc 1 (L/u)).biUnion fun v => block H d u v

theorem mem_cover {A B H L d u v x z : ℕ} (dpos : 0 < d) (upos : 0 < u)
    (vpos : 0 < v) (xpos : 0 < x) (zpos : 0 < z) (smallA : A ≤ H) (smallB : B ≤ H)
    (eqA : A=d*u*x^2) (eqB : B=d*v*z^2) (uv : u*v ≤ L) : (A,B) ∈ cover H L := by
  have bound {m n a : ℕ} (pm : 0 < m) (eqn : a=d*m*n^2) (ah : a ≤ H) : n ≤ height H d m := by
    apply Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le (Nat.mul_pos dpos pm)).mpr ?_)
    simpa only [eqn,Nat.mul_comm (n^2)] using ah
  have dh : d ≤ H := calc
    d ≤ d*(u*x^2) := Nat.le_mul_of_pos_right _ (Nat.mul_pos upos (pow_pos xpos 2))
    _ = A := by rw [eqA,Nat.mul_assoc]
    _ ≤ H := smallA
  have uh := (Nat.le_mul_of_pos_right u vpos).trans uv
  have vh : v ≤ L/u := (Nat.le_div_iff_mul_le upos).mpr (Nat.mul_comm v u ▸ uv)
  refine mem_biUnion.mpr ⟨d, mem_Icc.mpr ⟨dpos,dh⟩, mem_biUnion.mpr ⟨u,mem_Icc.mpr ⟨upos,uh⟩,
    mem_biUnion.mpr ⟨v,mem_Icc.mpr ⟨vpos,vh⟩,mem_image.mpr ⟨(x,z),?_,?_⟩⟩⟩⟩
  · exact mem_product.mpr ⟨mem_Icc.mpr ⟨xpos,bound upos eqA smallA⟩,
      mem_Icc.mpr ⟨zpos,bound vpos eqB smallB⟩⟩
  · exact Prod.ext eqA.symm eqB.symm

private theorem block_bound {H d u v : ℕ} (hd : 0 < d) (hu : 0 < u) (hv : 0 < v) :
    ((block H d u v).card:ℝ) ≤ H/((d:ℝ)*Real.sqrt ((u:ℝ)*v)) := by
  have count : (block H d u v).card ≤ height H d u * height H d v := by
    exact card_image_le.trans_eq (by simp only [card_product,Nat.card_Icc,Nat.add_sub_cancel])
  let X := height H d u
  let Z := height H d v
  have height_sq (a : ℕ) (ha : 0 < a) : (height H d a)^2*(d*a) ≤ H :=
    (Nat.le_div_iff_mul_le (Nat.mul_pos hd ha)).mp (Nat.sqrt_le' _)
  have mul := Nat.mul_le_mul (height_sq u hu) (height_sq v hv)
  have lifted : ((X:ℝ)^2*(d*u))*((Z:ℝ)^2*(d*v)) ≤ (H:ℝ)*(H:ℝ) := by exact_mod_cast mul
  have rt : 0 < Real.sqrt ((u:ℝ)*v) := Real.sqrt_pos.mpr (by positivity)
  have square : ((X:ℝ)*Z*((d:ℝ)*Real.sqrt ((u:ℝ)*v)))^2 ≤ (H:ℝ)^2 := calc
    _ = ((X:ℝ)^2*(d*u))*((Z:ℝ)^2*(d*v)) := by simp only [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ (u:ℝ)*v)]; ring
    _ ≤ _ := by simpa only [pow_two] using lifted
  apply (le_div_iff₀ (mul_pos (by exact_mod_cast hd) rt)).mpr
  have card_le : ((block H d u v).card:ℝ) ≤ (X:ℝ)*Z := by exact_mod_cast count
  exact (mul_le_mul_of_nonneg_right card_le (by positivity)).trans
    ((sq_le_sq₀ (by positivity) (by positivity)).mp square)

/-- Count the two free square roots together before summing over the three
parameters. The bound has a harmonic weight in the common part d. -/
theorem card_bound (H L : ℕ) : ((cover H L).card : ℝ) ≤
    ∑ d ∈ Icc 1 H, ∑ u ∈ Icc 1 L, ∑ v ∈ Icc 1 (L/u),
      (H:ℝ)/((d:ℝ)*Real.sqrt ((u:ℝ)*v)) := by
  have unions : (cover H L).card ≤
      ∑ d ∈ Icc 1 H, ∑ u ∈ Icc 1 L, ∑ v ∈ Icc 1 (L/u), (block H d u v).card := by
    refine card_biUnion_le.trans (sum_le_sum fun d _ => ?_)
    exact card_biUnion_le.trans (sum_le_sum fun u _ => card_biUnion_le)
  have realUnions := (Nat.cast_le (α:=ℝ)).mpr unions
  push_cast at realUnions
  refine realUnions.trans (sum_le_sum fun d hd => sum_le_sum fun u hu => sum_le_sum fun v hv => ?_)
  exact block_bound (mem_Icc.mp hd).1 (mem_Icc.mp hu).1 (mem_Icc.mp hv).1

/-- Cover any set of bounded positive pairs without assuming that their
given scale t is the least scale or even squarefree. -/
theorem finite_count {H L : ℕ} (pairs : Finset (ℕ × ℕ))
    (valid : ∀ z ∈ pairs, 0 < z.1 ∧ z.1 ≤ H ∧ 0 < z.2 ∧ z.2 ≤ H ∧
      ∃ t y : ℕ, 0 < t ∧ t ≤ L ∧ z.1*z.2=t*y^2) :
    (pairs.card : ℝ) ≤ SquareScaleHarmonicBound.weight H L := by
  have subset : pairs ⊆ cover H L := by
    rintro ⟨A,B⟩ mem
    obtain ⟨ap,ah,bp,bh,t,y,tp,cap,hit⟩ := valid (A,B) mem
    obtain ⟨d,u,v,x,z,dp,up,vp,xp,zp,eqA,eqB,uv,_⟩ :=
      SquareScalePairCoordinates.coordinates ap bp tp cap hit
    exact mem_cover dp up vp xp zp ah bh eqA eqB uv
  exact (show (pairs.card:ℝ) ≤ (cover H L).card by exact_mod_cast card_le_card subset).trans (card_bound H L)

end PrimeFactors.SquareScalePairCover
