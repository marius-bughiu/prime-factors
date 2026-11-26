import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! Finite square-root cells for signed weighted square dependencies. All sizes are
natural-number bounds. The catalogue itself depends only on a cell and a residue. -/
namespace PrimeFactors.WeightedGrowingCells
open Finset

def stride (r ρ : ℕ) := Nat.gcd 24 (2*(r+ρ))

private theorem stride_pos (r ρ : ℕ) : 0<stride r ρ := Nat.gcd_pos_of_pos_left _ (by decide)
private theorem stride_le (r ρ : ℕ) : stride r ρ≤24 := Nat.gcd_le_left _ (by decide)

/-- All eligible signed labels satisfy the same public residue condition. -/
def Actual (n J r A : ℕ) : Prop := A ≡ r+n [MOD stride r n] ∧
  |(A:ℝ) - 2*Real.sqrt r*Real.sqrt n| ≤ (J:ℝ)*stride r n

def InBand (ρ v w J r A : ℕ) : Prop := A ≡ r+ρ [MOD stride r ρ] ∧
  2*Real.sqrt r*v-(J:ℝ)*stride r ρ ≤ A ∧
  (A:ℝ) ≤ 2*Real.sqrt r*((v:ℝ)+w)+(J:ℝ)*stride r ρ

noncomputable def labels (ρ v w J r : ℕ) : Finset ℕ := by
  classical
  exact (range (⌊2*Real.sqrt r*((v:ℝ)+w)+(J:ℝ)*stride r ρ⌋₊+1)).filter (InBand ρ v w J r)

@[simp] theorem mem_labels {ρ v w J r A : ℕ} : A∈labels ρ v w J r ↔ InBand ρ v w J r A := by
  classical
  simp only [labels,mem_filter,mem_range,and_iff_right_iff_imp]
  exact fun h => Nat.lt_succ_of_le (Nat.le_floor h.2.2)

/-- Membership holds for every input with this residue and square-root cell. -/
theorem actual_mem {n ρ v w J r A : ℕ} (res : n ≡ ρ [MOD 24])
    (lo : (v:ℝ)≤Real.sqrt n) (hi : Real.sqrt n≤(v:ℝ)+w) (h : Actual n J r A) :
    A∈labels ρ v w J r := by
  have orig := res.add_left r
  have same := (orig.mul_left 2).gcd_eq
  rw [Nat.gcd_comm _ 24,Nat.gcd_comm _ 24] at same
  change stride r n=stride r ρ at same
  rcases h with ⟨cong,bound⟩
  rw [same] at cong bound
  obtain ⟨lower,upper⟩ := abs_le.mp bound
  exact mem_labels.mpr ⟨cong.trans (orig.of_dvd (Nat.gcd_dvd_left ..)),by
    linarith only [lower,mul_le_mul_of_nonneg_left lo (show 0≤2*Real.sqrt r by positivity)],by
    linarith only [upper,mul_le_mul_of_nonneg_left hi (show 0≤2*Real.sqrt r by positivity)]⟩

/-- Integer division here gives the exact floor of the square-root width divided by the stride. -/
def rowCap (ρ w J r : ℕ) := 2*J+1+(4*r*w^2).sqrt / stride r ρ

private theorem gap_index {k s J r w : ℕ} (pos : 0<s)
    (gap : (k:ℝ)*s≤2*(J:ℝ)*s+2*Real.sqrt r*w) : k ≤ 2*J+(4*r*w^2).sqrt/s := by
  by_cases h : k≤2*J
  · exact h.trans (Nat.le_add_right ..)
  let z := k-2*J
  have eq : k=z+2*J := by dsimp [z]; omega
  rw [eq] at gap ⊢
  push_cast at gap
  have small : (z:ℝ)*s≤2*Real.sqrt r*w := by linarith only [gap]
  have sq := pow_le_pow_left₀ (show 0≤(z:ℝ)*s by positivity) small 2
  have rs := Real.sq_sqrt (show 0≤(r:ℝ) by positivity)
  have lim : ((z:ℝ)*s)^2 ≤ 4*(r:ℝ)*w^2 := by
    calc _ ≤ _ := sq
         _ = _ := by linear_combination 4*(w:ℝ)^2*rs
  have nsq : (z*s)^2≤4*r*w^2 := by exact_mod_cast lim
  have := (Nat.le_div_iff_mul_le pos).mpr (Nat.le_sqrt'.mpr nsq)
  omega

theorem labels_card (ρ v w J r : ℕ) : (labels ρ v w J r).card≤rowCap ρ w J r := by
  classical
  let S := labels ρ v w J r
  by_cases h : S.Nonempty
  · let a := S.min' h
    have amin : a∈S := min'_mem S h
    have ha := mem_labels.mp amin
    have sub : S ⊆ (range (rowCap ρ w J r)).image (fun k => a+k*stride r ρ) := by
      intro b hb
      have ab : a≤b := min'_le _ _ hb
      have hB := mem_labels.mp hb
      obtain ⟨k,hk⟩ := (Nat.modEq_iff_dvd' ab).mp (ha.1.trans hB.1.symm)
      have eq : b=a+k*stride r ρ := by rw [Nat.mul_comm] at hk; omega
      have eqr : (b:ℝ)=a+(k:ℝ)*stride r ρ := by exact_mod_cast eq
      have lim := gap_index (stride_pos r ρ) (show (k:ℝ)*stride r ρ≤2*(J:ℝ)*stride r ρ+2*Real.sqrt r*w by
        linarith only [ha.2.1,hB.2.2,eqr])
      exact mem_image.mpr ⟨k,mem_range.mpr (by dsimp [rowCap]; omega),eq.symm⟩
    exact (card_le_card sub).trans (card_image_le.trans_eq (card_range _))
  · change S.card≤_
    rw [not_nonempty_iff_eq_empty.mp h,card_empty]
    exact Nat.zero_le _

noncomputable def catalogue (ρ v w J K : ℕ) : Finset (ℕ×ℕ) :=
  (Icc 1 K).biUnion fun r => (labels ρ v w J r).image (Prod.mk r)

@[simp] theorem mem_catalogue {ρ v w J K r A : ℕ} : (r,A)∈catalogue ρ v w J K ↔
    1≤r ∧ r≤K ∧ InBand ρ v w J r A := by
  simp [catalogue,and_assoc]

noncomputable def catalogueCap (ρ w J K : ℕ) := ∑ r∈Icc 1 K, rowCap ρ w J r

theorem catalogue_card (ρ v w J K : ℕ) : (catalogue ρ v w J K).card≤catalogueCap ρ w J K :=
  card_biUnion_le.trans (sum_le_sum fun r _ => card_image_le.trans (labels_card ρ v w J r))

/-- Total anchor choices across all cells and permitted residues, counting every possible label. -/
theorem anchors_card (residues : Finset ℕ) (X cells w J K : ℕ) :
    (∑ i∈range cells, ∑ ρ∈residues, (catalogue ρ (X+i*w) w J K).card) ≤
      cells * ∑ ρ∈residues, catalogueCap ρ w J K := by
  calc _ ≤ ∑ _i∈range cells, ∑ ρ∈residues, catalogueCap ρ w J K :=
          sum_le_sum fun i _ => sum_le_sum fun ρ _ => catalogue_card ρ (X+i*w) w J K
       _ = _ := by simp

/-- Public integer upper bound on a signed excess, for a label within `F` of the endpoint. -/
def excessBound (X h F : ℕ) := F*(8*X*h+F)

private theorem sqrt_le_cap {r h : ℕ} (rk : r≤h^2) : Real.sqrt r≤(h:ℝ) :=
  Real.sqrt_le_iff.mpr ⟨by positivity,by exact_mod_cast rk⟩

private theorem real_excess {X h F r A : ℕ} {t : ℝ} (rk : r≤h^2)
    (t0 : 0≤t) (top : t≤2*(X:ℝ)) (near : |(A:ℝ)-2*Real.sqrt r*t|≤F) :
    |(A:ℝ)^2-4*r*t^2|≤(excessBound X h F:ℝ) := by
  let z := 2*Real.sqrt r*t
  have z0 : 0≤z := by dsimp [z]; positivity
  have zcap : z≤4*(X:ℝ)*h := by
    have m := mul_le_mul (sqrt_le_cap rk) top t0 (by positivity)
    dsimp [z]
    linarith only [m]
  change |(A:ℝ)-z|≤F at near
  have plus : (A:ℝ)+z≤8*(X:ℝ)*h+F := by linarith only [abs_le.mp near |>.2,zcap]
  have square : z^2=4*r*t^2 := by
    dsimp [z]
    linear_combination 4*t^2*Real.sq_sqrt (Nat.cast_nonneg r)
  rw [←square,sq_sub_sq,abs_mul,abs_of_nonneg (show 0≤(A:ℝ)+z by positivity)]
  rw [mul_comm]
  exact_mod_cast mul_le_mul near plus (by positivity) (Nat.cast_nonneg F)

/-- This bound uses the actual input and applies to labels below or above the endpoint. -/
theorem actual_excess {n r A J X h : ℕ} (rk : r≤h^2) (top : Real.sqrt n≤2*(X:ℝ))
    (a : Actual n J r A) : ((A:ℤ)^2-4*r*n).natAbs≤excessBound X h (24*J) := by
  have fj : J*stride r n ≤ 24*J := by simpa [Nat.mul_comm] using Nat.mul_le_mul_left J (stride_le r n)
  have near : |(A:ℝ)-2*Real.sqrt r*Real.sqrt n|≤(24*J:ℕ) := a.2.trans (by exact_mod_cast fj)
  have hh := real_excess rk (Real.sqrt_nonneg _) top near
  rw [Real.sq_sqrt (Nat.cast_nonneg n)] at hh
  apply (Nat.cast_le (α := ℝ)).mp
  simpa [Int.cast_natAbs,Int.cast_abs] using hh

/-- A full catalogue is controlled from its *left cell endpoint*, even for labels
introduced by a different input in the same cell. -/
def deviation (h w J : ℕ) := 24*J+2*h*w

theorem cell_excess {ρ r A J X h v w : ℕ} (rk : r≤h^2) (top : v≤2*X)
    (a : InBand ρ v w J r A) : |(A:ℝ)^2-4*r*(v:ℝ)^2|≤(excessBound X h (deviation h w J):ℝ) := by
  apply real_excess rk (by positivity) (by exact_mod_cast top)
  have bound : (J:ℝ)*stride r ρ≤24*J := by
    have := mul_le_mul_of_nonneg_left (show (stride r ρ:ℝ)≤24 by exact_mod_cast stride_le r ρ) (Nat.cast_nonneg J)
    linarith only [this]
  have ws := mul_le_mul_of_nonneg_right (sqrt_le_cap rk) (Nat.cast_nonneg w)
  simp only [deviation,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  apply abs_le.mpr
  constructor
  · linarith only [a.2.1,bound,show 0≤2*(h:ℝ)*w by positivity]
  · linarith only [a.2.2,bound,ws]

/-- The determinant uses only two public rows. -/
def determinant (i j : ℕ×ℕ) := ((j.1:ℤ)*i.2^2-(i.1:ℤ)*j.2^2).natAbs

def determinantBound (X h K w J : ℕ) := 2*K*excessBound X h (deviation h w J)

theorem cell_determinant {ρ v w J K X h : ℕ} {i j : ℕ×ℕ} (cap : K≤h^2) (top : v≤2*X)
    (hi : i∈catalogue ρ v w J K) (hj : j∈catalogue ρ v w J K) :
    determinant i j ≤ determinantBound X h K w J := by
  obtain ⟨r,A⟩ := i
  obtain ⟨s,B⟩ := j
  obtain ⟨_,rk,a⟩ := mem_catalogue.mp hi
  obtain ⟨_,sk,b⟩ := mem_catalogue.mp hj
  let E := excessBound X h (deviation h w J)
  have ar := cell_excess (rk.trans cap) top a
  have br := cell_excess (sk.trans cap) top b
  have m1 : (s:ℝ)*|(A:ℝ)^2-4*r*(v:ℝ)^2|≤K*(E:ℝ) :=
    mul_le_mul (by exact_mod_cast sk) ar (abs_nonneg _) (by positivity)
  have m2 : (r:ℝ)*|(B:ℝ)^2-4*s*(v:ℝ)^2|≤K*(E:ℝ) :=
    mul_le_mul (by exact_mod_cast rk) br (abs_nonneg _) (by positivity)
  have eq : (s:ℝ)*A^2-r*(B:ℝ)^2 = s*((A:ℝ)^2-4*r*(v:ℝ)^2) - r*((B:ℝ)^2-4*s*(v:ℝ)^2) := by ring
  have f : |(s:ℝ)*A^2-r*(B:ℝ)^2| ≤ 2*K*(E:ℝ) := by
    rw [eq]
    apply (abs_sub _ _).trans
    simp only [abs_mul,abs_of_nonneg (Nat.cast_nonneg s : (0:ℝ)≤s),abs_of_nonneg (Nat.cast_nonneg r : (0:ℝ)≤r)]
    linarith only [m1,m2]
  change ((s:ℤ)*A^2-r*(B:ℤ)^2).natAbs≤2*K*E
  apply (Nat.cast_le (α := ℝ)).mp
  simpa [Int.cast_natAbs,Int.cast_abs] using f

/-- Positive support for a specified anchor. Proportional rows contribute a factor of one. -/
noncomputable def support (S : Finset (ℕ×ℕ)) (i : ℕ×ℕ) :=
  ∏ j∈S.erase i, max 1 (determinant i j)

theorem support_pos (S : Finset (ℕ×ℕ)) (i : ℕ×ℕ) : 0<support S i :=
  prod_pos fun _ _ => lt_of_lt_of_le (by decide : 0<1) (le_max_left ..)

theorem support_le {ρ v w J K X h : ℕ} {i : ℕ×ℕ} (cap : K≤h^2) (top : v≤2*X)
    (pos : 0<determinantBound X h K w J) (hi : i∈catalogue ρ v w J K) :
    support (catalogue ρ v w J K) i ≤ (determinantBound X h K w J)^(catalogueCap ρ w J K-1) := by
  let S := catalogue ρ v w J K
  let C := determinantBound X h K w J
  calc
    support S i ≤ ∏ _j∈S.erase i, C :=
      Finset.prod_le_prod' fun j hj => max_le pos (cell_determinant cap top hi (mem_of_mem_erase hj))
    _ = C^(S.card-1) := by rw [prod_const,card_erase_of_mem hi]
    _ ≤ _ := Nat.pow_le_pow_right pos (Nat.sub_le_sub_right (catalogue_card ρ v w J K) 1)

/-- Ceiling division for the number of cells covering the octave `[X, 2X)`. -/
def cellCount (X w : ℕ) := (X+w-1)/w

/-- The computed cell reaches the integer floor of the input square root and its
entire fractional part. The final cell may extend beyond the top of the octave. -/
theorem locate {n X w : ℕ} (wp : 0<w) (lower : X≤n.sqrt) (upper : n.sqrt<2*X) :
    let i := (n.sqrt-X)/w
    i < cellCount X w ∧ X+i*w<2*X ∧ (X+i*w:ℕ)≤Real.sqrt n ∧
      Real.sqrt n<(X+i*w:ℕ)+ (w:ℝ) := by
  let i := (n.sqrt-X)/w
  have ceil : X≤cellCount X w*w := by
    have h := Nat.div_add_mod' (X+w-1) w
    have m := Nat.mod_lt (X+w-1) wp
    dsimp [cellCount]
    omega
  have hi : i<cellCount X w := (Nat.div_lt_iff_lt_mul wp).mpr (by omega)
  have ht := Nat.div_mul_le_self (n.sqrt-X) w
  have hf := Nat.div_add_mod' (n.sqrt-X) w
  have mr := Nat.mod_lt (n.sqrt-X) wp
  change i*w≤n.sqrt-X at ht
  change i*w+(n.sqrt-X)%w=n.sqrt-X at hf
  have v1 : X+i*w≤n.sqrt := by omega
  have v2 : n.sqrt+1≤X+i*w+w := by omega
  have a : (n.sqrt:ℝ)≤Real.sqrt n := Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' n)
  have b : Real.sqrt n < ((n.sqrt+1:ℕ):ℝ) := Real.sqrt_lt' (by positivity) |>.mpr (by exact_mod_cast Nat.lt_succ_sqrt' n)
  exact ⟨hi,v1.trans_lt upper,le_trans (by exact_mod_cast v1) a,lt_of_lt_of_le b (by exact_mod_cast v2)⟩

/-- This also excludes negative integer labels from the octave, so counting
only natural labels is sufficient under the displayed budget. -/
theorem positive_of_near {n X J r : ℕ} {A : ℝ} (r1 : 1≤r) (lower : (X:ℝ)≤Real.sqrt n)
    (budget : 24*J<2*X) (near : |A-2*Real.sqrt r*Real.sqrt n|≤(J:ℝ)*stride r n) : 0<A := by
  have sc : (1:ℝ)≤Real.sqrt r := Real.le_sqrt_of_sq_le (by norm_num; exact_mod_cast r1)
  have z := mul_le_mul sc lower (Nat.cast_nonneg X) (Real.sqrt_nonneg _)
  have bound : (J:ℝ)*stride r n≤24*J := by
    have := mul_le_mul_of_nonneg_left (show (stride r n:ℝ)≤24 by exact_mod_cast stride_le r n) (Nat.cast_nonneg J)
    linarith only [this]
  have budget' : 24*(J:ℝ)<2*X := by exact_mod_cast budget
  linarith only [budget',z,(abs_le.mp near).1,bound]

theorem actual_positive {n X J r A : ℕ} (r1 : 1≤r) (lower : (X:ℝ)≤Real.sqrt n)
    (budget : 24*J<2*X) (act : Actual n J r A) : 0<A := by
  exact_mod_cast positive_of_near r1 lower budget act.2

/-- Either orientation of the first `J` labels is covered. Here `B` is the
adjacent congruent label on that side. The closed first-step bound allows the
convention that a label exactly at the endpoint belongs to either side. -/
theorem actual_from_rank {n r A B i J : ℕ} (rank : i<J)
    (res : B≡r+n [MOD stride r n]) (first : |(B:ℝ)-2*Real.sqrt r*Real.sqrt n|≤stride r n)
    (side : A=B+i*stride r n ∨ B=A+i*stride r n) : Actual n J r A := by
  let s := stride r n
  have room : (s:ℝ)+(i:ℝ)*s ≤ (J:ℝ)*s := by
    have step := Nat.mul_le_mul_right s (show i+1≤J by omega)
    simpa [add_mul,add_comm] using (show ((i+1:ℕ):ℝ)*s≤(J:ℝ)*s by exact_mod_cast step)
  have off : i*s≡0 [MOD s] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left s i)
  rcases side with eq|eq
  · have cong : A≡B [MOD s] := by rw [eq]; simpa only [add_zero] using off.add_left B
    refine ⟨cong.trans res,?_⟩
    have eqr : (A:ℝ)=B+(i:ℝ)*s := by exact_mod_cast eq
    apply abs_le.mpr
    constructor <;> linarith only [eqr,(abs_le.mp first).1,(abs_le.mp first).2,room,
      show 0≤(i:ℝ)*s by positivity]
  · have cong : B≡A [MOD s] := by rw [eq]; simpa only [add_zero] using off.add_left A
    refine ⟨cong.symm.trans res,?_⟩
    have eqr : (B:ℝ)=A+(i:ℝ)*s := by exact_mod_cast eq
    apply abs_le.mpr
    constructor <;> linarith only [eqr,(abs_le.mp first).1,(abs_le.mp first).2,room,
      show 0≤(i:ℝ)*s by positivity]

/-- Parameters computed using the integer square root in the finite table. -/
def rootCap (K : ℕ) := 1+(K-1).sqrt

def cellWidth (K J : ℕ) := max 1 (J/rootCap K)

theorem rootCap_sq (K : ℕ) : K≤rootCap K^2 := by
  have hi := Nat.lt_succ_sqrt' (K-1)
  simp only [Nat.succ_eq_add_one] at hi
  dsimp [rootCap]
  rw [add_comm]
  omega

theorem cellWidth_pos (K J : ℕ) : 0<cellWidth K J := by
  exact le_max_left 1 _

noncomputable def residues : Finset ℕ := {1,5,7,11,13,17,19,23}

theorem unit_residue {n : ℕ} (unit : n.Coprime 24) : n%24∈residues := by
  have cap := Nat.mod_lt n (by decide : 0<24)
  have hc : (n%24).Coprime 24 := by
    change (n%24).gcd 24=1
    rw [←Nat.gcd_rec 24 n,Nat.gcd_comm]
    exact unit
  have table : ∀ a : Fin 24, a.val.Coprime 24 → a.val∈residues := by decide +kernel
  exact table ⟨n%24,cap⟩ hc

/-- One input's complete menu is contained in a single fixed catalogue. Its
anchor may be chosen after the input is known. -/
theorem common_catalogue {n X K J : ℕ} (unit : n.Coprime 24)
    (lower : X≤n.sqrt) (upper : n.sqrt<2*X) :
    let w := cellWidth K J
    ∃ ρ∈residues, ∃ i<cellCount X w, X+i*w<2*X ∧
      ∀ r A, 1≤r → r≤K → Actual n J r A → (r,A)∈catalogue ρ (X+i*w) w J K := by
  let w := cellWidth K J
  let i := (n.sqrt-X)/w
  obtain ⟨hi,top,lo,up⟩ := locate (cellWidth_pos K J) lower upper
  refine ⟨n%24,unit_residue unit,i,hi,top,?_⟩
  intro r A r1 rk hh
  exact mem_catalogue.mpr ⟨r1,rk,mem_labels.mp (actual_mem (by simp [Nat.ModEq]) lo up.le hh)⟩

/-- All fixed determinants used by an input menu also divide the chosen
catalogue's support integer. -/
theorem determinant_dvd_support {S : Finset (ℕ×ℕ)} {i j : ℕ×ℕ}
    (mem : j∈S) (ne : j≠i) (nonzero : 0<determinant i j) : determinant i j∣support S i := by
  have h := Finset.dvd_prod_of_mem (fun k => max 1 (determinant i k)) (mem_erase.mpr ⟨ne,mem⟩)
  simpa only [max_eq_right (show 1≤determinant i j from nonzero),support] using h

/-- The support bit budget may round `C` upward to an integer power of two. -/
theorem support_bits {ρ v w J K X h bits : ℕ} {i : ℕ×ℕ} (cap : K≤h^2) (top : v≤2*X)
    (pos : 0<determinantBound X h K w J) (bound : determinantBound X h K w J≤2^bits)
    (hi : i∈catalogue ρ v w J K) :
    support (catalogue ρ v w J K) i ≤ 2^((catalogueCap ρ w J K-1)*bits) := by
  have hh := (support_le cap top pos hi).trans (Nat.pow_le_pow_left bound _)
  simpa only [←pow_mul,Nat.mul_comm bits] using hh

/-- Three sample row counts from the sixteen-weight budget. -/
theorem sample_row_counts :
    (cellWidth 16 16, rowCap 1 4 16 1, rowCap 1 4 16 5, rowCap 1 4 16 16) = (4,35,34,49) := by
  decide +kernel

end PrimeFactors.WeightedGrowingCells
