import PrimeFactors.DyadicClueSquareBranch
import PrimeFactors.Fermat
import PrimeFactors.Certificate
import Mathlib.Data.Fintype.Parity

/-! Two 30-bit semiprimes with the same low 14 product bits. Each scan
starts at the ceiling of twice the square root and excludes the true sum. -/
namespace PrimeFactors.DyadicClueScanControls

open Finset DyadicClueSquareBranch DyadicClueFullSumClass

abbrev squareN : ℕ := 623706113
abbrev regularN : ℕ := 623493121

/-- The factorizations verify the supplied smaller-factor suffixes independently. -/
theorem certificates : ExactFactorization squareN [20873,29881] ∧
    ExactFactorization regularN [20347,30643] := by
  norm_num [ExactFactorization]

theorem matched : 2^29≤squareN ∧ squareN<2^30 ∧ 2^29≤regularN ∧ regularN<2^30 ∧
    2^14≤20873 ∧ 20873<29881 ∧ 29881<2^15 ∧ 2^14≤20347 ∧ 20347<30643 ∧ 30643<2^15 ∧
    squareN%2^14=1 ∧ regularN%2^14=1 ∧ 20873%8=1 ∧ 20347%8=3 ∧
    20873+29881=50754 ∧ 20347+30643=50990 := by decide +kernel

private theorem ceiling {n a : ℕ} (hi : n≤a^2) (lo : (a-1)^2<n) : ceilSqrt n=a := by
  apply le_antisymm (ceilSqrt_le_iff.mpr hi)
  by_contra! lt
  have bad := ceilSqrt_le_iff.mp (show ceilSqrt n≤a-1 by omega)
  omega

theorem ends : ceilSqrt (4*squareN)=49949 ∧ ceilSqrt (4*regularN)=49940 := by
  constructor <;> apply ceiling <;> decide +kernel

noncomputable def squareWindow : Finset ℕ := Ico (ceilSqrt (4*squareN)) (20873+29881)
noncomputable def regularWindow : Finset ℕ := Ico (ceilSqrt (4*regularN)) (20347+30643)

noncomputable def coarseSquare := squareWindow.filter (fun s => s%64=2)

noncomputable def refinedSquare : Finset ℕ := by
  classical
  exact squareWindow.filter (fun s => AtLevel 3 14 squareN 1 (s:ℤ))

noncomputable def refinedRegular : Finset ℕ := by
  classical
  exact regularWindow.filter (fun s => Possible 3 regularN 3 (s:ℤ))

/-- On the singular control, the 14-bit test is equivalent to the low six
sum bits and a square test on the remaining index modulo 256. -/
theorem square_test (s : ℕ) : AtLevel 3 14 squareN 1 (s:ℤ) ↔
    s%64=2 ∧ IsSquare ((s/64:ℕ):ZMod 256) := by
  have root : (1:ℤ)^2 ≡ (squareN:ℤ) [ZMOD 2^(2*3+8)] := by decide +kernel
  have onClass (eq : s%64=2) : AtLevel 3 14 squareN 1 (s:ℤ) ↔ IsSquare ((s/64:ℕ):ZMod 256) := by
    have val : 2+64*(s/64)=s := eq ▸ Nat.mod_add_div s 64
    have vz : 2+64*((s/64:ℕ):ℤ)=(s:ℤ) := by exact_mod_cast val
    have branch := square_branch (k:=3) (j:=8) (by decide) (by decide : Odd (1:ℤ))
      (Int.ModEq.refl 1) root ((s/64:ℕ):ℤ)
    simp only [one_mul,Int.cast_natCast] at branch
    change AtLevel 3 14 squareN 1 (2+64*((s/64:ℕ):ℤ)) ↔ IsSquare ((s/64:ℕ):ZMod 256) at branch
    rwa [vz] at branch
  constructor
  · intro hit
    have cut := center_necessary (k:=3) (j:=8) (by decide) (by decide : Odd (1:ℤ))
      (Int.ModEq.refl 1) root hit
    have eq : s≡2 [MOD 64] := Int.natCast_modEq_iff.mp (by simpa only [mul_one] using cut)
    exact ⟨eq,(onClass eq).mp hit⟩
  · rintro ⟨eq,sq⟩
    exact (onClass eq).mpr sq

private theorem coarse_set : coarseSquare =
    {49986,50050,50114,50178,50242,50306,50370,50434,50498,50562,50626,50690} := by
  rw [coarseSquare,squareWindow,ends.1]
  decide +kernel

theorem square_counts : coarseSquare.card=12 ∧ refinedSquare={50178,50242} ∧ refinedSquare.card=2 := by
  have split : refinedSquare = coarseSquare.filter (fun s => IsSquare ((s/64:ℕ):ZMod 256)) := by
    ext s
    simp only [refinedSquare,coarseSquare,mem_filter,square_test,and_assoc]
  have result : refinedSquare={50178,50242} := by
    rw [split,coarse_set]
    decide +kernel
  rw [coarse_set,result]
  decide +kernel

/-- On the regular control the congruence modulo 128 remains sufficient
for every finite precision, however many additional bits are tested. -/
theorem regular_test (s : ℤ) : Possible 3 regularN 3 s ↔ s ≡ 46 [ZMOD 128] := by
  have all := full_class (k:=3) (t:=3) (a:=3) (N:=regularN) (s:=s) (g:=-77936639)
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
  change Possible 3 regularN 3 s ↔ 3*s ≡ 3^2+(regularN:ℤ) [ZMOD 128] at all
  rw [all]
  have at46 : (3:ℤ)*46 ≡ 3^2+(regularN:ℤ) [ZMOD 128] := by decide +kernel
  have inv : (43:ℤ)*3 ≡ 1 [ZMOD 128] := by decide
  have cancel (z : ℤ) : 43*(3*z) ≡ z [ZMOD 128] := by simpa only [←mul_assoc,one_mul] using inv.mul_right z
  exact ⟨fun h => (cancel s).symm.trans (((h.trans at46.symm).mul_left 43).trans (cancel 46)),
    fun h => (h.mul_left 3).trans at46⟩

theorem regular_count : refinedRegular={49966,50094,50222,50350,50478,50606,50734,50862} ∧
    refinedRegular.card=8 := by
  have split : refinedRegular = regularWindow.filter (fun s => s%128=46) := by
    ext s
    simp only [refinedRegular,mem_filter,regular_test]
    exact and_congr_right fun _ => (Int.natCast_modEq_iff (a:=s) (b:=46) (n:=128))
  have result : refinedRegular={49966,50094,50222,50350,50478,50606,50734,50862} := by
    rw [split,regularWindow,ends.2]
    decide +kernel
  rw [result]
  decide +kernel

end PrimeFactors.DyadicClueScanControls
