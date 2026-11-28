import PrimeFactors.DyadicClueSquareBranch
import PrimeFactors.DyadicCluePersistentClass
import PrimeFactors.DyadicClueScanControls
import Mathlib.Data.Fintype.Parity

/-! The smallest dyadic modulus of a full sum progression surviving at all
precisions for a supplied singular factor suffix. -/
namespace PrimeFactors.SharpDyadicCluePeriod

open DyadicClueSquareBranch DyadicClueFullSumClass

private theorem three_offsets : ∀ c h : ZMod 16, ∃ i : Fin 3,
    ¬IsSquare ((2*c+1)*(h+4*(i.val:ZMod 16))) := by decide +kernel

private theorem restrict {k e f : ℕ} {N a s : ℤ} (le : e≤f) (pass : AtLevel k f N a s) :
    AtLevel k e N a s := by
  obtain ⟨x,same,prod⟩ := pass
  exact ⟨x,same,prod.of_dvd (pow_dvd_pow (2:ℤ) le)⟩

/-- Among the first three consecutive members starting at b in any class
modulo 2^(2k+2), at least one fails the test at depth 2k+4. -/
theorem first_three {k N a : ℕ} (hk : 3≤k) (odd : Odd N)
    (hit : a∈SingularDyadicClueSuffixes.menu k N) (b : ℕ) :
    ∃ i : Fin 3, ¬AtLevel k (2*k+4) N a ((b+i.val*2^(2*k+2) : ℕ):ℤ) := by
  obtain ⟨r,ro,same,root⟩ := SingularDyadicClueSuffixes.lift hk odd hit (2*k+4)
  by_cases centered : (b:ℤ) ≡ 2*r [ZMOD (2:ℤ)^(2*k)]
  · obtain ⟨h,eq⟩ := Int.modEq_iff_dvd.mp centered.symm
    obtain ⟨c,hc⟩ := ro
    obtain ⟨i,miss⟩ := three_offsets c h
    refine ⟨i, fun pass => miss ?_⟩
    have exp : ((b+i.val*2^(2*k+2) : ℕ):ℤ) = 2*r+2^(2*k)*(h+4*i.val) := by
      push_cast
      rw [pow_add (2:ℤ) (2*k) 2]
      linear_combination eq
    rw [exp] at pass
    have sq := (square_branch hk (j:=4) (show Odd r from ⟨c,hc⟩) same root (h+4*i.val)).mp pass
    rw [hc] at sq
    push_cast at sq
    exact sq
  · refine ⟨0,fun pass => centered ?_⟩
    apply center_necessary (by omega) ro same root
    simpa only [Fin.val_zero,Nat.zero_mul,Nat.add_zero] using pass

/-- This obstruction persists at all greater depths, including 2k+5, and
on any proposed congruence class of exponent at most 2k+2. -/
theorem failing_lift {k N a : ℕ} (hk : 3≤k) (odd : Odd N)
    (hit : a∈SingularDyadicClueSuffixes.menu k N) (b : ℕ) {d e : ℕ}
    (width : d≤2*k+2) (depth : 2*k+4≤e) :
    ∃ s : ℕ, b≤s ∧ s ≡ b [MOD 2^d] ∧ ¬AtLevel k e N a (s:ℤ) := by
  obtain ⟨i,miss⟩ := first_three hk odd hit b
  refine ⟨_,Nat.le_add_right b _,?_,fun pass => miss (restrict depth pass)⟩
  have dv : (2:ℕ)^d∣i.val*2^(2*k+2) := dvd_mul_of_dvd_right (pow_dvd_pow 2 width) _
  simpa only [Nat.add_zero] using (Nat.modEq_zero_iff_dvd.mpr dv).add_left b

/-- One bit earlier, at depth 2k+3, an entire class modulo 2^(2k+2)
still passes. Thus 2k+4 is the first depth rejecting a lift in every class. -/
theorem previous_depth {k N a : ℕ} (hk : 3≤k) (odd : Odd N)
    (hit : a∈SingularDyadicClueSuffixes.menu k N) :
    ∃ b : ℕ, ∀ s : ℕ, s ≡ b [MOD 2^(2*k+2)] → AtLevel k (2*k+3) N a (s:ℤ) := by
  obtain ⟨r,ro,same,root⟩ := SingularDyadicClueSuffixes.lift hk odd hit (2*k+3)
  let M : ℤ := 2^(2*k+2)
  let b := ((2*r)%M).toNat
  have base : (b:ℤ) ≡ 2*r [ZMOD M] := by
    rw [show (b:ℤ)=(2*r)%M from Int.toNat_of_nonneg (Int.emod_nonneg _ (by dsimp [M]; positivity))]
    exact Int.mod_modEq ..
  refine ⟨b,fun s hs => ?_⟩
  have cast : (s:ℤ) ≡ (b:ℤ) [ZMOD (2:ℤ)^(2*k+2)] := by exact_mod_cast Int.natCast_modEq_iff.mpr hs
  obtain ⟨u,eq⟩ := Int.modEq_iff_dvd.mp (cast.trans base).symm
  have shape : (s:ℤ)=2*r+2^(2*k)*(4*u) := by
    rw [pow_add (2:ℤ) (2*k) 2] at eq
    linear_combination eq
  rw [shape,square_branch hk ro same root]
  have small : ∀ z : ZMod 8, IsSquare (4*z) := by decide +kernel
  push_cast
  simpa only [mul_left_comm (r:ZMod 8)] using small ((r:ZMod 8)*u)

/-- The supplied singular suffix admits a full persistent class of modulus
2^d precisely for exponents d≥2k+3. The class may depend on the suffix. -/
theorem persistent_iff {k N a : ℕ} (hk : 3≤k) (odd : Odd N)
    (hit : a∈SingularDyadicClueSuffixes.menu k N) (d : ℕ) :
    (∃ b : ℕ, ∀ s : ℕ, s ≡ b [MOD 2^d] → Possible k N a s) ↔ 2*k+3≤d := by
  constructor
  · rintro ⟨b,all⟩
    by_contra! less
    obtain ⟨s,_,same,miss⟩ := failing_lift hk odd hit b (by omega : d≤2*k+2) (Nat.le_refl _)
    exact miss ((all s same) (2*k+4))
  · intro width
    obtain ⟨r,⟨c,hc⟩,same,_⟩ := SingularDyadicClueSuffixes.lift hk odd hit 1
    have both := same.of_dvd (dvd_pow_self (2:ℤ) (by omega : k≠0))
    change r%2=(a:ℤ)%2 at both
    have ao : Odd a := Nat.odd_iff.mpr (by omega)
    obtain ⟨b,all⟩ := DyadicCluePersistentClass.exists_class hk odd ao (SingularDyadicClueSuffixes.mem_menu.mp hit).1
    exact ⟨b,fun s hs => all s (hs.of_dvd (pow_dvd_pow 2 width))⟩

/-- In the earlier-sum window of the 30-bit singular control, the first
two members of this progression pass at ten bits and the third fails. -/
theorem three_needed : AtLevel 3 10 DyadicClueScanControls.squareN 1 50178 ∧
    AtLevel 3 10 DyadicClueScanControls.squareN 1 50434 ∧
    ¬AtLevel 3 10 DyadicClueScanControls.squareN 1 50690 := by
  have test (h : ℤ) : AtLevel 3 10 DyadicClueScanControls.squareN 1 (2+64*h) ↔ IsSquare (h:ZMod 16) := by
    have root : (1:ℤ)^2 ≡ (DyadicClueScanControls.squareN:ℤ) [ZMOD 2^(2*3+4)] := by decide +kernel
    simpa only [one_mul] using square_branch (k:=3) (j:=4) (by decide) (by decide : Odd (1:ℤ))
      (Int.ModEq.refl 1) root h
  change AtLevel _ _ _ _ (2+64*784) ∧ AtLevel _ _ _ _ (2+64*788) ∧ ¬AtLevel _ _ _ _ (2+64*792)
  rw [test,test,test]
  decide +kernel

end PrimeFactors.SharpDyadicCluePeriod
