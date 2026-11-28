import PrimeFactors.CircleMarkPrimitiveDensity
import PrimeFactors.CircleMarkRationalDisk
import PrimeFactors.CircleMarkDiskStaircase
import PrimeFactors.CircleMarkPublicGridRate

/-! The public fourth-root square hits more than nine tenths of negative-Jacobi
targets for each balanced product of two ordered 1024-bit primes. The proof
counts a clipped quarter disk inside the square, scaled using the larger prime. -/
namespace PrimeFactors.CircleMarkPublicDiskRate

open Finset CircleMarkTargetFrequency CircleMarkRationalFrequency CircleMarkPublicGridRate
open CircleMarkPrimitiveDensity CircleMarkDiskStaircase

/-- Integer scale of the staircase for a disk with squared radius below q. -/
abbrev scale (q : ℕ) := (q-1).sqrt/125

private theorem radius (q : ℕ) :
    (125*scale q)^2 ≤ q-1 ∧ q-1 < (125*(scale q+1))^2 := by
  have lo : 125*scale q ≤ (q-1).sqrt := by
    simpa only [Nat.mul_comm 125] using Nat.div_mul_le_self (q-1).sqrt 125
  have hi : (q-1).sqrt < 125*(scale q+1) := by
    simpa only [Nat.mul_comm 125] using
      (Nat.div_lt_iff_lt_mul (by decide : 0<125)).mp (Nat.lt_succ_self (scale q))
  exact ⟨(Nat.pow_le_pow_left lo 2).trans (Nat.sqrt_le' _),
    (Nat.lt_succ_sqrt' _).trans_le (Nat.pow_le_pow_left hi 2)⟩

private theorem fits {p q : ℕ} (order : p<q) (balance : q<2*p) (large : 2000≤side p q) :
    105*scale q ≤ side p q := by
  have disk := disk_room order balance large
  have rad := (radius q).1.trans (Nat.sub_le q 1)
  have squared : (25*(105*scale q))^2 < (25*side p q)^2 := by
    nlinarith only [disk, Nat.mul_le_mul_left (21^2) rad]
  have lt := Nat.mul_self_lt_mul_self_iff.mp (by simpa only [sq] using squared)
  omega

/-- The staircase already contains more than two fifths of q−1 as
distinct primitive pairs once its integer scale reaches ten million. -/
theorem staircase_count {q : ℕ} (large : 10^7 ≤ scale q) :
    2*(q-1) < 5*((region (scale q)).filter (fun z => z.1.Coprime z.2)).card := by
  let m := scale q
  change 10^7 ≤ m at large
  have lower := region_lower (inside m) (K:=160) (by decide) (by omega)
    (fun d hd => discrepancy (m:=m) (d:=d) (mem_Icc.mp hd).1)
  push_cast at lower
  have mlo : (10000000:ℚ) ≤ m := by exact_mod_cast large
  have mm : (0:ℚ) < m := by linarith
  have scale2 := mul_le_mul_of_nonneg_right mlo mm.le
  have c := mul_lt_mul_of_pos_right coefficient_160 (show 0 < 10394*(m:ℚ)^2 by positivity)
  have qcap : ((q-1:ℕ):ℚ) < (125*((m:ℚ)+1))^2 := by exact_mod_cast (radius q).2
  exact_mod_cast (show 2*((q-1:ℕ):ℚ) < 5*(((region m).filter (fun z => z.1.Coprime z.2)).card:ℚ) by
    nlinarith only [qcap,lower,scale2,c,mlo])

/-- The public menu depends only on the product. The staircase inside it
provides the contribution at the larger prime. -/
theorem nine_tenths_of_scale {p q : ℕ} [Fact p.Prime] [hq : Fact q.Prime]
    (big : 9≤p) (order : p<q) (balance : q<2*p)
    (large : 2000≤side p q) (mlarge : 10^7≤scale q) :
    9/10 < rate (p*q) (menu (p*q) (side p q) (side p q)) := by
  let m := scale q
  have fit := fits order balance large
  have sub : region m ⊆ rectangle (side p q) (side p q) :=
    (inside m).trans (product_subset_product (Icc_subset_Icc_right fit) (Icc_subset_Icc_right fit))
  have shape (z : ℕ×ℕ) (hz : z ∈ region m) : z.1^2+z.2^2 < q :=
    (norm_bound hz).trans_lt (((radius q).1).trans_lt (Nat.sub_lt hq.out.pos (by decide)))
  have coveredCount := CircleMarkRationalDisk.disk_count (n:=p*q) (h:=side p q)
    (dvd_mul_left q p) (region m) sub shape (units big order balance)
  have mass : 2*(q-1) < 5*(covered q (menu (p*q) (side p q) (side p q))).card :=
    (staircase_count mlarge).trans_le (Nat.mul_le_mul_left 5 coveredCount)
  have qpos := hq.out.one_lt
  have pos : (0:ℚ) < (q:ℚ)-1 := sub_pos.mpr (by exact_mod_cast qpos)
  have cast : 2*((q:ℚ)-1) < 5*((covered q (menu (p*q) (side p q) (side p q))).card:ℚ) := by
    rw [←Nat.cast_one (R:=ℚ),←Nat.cast_sub qpos.le]
    exact_mod_cast mass
  rw [rate_split big order balance]
  have contribution : (2:ℚ)/5 < (covered q (menu (p*q) (side p q) (side p q))).card/((q:ℚ)-1) :=
    (lt_div_iff₀ pos).mpr (by linarith only [cast])
  linarith

set_option exponentiation.threshold 8192

/-- Uniform target frequency at every balanced full-width input. -/
theorem nine_tenths {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (lo : 2^1023≤p) (order : p<q) (hi : q<2^1024) :
    9/10 < rate (p*q) (menu (p*q) (side p q) (side p q)) := by
  have balance : q<2*p := hi.trans_le ((by decide +kernel : (2:ℕ)^1024≤2*2^1023).trans
    (Nat.mul_le_mul_left _ lo))
  have large := (full_dimensions lo order hi).1
  apply nine_tenths_of_scale ((by decide +kernel : 9≤2^1023).trans lo) order balance
    ((by decide +kernel : 2000≤2^511).trans large)
  apply (Nat.le_div_iff_mul_le (by decide : 0<125)).mpr
  apply Nat.le_sqrt'.mpr
  exact (by decide +kernel : ((10:ℕ)^7*125)^2≤2^1023).trans (by omega)

end PrimeFactors.CircleMarkPublicDiskRate
