import PrimeFactors.WeightedStride

namespace PrimeFactors.ConstantWeightedResidue

/-- A constant value for all possible local units must equal the value at 1. -/
def Constant (m a c : ℕ) : Prop :=
  ∀ r : (ZMod m)ˣ, (a : ZMod m)*r + (c : ZMod m)*↑r⁻¹ = a+c

/-- Multiplication by the unit r gives a quadratic test with no inverses. -/
private theorem constant_iff (m a c : ℕ) : Constant m a c ↔
    ∀ r : (ZMod m)ˣ, ((r : ZMod m)-1)*((a : ZMod m)*r-c)=0 := by
  have id (r : (ZMod m)ˣ) :
      ((a : ZMod m)*r+c*↑r⁻¹-(a+c))*r = ((r : ZMod m)-1)*((a : ZMod m)*r-c) := by
    have inv := Units.inv_mul r
    linear_combination (c : ZMod m)*inv
  constructor
  · intro h r
    rw [← id,h r,sub_self,zero_mul]
  · intro h r
    apply sub_eq_zero.mp
    apply (r.isUnit.mul_left_inj).mp
    rw [id,h r,zero_mul]

private theorem descend {m d a c : ℕ} [NeZero m] (dvd : d ∣ m) (h : Constant m a c) :
    Constant d a c := by
  rw [constant_iff] at h ⊢
  intro r
  obtain ⟨s,rfl⟩ := ZMod.unitsMap_surjective dvd r
  let f := ZMod.castHom dvd (ZMod d)
  have eq := congrArg f (h s)
  change (f (s : ZMod m)-1)*((a : ZMod d)*f (s : ZMod m)-c)=0
  simpa only [map_mul,map_sub,map_one,map_natCast,map_zero] using eq

/-- A single test at −1 is necessary at every modulus. -/
private theorem at_neg_one {m a c : ℕ} (h : Constant m a c) : m ∣ 2*(a+c) := by
  have neg := (constant_iff ..).mp h (-1)
  change ((-1 : ZMod m)-1)*((a : ZMod m)*(-1)-c)=0 at neg
  apply (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp
  push_cast
  linear_combination neg

private theorem odd_part {d a c : ℕ} (odd : Odd d) (prim : (a.gcd c).Coprime d)
    (h : Constant d a c) : d ∣ 3 := by
  let r := ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr odd)
  have plus := (constant_iff ..).mp h r
  change ((2:ZMod d)-1)*((a:ZMod d)*2-c)=0 at plus
  have neg := (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mpr (at_neg_one h)
  push_cast at neg
  have da : d ∣ 6*a := (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp (by
    push_cast
    linear_combination neg + 2*plus)
  have dc : d ∣ 6*c := (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp (by
    push_cast
    linear_combination 2*neg - 2*plus)
  have common := Nat.dvd_gcd da dc
  rw [Nat.gcd_mul_left] at common
  exact (Nat.coprime_two_right.mpr odd).dvd_of_dvd_mul_left
    (show d ∣ 2*3 from prim.symm.dvd_of_dvd_mul_right common)

private theorem not_sixteen {a c : ℕ} (prim : (a.gcd c).Coprime 16) (h : Constant 16 a c) : False := by
  have plus := (constant_iff ..).mp h (ZMod.unitOfCoprime 3 (by decide))
  change ((3:ZMod 16)-1)*((a:ZMod 16)*3-c)=0 at plus
  have neg := (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mpr (at_neg_one h)
  push_cast at neg
  have even_a : 2 ∣ a := (Nat.mul_dvd_mul_iff_left (by decide : 0 < 8)).mp
    ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp (by
      push_cast
      linear_combination neg + plus) : 16 ∣ 8*a)
  have even_c : 2 ∣ c := (Nat.mul_dvd_mul_iff_left (by decide : 0 < 8)).mp
    ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp (by
      push_cast
      linear_combination 3*neg - plus) : 16 ∣ 8*c)
  exact (by decide : ¬ 2 ∣ 1) (prim.gcd_eq_one ▸ Nat.dvd_gcd (Nat.dvd_gcd even_a even_c) (by decide : 2 ∣ 16))

private theorem divides_twenty_four {m a c : ℕ} [NeZero m] (prim : (a.gcd c).Coprime m)
    (h : Constant m a c) : m ∣ 24 := by
  obtain ⟨k,d,odd,eq⟩ := Nat.exists_eq_two_pow_mul_odd (NeZero.ne m)
  have two_div : 2^k ∣ m := eq ▸ dvd_mul_right _ _
  have d_div : d ∣ m := eq ▸ dvd_mul_left _ _
  have d3 := odd_part odd (prim.of_dvd_right d_div) (descend d_div h)
  have k3 : k ≤ 3 := by
    by_contra! high
    have d16 := (Nat.pow_dvd_pow 2 (show 4 ≤ k from high)).trans two_div
    exact not_sixteen (prim.of_dvd_right d16) (descend d16 h)
  rw [eq]
  exact Nat.mul_dvd_mul (show 2^k ∣ 2^3 from Nat.pow_dvd_pow _ k3) d3

private theorem sufficient {m a c : ℕ} (d24 : m ∣ 24) (sum : m ∣ 2*(a+c)) :
    Constant m a c := by
  rw [constant_iff]
  intro r
  obtain ⟨s,rfl⟩ := ZMod.unitsMap_surjective d24 r
  let k := (s : ZMod 24).val
  have k6 : k.Coprime 6 := (ZMod.val_coe_unit_coprime s).of_dvd_right (by decide)
  have mapped : (ZMod.unitsMap d24 s : ZMod m) = (k : ZMod m) := by
    let f := ZMod.castHom d24 (ZMod m)
    change f (s : ZMod 24) = (k : ZMod m)
    rw [← ZMod.natCast_zmod_val (s : ZMod 24),map_natCast]
  have sq : (k : ZMod m)^2=1 := by
    exact_mod_cast (ZMod.eq_iff_modEq_nat m).2 ((square_mod_twentyfour k6).of_dvd d24)
  have zero := (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mpr sum
  push_cast at zero
  obtain ⟨j,hj⟩ := Nat.coprime_two_right.mp (k6.of_dvd_right (by decide : 2∣6))
  have repr : (k : ZMod m) = 2*j+1 := by rw [hj]; push_cast; rfl
  rw [mapped]
  calc
    _ = (a : ZMod m)*(k^2-1)-(a+c)*(k-1) := by ring
    _ = 0 := by rw [sq,repr]; linear_combination -(j:ZMod m)*zero

/-- Complete classification for local unit residues with m prime to gcd(a,c).
The weighted trace has a single value at every unit exactly at these moduli. -/
theorem classify {m a c : ℕ} [NeZero m] (prim : (a.gcd c).Coprime m) :
    Constant m a c ↔ m ∣ Nat.gcd 24 (2*(a+c)) := by
  exact ⟨fun h => Nat.dvd_gcd (divides_twenty_four prim h) (at_neg_one h),
    fun h => sufficient (h.trans (Nat.gcd_dvd_left ..)) (h.trans (Nat.gcd_dvd_right ..))⟩

/-- Specializing c=bN proves maximality of the weighted search stride for primitive
weights and moduli coprime to the input. The possible residues here range over all units. -/
theorem weighted_iff {m n a b : ℕ} [NeZero m] (weights : a.Coprime b) (unit : n.Coprime m) :
    (∃ t : ZMod m, ∀ r : (ZMod m)ˣ,
      (a : ZMod m)*r + ((b*n : ℕ) : ZMod m)*↑r⁻¹ = t) ↔ m ∣ weightedStride n a b := by
  have primitive : (a.gcd (b*n)).Coprime m := by
    rw [Nat.gcd_comm, Nat.Coprime.gcd_mul_left_cancel n weights.symm]
    exact unit.of_dvd_left (Nat.gcd_dvd_left ..)
  change _ ↔ m ∣ Nat.gcd 24 (2*(a+b*n))
  rw [← classify primitive]
  constructor
  · rintro ⟨t,h⟩
    have value := h 1
    simp only [Units.val_one,inv_one,mul_one] at value
    exact fun r => (h r).trans value.symm
  · intro h
    exact ⟨_,h⟩

end PrimeFactors.ConstantWeightedResidue
