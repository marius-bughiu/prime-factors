import PrimeFactors.FactorClueSumPrecision
import Mathlib.Data.Int.CardIntervalMod

/-! Distribution of forced sum precision for a fixed supplied odd factor
class and a product uniformly distributed among odd residues modulo 2^(k+1). -/
namespace PrimeFactors.DyadicFactorClueGain

open Finset FactorClueSumPrecision

private theorem cap_pow {k : ℕ} (hk : 1 ≤ k) : cap (2^k) = 2^(k+(k+1)) := by
  have even : 2 ∣ (2:ℕ)^k := by simpa using pow_dvd_pow 2 hk
  rw [cap,if_pos even,pow_add, pow_succ 2 k]
  ring

private theorem gcd_iff (x : ℤ) (c d : ℕ) : d ∣ Int.gcd x c ↔ (d:ℤ)∣x ∧ d∣c := by
  constructor
  · intro div
    have hz := Int.natCast_dvd_natCast.mpr div
    exact ⟨hz.trans Int.gcd_dvd_left,Int.natCast_dvd_natCast.mp (hz.trans Int.gcd_dvd_right)⟩
  · rintro ⟨l,r⟩
    exact Int.natCast_dvd_natCast.mp (Int.dvd_coe_gcd l (Int.natCast_dvd_natCast.mpr r))

/-- At level j, exactly one class of products gives the extra j bits, up to
the fixed cap. The formula is valid for arbitrary factor and product representatives. -/
theorem precision_iff {k : ℕ} (hk : 1 ≤ k) (a N j : ℕ) :
    2^(k+j) ∣ greatest N a (2^k) ↔ j≤k+1 ∧ N ≡ a^2+a*2^k [MOD 2^j] := by
  rw [greatest,gcd_iff,cap_pow hk,Nat.pow_dvd_pow_iff_le_right (by decide : 1<(2:ℕ)),Nat.add_le_add_iff_left]
  rw [←Int.natCast_modEq_iff,Int.modEq_iff_dvd]
  push_cast
  rw [pow_add,show (a:ℤ)^2-N+a*2^k = (a^2+a*2^k)-N by ring,
    Int.mul_dvd_mul_iff_left (by positivity : (2:ℤ)^k ≠ 0),and_comm]

/-- Number of additional forced low bits beyond the k supplied factor bits. -/
def extra (k a N : ℕ) : ℕ := Nat.log 2 (greatest N a (2^k)) - k

private theorem exponent {k : ℕ} (hk : 1≤k) (a N : ℕ) :
    ∃ e ≤ k+(k+1), k≤e ∧ greatest N a (2^k)=2^e := by
  have div : greatest N a (2^k) ∣ cap (2^k) := Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right ..)
  rw [cap_pow hk] at div
  obtain ⟨e,le,eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp div
  have base := (precision_iff hk a N 0).mpr ⟨Nat.zero_le _, by simp only [Nat.ModEq,pow_zero,Nat.mod_one]⟩
  rw [Nat.add_zero,eq,Nat.pow_dvd_pow_iff_le_right (by decide : 1<(2:ℕ))] at base
  exact ⟨e,le,base,eq⟩

/-- The exponent statistic recovers the largest forced modulus exactly. -/
theorem greatest_eq {k : ℕ} (hk : 1≤k) (a N : ℕ) : greatest N a (2^k)=2^(k+extra k a N) := by
  obtain ⟨e,_,base,eq⟩ := exponent hk a N
  simp only [extra,eq,Nat.log_pow (by decide : 1<(2:ℕ)),Nat.add_sub_of_le base]

theorem extra_iff {k : ℕ} (hk : 1≤k) (a N j : ℕ) :
    j≤extra k a N ↔ j≤k+1 ∧ N ≡ a^2+a*2^k [MOD 2^j] := by
  rw [←precision_iff hk, greatest_eq hk a N,Nat.pow_dvd_pow_iff_le_right (by decide : 1<(2:ℕ)),Nat.add_le_add_iff_left]

/-- Replacing the product by any representative of the same residue preserves
the gain. -/
theorem extra_product_congr {k N N' : ℕ} (hk : 1≤k) (a : ℕ) (same : N ≡ N' [MOD 2^(k+1)]) :
    extra k a N = extra k a N' := by
  have keep {u v : ℕ} (res : u ≡ v [MOD 2^(k+1)]) : extra k a u ≤ extra k a v := by
    obtain ⟨cap,hit⟩ := (extra_iff hk a u _).mp (Nat.le_refl _)
    exact (extra_iff hk a v _).mpr ⟨cap, (res.of_dvd (pow_dvd_pow 2 cap)).symm.trans hit⟩
  exact Nat.le_antisymm (keep same) (keep same.symm)

/-- Full set of odd product representatives, each counted once. -/
noncomputable def products (k : ℕ) := (range (2^(k+1))).filter fun N => N%2=1

private theorem one_class {e j : ℕ} (le : j≤e) (r : ℕ) :
    ((range (2^e)).filter fun N => N ≡ r [MOD 2^j]).card = 2^(e-j) := by
  rw [←Nat.count_eq_card_filter_range,Nat.count_modEq_card (2^e) (by positivity) r,
    Nat.mod_eq_zero_of_dvd (pow_dvd_pow 2 le),Nat.pow_div le (by decide : 0<(2:ℕ))]
  simp

theorem products_card (k : ℕ) : (products k).card=2^k := by
  simpa only [products,pow_one,Nat.succ_sub_one] using one_class (e:=k+1) (j:=1) (by omega) 1

/-- Exactly 2^(k+1−j) of the 2^k odd products force at least j extra bits. -/
theorem tail {k j a : ℕ} (hk : 1≤k) (ha : Odd a) (hj : 1≤j) (le : j≤k+1) :
    ((products k).filter fun N => j≤extra k a N).card = 2^(k+1-j) := by
  have even : 2 ∣ (2:ℕ)^k := by simpa using pow_dvd_pow 2 hk
  have odd : (a^2+a*2^k)%2=1 := by
    rw [Nat.add_mod,Nat.mul_mod, Nat.mod_eq_zero_of_dvd even, Nat.pow_mod, Nat.odd_iff.mp ha]
  have eq : (products k).filter (fun N => j≤extra k a N) =
      (range (2^(k+1))).filter fun N => N ≡ a^2+a*2^k [MOD 2^j] := by
    ext N
    simp only [products,mem_filter,mem_range,extra_iff hk,le,true_and]
    constructor
    · exact fun h => ⟨h.1.1,h.2⟩
    · rintro ⟨size,same⟩
      have low := same.of_dvd (show 2∣(2:ℕ)^j by simpa using pow_dvd_pow 2 hj)
      exact ⟨⟨size,(show N%2=(a^2+a*2^k)%2 from low).trans odd⟩,same⟩
  rw [eq,one_class le]

/-- The finite uniform probability of a gain of at least j bits is 1/2^(j−1). -/
theorem tail_probability {k j a : ℕ} (hk : 1≤k) (ha : Odd a) (hj : 1≤j) (le : j≤k+1) :
    (((products k).filter fun N => j≤extra k a N).card : ℚ) / (products k).card =
      1/(2:ℚ)^(j-1) := by
  rw [tail hk ha hj le,products_card,Nat.cast_pow,Nat.cast_pow,Nat.cast_ofNat]
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  rw [one_mul,←pow_add,show k+1-j+(j-1)=k by omega]

/-- Exactly one odd residue attains the maximum. -/
theorem maximum_count {k a : ℕ} (hk : 1≤k) (ha : Odd a) :
    ((products k).filter fun N => extra k a N=k+1).card = 1 := by
  have eq : ∀ N, (extra k a N=k+1) ↔ k+1≤extra k a N := by
    intro N
    have cap := ((extra_iff hk a N _).mp (Nat.le_refl _)).1
    omega
  simp_rw [eq]
  simpa using tail hk ha (show 1≤k+1 by omega) (Nat.le_refl _)

/-- Exact total of the extra bit counts across the odd representatives. -/
theorem total {k a : ℕ} (hk : 1≤k) (ha : Odd a) :
    (∑ N ∈ products k, extra k a N) = 2^(k+1)-1 := by
  have byLevel (N : ℕ) : extra k a N = ∑ i ∈ range (k+1), if i+1≤extra k a N then 1 else 0 := by
    rw [sum_boole]
    have cap := ((extra_iff hk a N _).mp (Nat.le_refl _)).1
    have eq : (range (k+1)).filter (fun i => i+1≤extra k a N) = range (extra k a N) := by
      ext i
      simp only [mem_filter,mem_range]
      omega
    rw [eq,card_range,Nat.cast_id]
  calc
    _ = ∑ N ∈ products k, ∑ i ∈ range (k+1), if i+1≤extra k a N then 1 else 0 :=
      sum_congr rfl fun N _ => byLevel N
    _ = ∑ i ∈ range (k+1), ((products k).filter (fun N => i+1≤extra k a N)).card := by
      rw [sum_comm]; simp only [sum_boole,Nat.cast_id]
    _ = ∑ i ∈ range (k+1), 2^(k+1-1-i) := by
      apply sum_congr rfl
      intro i hi
      rw [tail hk ha (by omega) (by simpa only [mem_range] using hi : i+1≤k+1)]
      congr 1; omega
    _ = ∑ i ∈ range (k+1), 2^i := sum_range_reflect (fun i => (2:ℕ)^i) _
    _ = _ := by simpa using geom_sum_mul_of_one_le (by decide : 1≤(2:ℕ)) (k+1)

/-- Mean gain for uniform odd product residues at fixed supplied factor class. -/
theorem mean {k a : ℕ} (hk : 1≤k) (ha : Odd a) :
    ((∑ N ∈ products k, extra k a N : ℕ) : ℚ) / (products k).card = 2-1/(2:ℚ)^k := by
  rw [total hk ha, products_card, Nat.cast_sub (Nat.one_le_two_pow),Nat.cast_one,Nat.cast_pow,Nat.cast_pow]
  norm_num only [Nat.cast_ofNat,pow_succ]
  field_simp
  ring

/-- All odd residues modulo 16 for the supplied factor class 1 modulo 8. -/
theorem example_three : [1,3,5,7,9,11,13,15].map (extra 3 1) = [3,1,2,1,4,1,2,1] := by
  norm_num [extra,greatest,cap,Nat.log]

end PrimeFactors.DyadicFactorClueGain
