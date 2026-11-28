import PrimeFactors.TransposedRadixProducts
import Mathlib.Data.Nat.GCD.Basic

/-! Two different binary block widths cannot transpose the same two distinct
positive numbers of equal bit length. The proof compares the least common
multiple of the two required gap divisors with the entire width interval. -/

namespace PrimeFactors.BinaryTransposeUniqueness

open TransposedRadixProducts

def Represents (k p q : ℕ) : Prop :=
  ∃ a b, Valid (2^k) a b ∧ (p,q)=factors (2^k) a b

/-- For two different block widths, the lcm of their Mersenne numbers
is at least the smaller Mersenne number times its radix. -/
theorem lcm_lower {k l : ℕ} (kp : 0<k) (kl : k<l) :
    (2^k-1)*2^k≤Nat.lcm (2^k-1) (2^l-1) := by
  let g := k.gcd l
  have gd : g∣l-k := Nat.dvd_sub (Nat.gcd_dvd_right ..) (Nat.gcd_dvd_left ..)
  have gs : g≤l-k := Nat.le_of_dvd (by omega) gd
  have power : (2:ℕ)^g≤2^(l-k) := Nat.pow_le_pow_right (by decide) gs
  have pos : 0<(2:ℕ)^g := by positivity
  have shape : 2^(l-k)*2^k=(2:ℕ)^l := by rw [←pow_add,Nat.sub_add_cancel kl.le]
  have pk : 0<(2:ℕ)^k := by positivity
  have left : (2^g-1)*2^k≤2^l-1 := by
    have h := Nat.mul_le_mul_right ((2:ℕ)^k) power
    rw [shape] at h
    rw [Nat.sub_mul,Nat.one_mul]
    omega
  have gp : 0<g := Nat.gcd_pos_of_pos_left l kp
  have gbig : (1:ℕ)<2^g := one_lt_pow₀ (by decide) (by omega)
  have small : 0<((2^k-1).gcd (2^l-1)) := by
    rw [Nat.pow_sub_one_gcd_pow_sub_one]
    exact Nat.sub_pos_of_lt gbig
  apply Nat.le_of_mul_le_mul_left (c:=(2^k-1).gcd (2^l-1)) _ small
  rw [Nat.gcd_mul_lcm,Nat.pow_sub_one_gcd_pow_sub_one]
  calc
    _ = (2^k-1)*((2^g-1)*2^k) := by dsimp [g]; ac_rfl
    _ ≤ _ := Nat.mul_le_mul_left _ left

/-- Each binary digit transposition requires a gap divisible by 2^k−1. -/
theorem gap_dvd {k p q : ℕ} (hit : Represents k p q) : (2^k-1)∣q-p := by
  obtain ⟨a,b,ok,eq⟩ := hit
  have hp : p=2^k*a+b := congrArg Prod.fst eq
  have hq : q=2^k*b+a := congrArg Prod.snd eq
  have low := ok.1
  have order := ok.2.2.2.2.1
  have diff : q=p+(2^k-1)*(b-a) := by
    rw [hp,hq]
    zify [show 1≤2^k by omega,order.le]
    ring
  exact ⟨b-a,by omega⟩

theorem half_width {w k p q : ℕ} (low : 2^(w-1)≤p) (hit : Represents k p q) : w≤2*k := by
  obtain ⟨a,b,ok,eq⟩ := hit
  have hp : p=2^k*a+b := congrArg Prod.fst eq
  have ab := ok.2.2.2.2.1
  have top := ok.2.2.2.2.2
  have size : (2:ℕ)^(w-1)<2^(k+k) := calc
    _ ≤ _ := low
    _ = _ := hp
    _ < 2^k*(a+1) := by rw [Nat.mul_add,Nat.mul_one]; omega
    _ ≤ _ := by rw [pow_add]; exact Nat.mul_le_mul_left _ (by omega)
  have := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp size
  omega

private theorem exclusion {w k l p q : ℕ} (kl : k<l) (low : 2^(w-1)≤p) (high : q<2^w)
    (hk : Represents k p q) (hl : Represents l p q) : False := by
  obtain ⟨a,b,ok,eq⟩ := hk
  have ord := (proper ok).2.1
  rw [←eq] at ord
  change p<q at ord
  have kp : 0<k := by
    have := ok.1
    cases k <;> simp_all
  have wz : 0<w := by cases w <;> simp_all
  have small := half_width low (show Represents k p q from ⟨a,b,ok,eq⟩)
  have boundary : (2:ℕ)^w=2^(w-1)+2^(w-1) := by
    conv_lhs => rw [show w=(w-1)+1 by omega,pow_succ]
    omega
  have short : q-p<2^(w-1) := by omega
  have exps : w-1≤(k-1)+k := by omega
  have start : (2:ℕ)^(k-1)≤2^k-1 := by
    have t : (2:ℕ)^k=2^(k-1)*2 := by
      conv_lhs => rw [show k=(k-1)+1 by omega,pow_succ]
    have u : 0<(2:ℕ)^(k-1) := by positivity
    omega
  have long : (2:ℕ)^(w-1)≤(2^k-1).lcm (2^l-1) := calc
    _ ≤ 2^((k-1)+k) := Nat.pow_le_pow_right (by decide) exps
    _ ≤ (2^k-1)*2^k := by rw [pow_add]; exact Nat.mul_le_mul_right _ start
    _ ≤ _ := lcm_lower kp kl
  have gap := Nat.lcm_dvd (gap_dvd (show Represents k p q from ⟨a,b,ok,eq⟩)) (gap_dvd hl)
  exact (not_le_of_gt short) (long.trans (Nat.le_of_dvd (by omega) gap))

/-- Among all binary split positions, a fixed pair of equal-width factors
can be represented at most once. This needs no primality assumption. -/
theorem unique {w p q k l : ℕ} (lower : 2^(w-1)≤p) (upper : q<2^w)
    (hk : Represents k p q) (hl : Represents l p q) : k=l := by
  rcases lt_trichotomy k l with kl|eq|lk
  · exact (exclusion kl lower upper hk hl).elim
  · exact eq
  · exact (exclusion lk lower upper hl hk).elim

end PrimeFactors.BinaryTransposeUniqueness
