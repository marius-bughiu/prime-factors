import PrimeFactors.LargeBaseOrderPairs
import Mathlib.Data.Nat.Choose.Sum

/-! The large-order pair bound applies to norm-one groups for all four
split/nonsplit choices. Positive integer Cayley parameters give a separate
small-order bound through the coefficients of powers of t + √D. -/
namespace PrimeFactors.SignedLargeOrder
open Finset LargeBaseOrderPairs

private theorem gcd_on_divisor {m P z Q : ℕ} (hm : m ∣ P) (same : P.gcd z = P.gcd Q) :
    m.gcd z = m.gcd Q := by
  calc
    _ = m.gcd (P.gcd z) := by rw [←Nat.gcd_assoc,Nat.gcd_eq_left hm]
    _ = m.gcd (P.gcd Q) := by rw [same]
    _ = _ := by rw [←Nat.gcd_assoc,Nat.gcd_eq_left hm]

/-- The signed projection exponent and the other signed group order have
identical annihilation tests for every divisor of the first group order. -/
theorem signed_dvd_iff {p q m E : ℕ} (hp : 0<p) (hq : 0<q) (s t : Bool)
    (hm : m ∣ signedTorusOrder p s) :
    m ∣ signedTorusOrder (p*q) (s==t)*E ↔ m ∣ signedTorusOrder q t * E := by
  have same := gcd_on_divisor hm (signedTorus_gcd hp hq s t)
  calc
    _ ↔ m ∣ m.gcd (signedTorusOrder (p*q) (s==t))*E := dvd_gcd_mul_iff_dvd_mul.symm
    _ ↔ m ∣ m.gcd (signedTorusOrder q t)*E := by rw [same]
    _ ↔ _ := dvd_gcd_mul_iff_dvd_mul

private theorem residual_dvd {m z E : ℕ} (mp : 0<m) (h : m ∣ z*E) : m / m.gcd E ∣ z := by
  have reduced : m.gcd E * (m/m.gcd E) ∣ m.gcd E*z := by
    rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)]
    exact dvd_gcd_mul_iff_dvd_mul.mpr (by simpa only [mul_comm E z] using h)
  exact Nat.dvd_of_mul_dvd_mul_left (Nat.gcd_pos_of_pos_left _ mp) reduced

theorem residual_dvd_other {p q m E : ℕ} (hp : 0<p) (hq : 0<q) (s t : Bool)
    (mp : 0<m) (hm : m ∣ signedTorusOrder p s)
    (killed : m ∣ signedTorusOrder (p*q) (s==t)*E) :
    m / m.gcd E ∣ signedTorusOrder q t :=
  residual_dvd mp ((signed_dvd_iff hp hq s t hm).mp killed)

/-- Each actual local power hit falls in the original ambient family,
after replacing the two coordinates by the appropriate signed group sizes. -/
theorem signed_hit {p q B T E : ℕ} (hp : 1<p) (hq : 1<q) (s t : Bool)
    (tp : 0<T) {G : Type*} [Group G] (u : G)
    (group_exp : u^signedTorusOrder p s=1) (large : T ≤ orderOf u)
    (smooth : E ∈ Nat.smoothNumbers B)
    (killed : u^(signedTorusOrder (p*q) (s==t)*E)=1) :
    Hit B T (signedTorusOrder p s) (signedTorusOrder q t) := by
  have hm := orderOf_dvd_of_pow_eq_one group_exp
  have pp : 0 < signedTorusOrder p s := by cases s <;> simp [signedTorusOrder]; omega
  apply (hit_iff_smooth_quotient tp pp).mpr
  refine ⟨orderOf u,Nat.mem_divisors.mpr ⟨hm,pp.ne'⟩,large,Nat.mem_smoothNumbers_of_dvd smooth ?_⟩
  have e := (signed_dvd_iff (by omega : 0<p) (by omega : 0<q) s t hm).mp
    (orderOf_dvd_of_pow_eq_one killed)
  exact residual_dvd (tp.trans_le large) (by rwa [mul_comm])

/-- Within the public factor-width interval the pair of signed orders obeys
the same finite population bounds, with either choice of target prime. -/
theorem signed_member {p q U B T E : ℕ} (hp : 1<p) (hq : 1<q) (pu : p<U) (qu : q<U)
    (s t : Bool) (tp : 0<T) {G : Type*} [Group G] (u : G)
    (group_exp : u^signedTorusOrder p s=1) (large : T ≤ orderOf u)
    (smooth : E ∈ Nat.smoothNumbers B)
    (killed : u^(signedTorusOrder (p*q) (s==t)*E)=1) :
    (signedTorusOrder p s,signedTorusOrder q t) ∈ admissible U B T := by
  apply mem_admissible.mpr
  refine ⟨?_,?_,signed_hit hp hq s t tp u group_exp large smooth killed⟩
  · cases s <;> simp [signedTorusOrder] <;> omega
  · cases t <;> simp [signedTorusOrder] <;> omega

/-- Integer coefficients Aᵢ,Bᵢ in (t+√D)^i. -/
def coefficients (t D : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1,0)
  | i+1 =>
    let (a,b) := coefficients t D i
    (t*a+D*b,a+t*b)

theorem expand {R : Type*} [CommRing R] {t D : ℕ} (w : R) (root : w^2 = (D:R)) (i : ℕ) :
    ((t:R)+w)^i = ((coefficients t D i).1:R) + ((coefficients t D i).2:R)*w := by
  induction i with
  | zero => simp [coefficients]
  | succ i ih =>
    rw [pow_succ,ih]
    simp only [coefficients,Nat.cast_add,Nat.cast_mul]
    linear_combination ((coefficients t D i).2 : R)*root

private theorem first_pos {t D : ℕ} (tp : 0<t) (i : ℕ) : 0 < (coefficients t D i).1 := by
  induction i with
  | zero => simp [coefficients]
  | succ i ih =>
    exact (Nat.mul_pos tp ih).trans_le (Nat.le_add_right _ _)

theorem second_pos {t D i : ℕ} (tp : 0<t) (ip : 0 < i) : 0 < (coefficients t D i).2 := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ip.ne'
  exact (first_pos tp n).trans_le (Nat.le_add_right _ _)

/-- Taking L near √D controls the height even when D is much larger than t. -/
theorem coefficient_height {t D L : ℕ} (lp : 0<L) (root_bound : D≤L^2) (i : ℕ) :
    (coefficients t D i).2 ≤ (t+L)^i := by
  have weighted (n : ℕ) : (coefficients t D n).1 + L*(coefficients t D n).2 ≤ (t+L)^n := by
    induction n with
    | zero => simp [coefficients]
    | succ n ih =>
      let a := (coefficients t D n).1
      let b := (coefficients t D n).2
      change t*a+D*b+L*(a+t*b) ≤ (t+L)^(n+1)
      calc
        _ ≤ t*a+L^2*b+L*(a+t*b) := by gcongr
        _ = (t+L)*(a+L*b) := by ring
        _ ≤ _ := by rw [pow_succ']; exact Nat.mul_le_mul_left _ ih
  exact ((Nat.le_mul_of_pos_left _ lp).trans (Nat.le_add_left _ _)).trans (weighted i)

/-- For a good prime, a power of the Cayley ratio equal to one forces the
prime to divide Bᵢ. This covers a root in the base or the quadratic extension. -/
theorem cayley_power_dvd {p t D i : ℕ} {F : Type*} [Field F] [CharP F p] (w : F)
    (root : w^2 = (D:F)) (nz : w≠0) (odd : (2:F)≠0) (den : (t:F)-w≠0)
    (hit : (((t:F)+w)/((t:F)-w))^i=1) : p ∣ (coefficients t D i).2 := by
  rw [div_pow,div_eq_iff (pow_ne_zero _ den),one_mul] at hit
  have left := expand (t:=t) w root i
  have right := expand (t:=t) (-w) (show (-w)^2=(D:F) by simpa using root) i
  rw [left,sub_eq_add_neg,right] at hit
  have zero : ((coefficients t D i).2 : F)*(2*w)=0 := by linear_combination hit
  exact (CharP.cast_eq_zero_iff F p _).mp ((mul_eq_zero.mp zero).resolve_right (mul_ne_zero odd nz))

/-- Every small local order of a valid Cayley unit supplies a witness to the
integer counting theorem, including over a nonsplit quadratic extension. -/
theorem cayley_small_witness {p t D T : ℕ} {F : Type*} [Field F] [Finite F] [CharP F p]
    (w : F) (root : w^2 = (D:F)) (nz : w≠0) (odd : (2:F)≠0) (den : (t:F)-w≠0)
    (u : Fˣ) (value : (u:F) = ((t:F)+w)/((t:F)-w)) (small : orderOf u<T) :
    ∃ i : ℕ, 0 < i ∧ i < T ∧ p ∣ (coefficients t D i).2 := by
  refine ⟨orderOf u,orderOf_pos _,small,cayley_power_dvd w root nz odd den ?_⟩
  rw [←value,←Units.val_pow_eq_pow_val,pow_orderOf_eq_one,Units.val_one]

/-- Among primes at least 2^b, a Cayley ratio of height t+L≤2^A has few
possible orders below T. The given witnesses come from cayley_power_dvd.
Only a product of positive integers enters the count. -/
theorem small_order_count {t D L A b T : ℕ} (tp : 0<t) (lp : 0<L) (root_bound : D≤L^2)
    (height : t+L ≤ 2^A) (P : Finset ℕ) (prime : ∀ p ∈ P, p.Prime)
    (lower : ∀ p ∈ P, 2^b≤p)
    (hit : ∀ p ∈ P, ∃ i : ℕ, 0 < i ∧ i < T ∧ p ∣ (coefficients t D i).2) :
    b*P.card ≤ A*(T.choose 2) := by
  let z := ∏ i ∈ range T, max 1 (coefficients t D i).2
  have pos : 0<z := prod_pos fun i _ => Nat.zero_lt_one.trans_le (le_max_left _ _)
  have sub : P ⊆ z.primeFactors := by
    intro p hp
    obtain ⟨i,ip,small,div⟩ := hit p hp
    apply Nat.mem_primeFactors.mpr ⟨prime p hp,_,pos.ne'⟩
    have share := dvd_prod_of_mem (fun j => max 1 (coefficients t D j).2) (mem_range.mpr small)
    have positive : 1 ≤ (coefficients t D i).2 := second_pos tp ip
    exact div.trans (by simpa only [z,max_eq_right positive] using share)
  have div := (prod_dvd_prod_of_subset P _ id sub).trans (Nat.prod_primeFactors_dvd z)
  have low : (2^b)^P.card ≤ ∏ p ∈ P, p := by simpa using prod_le_prod' lower
  have top : z ≤ (t+L)^(T.choose 2) := by
    calc
      _ ≤ ∏ i ∈ range T, (t+L)^i := prod_le_prod' fun i _ =>
        max_le (Nat.one_le_pow i _ (by omega)) (coefficient_height lp root_bound i)
      _ = _ := by rw [prod_pow_eq_pow_sum,sum_range_id,Nat.choose_two_right]
  apply (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
  rw [pow_mul,pow_mul]
  exact ((low.trans (Nat.le_of_dvd pos div)).trans top).trans (Nat.pow_le_pow_left height _)

end PrimeFactors.SignedLargeOrder
