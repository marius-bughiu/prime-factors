import PrimeFactors.MonotoneDivisorSampling
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Zify

/-! Sharp probability that the sum of two independent positive integers with
decreasing probability masses shares a proper factor with a balanced semiprime.
Both extremal rectangle sizes and the factor revealed by their larger cutoff are
checked. The existence proofs for optimal cutoffs use the unknown primes. -/

namespace PrimeFactors.TwoDrawBalancedArithmetic

/-- Once the longer prefix reaches p, the two exact complete-period terms
cover its entire length with the indicated weights. No upper bound on b. -/
theorem floors {p q b : ℕ} (hp : 2≤p) (order : p<q) (large : p≤b) :
    b≤(q-1)*(b/p)+(p-1)*(b/q) := by
  have pp : 0<p := by omega
  have qq : 0<q := by omega
  have first : 1≤b/p := (Nat.le_div_iff_mul_le pp).mpr (by simpa)
  by_cases low : b<q
  · have term := Nat.mul_le_mul_left (q-1) first
    rw [Nat.mul_one] at term
    omega
  · have second : 1≤b/q := (Nat.le_div_iff_mul_le qq).mpr (by simpa using le_of_not_gt low)
    have l := Nat.mul_le_mul_right (b/p) (by omega : p≤q-1)
    have r := Nat.mul_le_mul_left (p-1) second
    have rem := Nat.mod_lt b pp
    have eq := Nat.mod_add_div b p
    rw [Nat.mul_one] at r
    omega

/-- Literal integer lengths and one hit count per prime, with the deficits
cleared of positive denominators. This is the form that fits a count proof. -/
theorem large_count {p q a b u v : ℕ} (hp : 2≤p) (order : p<q) (large : p≤b)
    (hitP : (p-1)*u+a*(b/p)≤a*b) (hitQ : (q-1)*v+a*(b/q)≤a*b) :
    (u+v)*(p-1)*(q-1)≤a*b*(p+q-3) := by
  have cov := floors hp order large
  have cu := Nat.mul_le_mul_left (q-1) hitP
  have cv := Nat.mul_le_mul_left (p-1) hitQ
  have cf := Nat.mul_le_mul_left a cov
  have eq' : p+q-3+1=(p-1)+(q-1) := by omega
  nlinarith only [cu,cv,cf,congrArg (fun z => (a*b)*z) eq']

/-- For a,b≤P, the small-rectangle density increases toward the corner
(P,P). Multiplying each nonnegative one-coordinate improvement separately
avoids any assumptions about the sign of the numerator. -/
theorem small_both {P Q a b : ℚ} (pa : 0<a) (pb : 0<b) (ha : a≤P) (hb : b≤P)
    (order : P≤Q) :
    (2*(a+b)-P-Q)/(a*b)≤(3*P-Q)/(P^2) := by
  have pp := lt_of_lt_of_le pa ha
  have first : (2*(a+b)-P-Q)/(a*b)≤(2*(P+b)-P-Q)/(P*b) := by
    apply (div_le_div_iff₀ (mul_pos pa pb) (mul_pos pp pb)).mpr
    nlinarith only [mul_nonneg (mul_nonneg (sub_nonneg.mpr ha) pb.le)
      (show 0≤P+Q-2*b by linarith)]
  apply first.trans
  apply (div_le_div_iff₀ (mul_pos pp pb) (sq_pos_of_pos pp)).mpr
  nlinarith only [mul_nonneg (mul_nonneg (sub_nonneg.mpr hb) pp.le) (sub_nonneg.mpr order)]

/-- An integer form for computing the two diagonals when both start. -/
theorem small_both_count {P Q a b : ℕ} (pa : 0<a) (pb : 0<b) (ha : a≤P) (hb : b≤P)
    (order : P≤Q) (both : Q≤a+b) :
    ((a+b-P)+(a+b-Q))*P^2 ≤ (3*P-Q)*(a*b) := by
  have h := small_both (P:=(P:ℚ)) (Q:=(Q:ℚ)) (a:=(a:ℚ)) (b:=(b:ℚ))
    (by exact_mod_cast pa) (by exact_mod_cast pb) (by exact_mod_cast ha)
    (by exact_mod_cast hb) (by exact_mod_cast order)
  have bound := (div_le_div_iff₀ (mul_pos (by exact_mod_cast pa) (by exact_mod_cast pb))
    (sq_pos_of_pos (by exact_mod_cast (pa.trans_le ha)))).mp h
  have c : Q≤3*P := by omega
  have out : (((a+b-P : ℕ) : ℚ)+((a+b-Q : ℕ) : ℚ))*(P:ℚ)^2 ≤
      ((3*P-Q : ℕ) : ℚ)*((a:ℚ)*b) := by
    push_cast [Nat.cast_sub (order.trans both),Nat.cast_sub both,Nat.cast_sub c]
    linarith only [bound]
  exact_mod_cast out

/-- If q gives zero hits, the sharp single-prime bound implies the same corner
upper bound. Includes all q=2p−1 edge cases. -/
theorem small_one_count {P Q a b hits : ℕ} (balanced : Q≤2*P) (one : P*hits≤a*b) :
    hits*P^2≤a*b*(3*P-Q) := by
  calc
    _ = P*(P*hits) := by ring
    _ ≤ P*(a*b) := Nat.mul_le_mul_left _ one
    _ = a*b*P := by ac_rfl
    _ ≤ _ := Nat.mul_le_mul_left _ (by omega)

/-- B=(P+Q−1)/(PQ) beats C=(3P−Q)/P² exactly from the stated crossover. -/
theorem crossover {P Q : ℚ} (posP : 0<P) (posQ : 0<Q) :
    (3*P-Q)/(P^2)≤(P+Q-1)/(P*Q) ↔ P≤(Q-P)^2 := by
  rw [div_le_div_iff₀ (sq_pos_of_pos posP) (mul_pos posP posQ)]
  have eq : (P+Q-1)*P^2-(3*P-Q)*(P*Q) = P*((Q-P)^2-P) := by ring
  constructor
  · intro hit
    have nonnegative : 0≤P*((Q-P)^2-P) := by linarith only [eq,hit]
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right nonnegative posP)
  · intro cross
    have nonnegative := mul_nonneg posP.le (sub_nonneg.mpr cross)
    linarith only [eq,nonnegative]

end PrimeFactors.TwoDrawBalancedArithmetic


namespace PrimeFactors.TwoDrawSampling
open Finset

/-- Count a zero residue among sums of independent positive uniform prefixes. -/
noncomputable def hits (d a b : ℕ) : ℕ :=
  ∑ i ∈ range a, ∑ j ∈ range b, if d ∣ (i+1)+(j+1) then 1 else 0

theorem hits_comm (d a b : ℕ) : hits d a b = hits d b a := by
  unfold hits
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro i _
  rw [Nat.add_comm (i+1) (j+1)]

private theorem divisible_row (d x b : ℕ) :
    (∑ j ∈ range b, if d ∣ x+(j+1) then 1 else 0) + x/d = (x+b)/d := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [sum_range_succ]
    by_cases hd : d ∣ x+b+1
    · rw [Nat.add_succ, Nat.succ_div_of_dvd hd]
      rw [if_pos hd]
      omega
    · rw [Nat.add_succ, Nat.succ_div_of_not_dvd hd]
      rw [if_neg hd,Nat.add_zero,ih]

theorem hits_step {d : ℕ} (hd : 0<d) (a b : ℕ) :
    hits d a (b+d) = hits d a b + a := by
  have rows (i : ℕ) :
      (∑ j ∈ range (b+d), if d ∣ (i+1)+(j+1) then 1 else 0) =
      (∑ j ∈ range b, if d ∣ (i+1)+(j+1) then 1 else 0)+1 := by
    have x := divisible_row d (i+1) (b+d)
    have y := divisible_row d (i+1) b
    rw [←Nat.add_assoc, Nat.add_div_right _ hd] at x
    omega
  simp [hits,rows,sum_add_distrib]

theorem hits_periods {d : ℕ} (hd : 0<d) (a b k : ℕ) :
    hits d a (b+k*d) = hits d a b + k*a := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [Nat.succ_mul,←Nat.add_assoc,hits_step hd,ih]

theorem hits_reduce {d : ℕ} (hd : 0<d) (a b : ℕ) :
    hits d a b = hits d a (b%d) + (b/d)*a := by
  simpa only [Nat.mul_comm (b/d) d,Nat.mod_add_div] using hits_periods hd a (b%d) (b/d)

private theorem short_row {d x b : ℕ} (hx : x<d) (hb : b<d) :
    (∑ j ∈ range b, if d ∣ x+(j+1) then 1 else 0) = if d≤x+b then 1 else 0 := by
  have row := divisible_row d x b
  rw [Nat.div_eq_of_lt hx,Nat.add_zero] at row
  rw [row]
  by_cases le : d≤x+b
  · rw [if_pos le]
    exact (Nat.div_eq_iff (by omega : 0<d)).mpr ⟨by simpa using le,by omega⟩
  · rw [if_neg le,Nat.div_eq_of_lt (by omega)]

theorem hits_small {d a b : ℕ} (ha : a<d) (hb : b<d) :
    hits d a b = a+b+1-d := by
  induction a with
  | zero => simp [hits]; omega
  | succ a ih =>
    rw [hits, sum_range_succ]
    change hits d a b + _ = _
    rw [ih (by omega),short_row ha hb]
    split <;> omega

private theorem small_bound {d a b : ℕ} (ha : a<d) (hb : b<d) :
    (d-1)*hits d a b ≤ a*b := by
  rw [hits_small ha hb]
  by_cases tail : d ≤ a+b+1
  · zify [tail, show 1≤d by omega]
    nlinarith only [mul_nonneg (show (0:ℤ)≤d-1-a by omega) (show (0:ℤ)≤d-1-b by omega)]
  · rw [Nat.sub_eq_zero_of_le (show a+b+1≤d by omega),Nat.mul_zero]
    exact Nat.zero_le _

private theorem short_second_bound {d b : ℕ} (hb : b<d) (a : ℕ) :
    (d-1)*hits d a b ≤ a*b := by
  have pos : 0<d := by omega
  have total := Nat.mod_add_div a d
  have part := Nat.mul_le_mul_right (a/d) (Nat.sub_le d 1)
  have cover : a%d + (d-1)*(a/d) ≤ a := by omega
  calc
    (d-1)*hits d a b =
        (d-1)*hits d b (a%d) + ((d-1)*(a/d))*b := by
          rw [hits_comm d a b,hits_reduce pos b a,Nat.mul_add,Nat.mul_assoc]
    _ ≤ b*(a%d) + ((d-1)*(a/d))*b :=
      Nat.add_le_add_right (small_bound hb (Nat.mod_lt a pos)) _
    _ = (a%d+(d-1)*(a/d))*b := by ring
    _ ≤ a*b := Nat.mul_le_mul_right b cover

/-- Complete periods in the longer prefix give a quantitative deficit
from the universal single-modulus bound. -/
theorem period_deficit {d : ℕ} (hd : 0<d) (a b : ℕ) :
    (d-1)*hits d a b + a*(b/d) ≤ a*b := by
  have restore : d-1+1=d := by omega
  calc
    (d-1)*hits d a b + a*(b/d) =
        (d-1)*hits d a (b%d) + a*(b/d)*(d-1+1) := by
          rw [hits_reduce hd a b]; ring
    _ ≤ a*(b%d) + a*(b/d)*(d-1+1) :=
      Nat.add_le_add_right (short_second_bound (Nat.mod_lt b hd) a) _
    _ = a*(b%d+d*(b/d)) := by rw [restore]; ring
    _ = a*b := by rw [Nat.mod_add_div]

/-- A uniform-rectangle bound controls products of any two nonnegative
decreasing finite weight sequences. No identical-law assumption is used. -/
theorem weighted_rectangle (g : ℕ → ℕ → ℝ) (u v : ℕ → ℝ) (A B : ℕ) (r : ℝ)
    (hu : Antitone u) (hv : Antitone v) (un : ∀ i, 0 ≤ u i) (vn : ∀ j, 0 ≤ v j)
    (bound : ∀ a ≤ A, ∀ b ≤ B, ∑ i ∈ range a, ∑ j ∈ range b, g i j ≤ a*b*r) :
    ∑ i ∈ range A, u i*(∑ j ∈ range B, v j*g i j) ≤
      (∑ i ∈ range A, u i)*((∑ j ∈ range B, v j)*r) := by
  apply MonotoneDivisorSampling.weighted_of_prefix _ u _ A hu un
  intro a ha
  have inner := MonotoneDivisorSampling.weighted_of_prefix
      (fun j => ∑ i ∈ range a, g i j) v (a*r) B hv vn (by
        intro b hb
        rw [sum_comm]
        simpa only [mul_left_comm, mul_assoc] using bound a ha b hb)
  rw [sum_comm]
  simp_rw [←mul_sum]
  calc
    _ ≤ _ := inner
    _ = _ := by ring

end PrimeFactors.TwoDrawSampling
namespace PrimeFactors.TwoDrawSampling
open Finset TwoDrawBalancedArithmetic

/-- The search succeeds precisely when a prime divisor, and not the full
input, divides the sum of the two draws. -/
def proper (n i j : ℕ) : ℕ :=
  let s := (i+1)+(j+1)
  if ¬n.Coprime s ∧ ¬n∣s then 1 else 0

noncomputable def properCount (n a b : ℕ) : ℕ :=
  ∑ i ∈ range a, ∑ j ∈ range b, proper n i j

theorem overlap {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q) (a b : ℕ) :
    properCount (p*q) a b + 2*hits (p*q) a b = hits p a b + hits q a b := by
  have co := (Nat.coprime_primes pp qp).mpr ne
  have eq (i j : ℕ) :
      proper (p*q) i j + 2*(if p*q ∣ (i+1)+(j+1) then 1 else 0) =
      (if p ∣ (i+1)+(j+1) then 1 else 0) + (if q ∣ (i+1)+(j+1) then 1 else 0) := by
    let s := (i+1)+(j+1)
    have both : p*q∣s ↔ p∣s ∧ q∣s :=
      ⟨fun h => ⟨(dvd_mul_right p q).trans h,(dvd_mul_left q p).trans h⟩,
        fun h => co.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
    unfold proper
    change (if ¬(p*q).Coprime s ∧ ¬p*q∣s then 1 else 0) + 2*(if p*q∣s then 1 else 0) =
      (if p∣s then 1 else 0) + (if q∣s then 1 else 0)
    by_cases hp : p∣s <;> by_cases hq : q∣s <;>
      simp [Nat.coprime_mul_iff_left,pp.coprime_iff_not_dvd,qp.coprime_iff_not_dvd,both,hp,hq]
  calc
    _ = ∑ i ∈ range a, ∑ j ∈ range b,
        (proper (p*q) i j + 2*(if p*q∣(i+1)+(j+1) then 1 else 0)) := by
      simp only [properCount,hits,sum_add_distrib,←mul_sum]
    _ = _ := by simp only [eq,sum_add_distrib,hits]

private theorem no_overlap {p q a b : ℕ} (hp : 2≤p) (ha : a<q) (hb : b<q) :
    hits (p*q) a b=0 := by
  have big := Nat.mul_le_mul_right q hp
  rw [hits_small (by omega) (by omega)]
  omega

/-- For long uniform prefixes the first sharp rational bound applies. -/
theorem long_count {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (order : p<q)
    (a b : ℕ) (long : p≤b) :
    properCount (p*q) a b*(p-1)*(q-1) ≤ a*b*(p+q-3) := by
  have total := overlap pp qp order.ne a b
  have upper := large_count pp.two_le order long (period_deficit pp.pos a b) (period_deficit qp.pos a b)
  exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega :
    properCount (p*q) a b≤hits p a b+hits q a b))).trans upper

/-- The second sharp bound handles prefixes strictly shorter than p. -/
theorem short_count {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (order : p<q)
    (bal : q<2*p) {a b : ℕ} (pa : 0<a) (pb : 0<b) (ha : a<p) (hb : b<p) :
    properCount (p*q) a b*(p-1)^2 ≤ a*b*(3*(p-1)-(q-1)) := by
  have hp := pp.two_le
  have exactCounts := overlap pp qp order.ne a b
  rw [no_overlap hp (ha.trans order) (hb.trans order),Nat.mul_zero,Nat.add_zero] at exactCounts
  have support : q-1≤2*(p-1) := by omega
  by_cases both : q-1≤a+b
  · rw [hits_small ha hb,hits_small (ha.trans order) (hb.trans order)] at exactCounts
    have small := small_both_count pa pb (by omega : a≤p-1) (by omega : b≤p-1)
      (by omega : p-1≤q-1) both
    rw [Nat.mul_comm (3*(p-1)-(q-1))] at small
    have e : properCount (p*q) a b = (a+b-(p-1))+(a+b-(q-1)) := by omega
    rw [e]
    exact small
  · have noQ := hits_small (ha.trans order) (hb.trans order)
    have onlyP : properCount (p*q) a b=hits p a b := by omega
    exact small_one_count support (by rw [onlyP]; exact small_bound ha hb)

theorem long_attained {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (order : p<q)
    (bal : q<2*p) :
    properCount (p*q) (p-1) (q-1) = p+q-3 := by
  have hp := pp.two_le
  have hq := qp.two_le
  have counts := overlap pp qp order.ne (p-1) (q-1)
  rw [no_overlap hp (by omega) (by omega),Nat.mul_zero,Nat.add_zero,
    hits_small (by omega : p-1<q) (by omega : q-1<q)] at counts
  have e : q-1=(q-1-p)+p := by omega
  have hitP : hits p (p-1) (q-1) = q-2 := by
    rw [e,hits_step pp.pos,hits_small (by omega) (by omega)]
    omega
  omega

theorem short_attained {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (order : p<q)
    (bal : q<2*p) :
    properCount (p*q) (p-1) (p-1) = 3*(p-1)-(q-1) := by
  have hp := pp.two_le
  have counts := overlap pp qp order.ne (p-1) (p-1)
  rw [no_overlap hp (by omega) (by omega),Nat.mul_zero,Nat.add_zero,
    hits_small (by omega : p-1<p) (by omega : p-1<p),
    hits_small (by omega : p-1<q) (by omega : p-1<q)] at counts
  omega

end PrimeFactors.TwoDrawSampling
namespace PrimeFactors.TwoDrawSampling
open Finset

noncomputable def longRate (p q : ℕ) : ℝ :=
  ((p+q-3:ℕ):ℝ)/(((p-1:ℕ):ℝ)*((q-1:ℕ):ℝ))

noncomputable def shortRate (p q : ℕ) : ℝ :=
  ((3*(p-1)-(q-1):ℕ):ℝ)/((p-1:ℕ):ℝ)^2

noncomputable def best (p q : ℕ) : ℝ := max (longRate p q) (shortRate p q)

theorem properCount_comm (n a b : ℕ) : properCount n a b = properCount n b a := by
  unfold properCount
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro i _
  simp only [proper,Nat.add_comm (i+1) (j+1)]

private theorem rectangle_ordered {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (order : p<q) (bal : q<2*p) {a b : ℕ} (ab : a≤b) :
    (properCount (p*q) a b : ℝ) ≤ a*b*best p q := by
  have hp := pp.two_le
  have hq := qp.two_le
  have posP : (0:ℝ)<(p-1:ℕ) := by exact_mod_cast (show 0<p-1 by omega)
  have posQ : (0:ℝ)<(q-1:ℕ) := by exact_mod_cast (show 0<q-1 by omega)
  by_cases zero : a=0
  · simp [zero,properCount]
  by_cases large : p≤b
  · have h := long_count pp qp order a b large
    have cast : (properCount (p*q) a b:ℝ)*((p-1:ℕ):ℝ)*((q-1:ℕ):ℝ)≤
        (a:ℝ)*b*((p+q-3:ℕ):ℝ) := by exact_mod_cast h
    have bound : (properCount (p*q) a b:ℝ)≤a*b*longRate p q := by
      rw [longRate,←mul_div_assoc,le_div_iff₀ (mul_pos posP posQ)]
      simpa only [mul_assoc] using cast
    exact bound.trans (mul_le_mul_of_nonneg_left (le_max_left ..) (by positivity))
  · have h := short_count pp qp order bal (by omega : 0<a) (by omega : 0<b)
        (by omega : a<p) (by omega : b<p)
    have cast : (properCount (p*q) a b:ℝ)*((p-1:ℕ):ℝ)^2 ≤
        (a:ℝ)*b*((3*(p-1)-(q-1):ℕ):ℝ) := by exact_mod_cast h
    have bound : (properCount (p*q) a b:ℝ)≤a*b*shortRate p q := by
      rw [shortRate,←mul_div_assoc,le_div_iff₀ (sq_pos_of_pos posP)]
      exact cast
    exact bound.trans (mul_le_mul_of_nonneg_left (le_max_right ..) (by positivity))

theorem rectangle {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (order : p<q) (bal : q<2*p) (a b : ℕ) :
    (properCount (p*q) a b : ℝ) ≤ a*b*best p q := by
  rcases le_total a b with h | h
  · exact rectangle_ordered pp qp order bal h
  · rw [properCount_comm, mul_comm (a:ℝ) b]
    exact rectangle_ordered pp qp order bal h

theorem finite_weighted {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (order : p<q) (bal : q<2*p)
    (u v : ℕ → ℝ) (A B : ℕ) (hu : Antitone u) (hv : Antitone v)
    (un : ∀ i, 0≤u i) (vn : ∀ j, 0≤v j) :
    ∑ i ∈ range A, u i*(∑ j ∈ range B, v j*proper (p*q) i j) ≤
    (∑ i ∈ range A, u i)*((∑ j ∈ range B, v j)*best p q) := by
  apply weighted_rectangle _ u v A B _ hu hv un vn
  intro a _ b _
  simpa only [properCount,Nat.cast_sum] using rectangle pp qp order bal a b

/-- Independent uniform draws of the displayed lengths attain the bound.
The lengths themselves depend on the unknown primes. -/
theorem attained {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (order : p<q) (bal : q<2*p) :
    ∃ a b : ℕ, 0<a ∧ 0<b ∧ (properCount (p*q) a b:ℝ)/((a:ℝ)*b)=best p q := by
  have hp := pp.two_le
  have hq := qp.two_le
  rcases le_total (longRate p q) (shortRate p q) with h | h
  · refine ⟨p-1,p-1,by omega,by omega,?_⟩
    rw [best,max_eq_right h,short_attained pp qp order bal,shortRate,pow_two]
  · refine ⟨p-1,q-1,by omega,by omega,?_⟩
    rw [best,max_eq_left h,long_attained pp qp order bal,longRate]

end PrimeFactors.TwoDrawSampling


/-! A uniform bound for finite prefix rectangles extends to two independent
probability mass functions on the naturals, including unbounded supports. -/

namespace PrimeFactors.TwoDrawInfinite

open Filter Finset
open scoped Topology

/-- Normalization and nonnegativity suffice once the weighted inequality
is known on all finite rectangles. First let the second prefix length tend
to infinity, and then the first prefix length. -/
theorem of_rectangles {u v : ℕ → ℝ} {g : ℕ → ℕ → ℝ} {R : ℝ}
    (hu : HasSum u 1) (hv : HasSum v 1)
    (upos : ∀ i, 0≤u i) (vpos : ∀ j, 0≤v j)
    (scores : ∀ i j, 0≤g i j ∧ g i j≤1)
    (rectangles : ∀ a b : ℕ, (∑ i ∈ range a, u i*(∑ j ∈ range b, v j*g i j)) ≤
      (∑ i ∈ range a, u i)*((∑ j ∈ range b, v j)*R)) :
    (∑' i, u i*(∑' j, v j*g i j)) ≤ R := by
  have term_nonneg (i j : ℕ) : 0≤v j*g i j := mul_nonneg (vpos j) (scores i j).1
  have term_le (i j : ℕ) : v j*g i j≤v j := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (scores i j).2 (vpos j)
  have row (i : ℕ) : Summable (fun j => v j*g i j) :=
    Summable.of_nonneg_of_le (term_nonneg i) (term_le i) hv.summable
  have row_le (i : ℕ) : (∑' j, v j*g i j)≤1 := by
    rw [←hv.tsum_eq]
    exact (row i).tsum_le_tsum (term_le i) hv.summable
  have outer : Summable (fun i => u i*(∑' j, v j*g i j)) := by
    apply Summable.of_nonneg_of_le _ _ hu.summable
    · intro i
      exact mul_nonneg (upos i) (tsum_nonneg (term_nonneg i))
    · intro i
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (row_le i) (upos i)
  have partial_bound (a : ℕ) : (∑ i ∈ range a, u i*(∑' j, v j*g i j)) ≤
      (∑ i ∈ range a, u i)*R := by
    have left := tendsto_finset_sum (range a) (fun (i : ℕ) _ =>
      ((row i).hasSum.tendsto_sum_nat).const_mul (u i))
    have right := (hv.tendsto_sum_nat.mul_const R).const_mul (∑ i ∈ range a, u i)
    simpa only [one_mul] using le_of_tendsto_of_tendsto' left right (rectangles a)
  simpa only [one_mul] using le_of_tendsto_of_tendsto'
    outer.hasSum.tendsto_sum_nat (hu.tendsto_sum_nat.mul_const R) partial_bound

end PrimeFactors.TwoDrawInfinite

namespace PrimeFactors.TwoDrawSampling

/-- Exact cap for every independent pair of decreasing distributions, including
those with unbounded support. The displayed maximizing rectangles attain it. -/
theorem infinite_weighted {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (order : p<q) (bal : q<2*p)
    (u v : ℕ → ℝ) (hu : Antitone u) (hv : Antitone v)
    (un : ∀ i, 0≤u i) (vn : ∀ j, 0≤v j) (su : HasSum u 1) (sv : HasSum v 1) :
    (∑' i, u i*(∑' j, v j*proper (p*q) i j)) ≤ best p q := by
  apply TwoDrawInfinite.of_rectangles su sv un vn
  · intro i j
    by_cases h : ¬(p*q).Coprime ((i+1)+(j+1)) ∧ ¬p*q∣(i+1)+(j+1) <;> simp [proper,h]
  · intro a b
    exact finite_weighted pp qp order bal u v a b hu hv un vn

/-- Both optimizing formulas stay below the sum of the individual prime
bounds, including the crossing case. -/
theorem below_separate {p q : ℕ} (hp : 2<p) (order : p<q) (bal : q<2*p) :
    best p q < 1/((p-1:ℕ):ℝ) + 1/((q-1:ℕ):ℝ) := by
  let P : ℝ := (p-1:ℕ)
  let Q : ℝ := (q-1:ℕ)
  have pp : 0<P := by dsimp only [P]; exact_mod_cast (show 0<p-1 by omega)
  have qq : 0<Q := by dsimp only [Q]; exact_mod_cast (show 0<q-1 by omega)
  have pq : P<Q := by dsimp only [P,Q]; exact_mod_cast (show p-1<q-1 by omega)
  have a : ((p+q-3:ℕ):ℝ) = P+Q-1 := by
    have h : p+q-3+1=(p-1)+(q-1) := by omega
    have c := (show ((p+q-3:ℕ):ℝ)+1=P+Q by dsimp only [P,Q]; exact_mod_cast h)
    linarith
  have b : ((3*(p-1)-(q-1):ℕ):ℝ) = 3*P-Q := by
    have h : 3*(p-1)-(q-1)+(q-1)=3*(p-1) := by omega
    have c := (show ((3*(p-1)-(q-1):ℕ):ℝ)+Q=3*P by dsimp only [P,Q]; exact_mod_cast h)
    linarith
  change max (_/(P*Q)) (_/P^2) < 1/P+1/Q
  have reciprocals : 1/P+1/Q=(P+Q)/(P*Q) := by
    field_simp [pp.ne',qq.ne']
    ring
  rw [a,b,max_lt_iff,reciprocals]
  constructor
  · apply (div_lt_div_iff_of_pos_right (mul_pos pp qq)).mpr
    linarith
  · rw [div_lt_div_iff₀ (sq_pos_of_pos pp) (mul_pos pp qq)]
    nlinarith only [mul_pos pp (sq_pos_of_pos (sub_pos.mpr pq))]


/-- Whole target-size bound under the information available from factor widths. -/
theorem target_rate {p q : ℕ} (pp : p.Prime) (order : p<q)
    (lo : 2^1023≤p) (hi : q<2^1024) : best p q < 1/(2:ℝ)^1022 := by
  have odd := pp.odd_of_ne_two (by omega)
  obtain ⟨i,h⟩ := odd
  have lp : (2:ℝ)^1023 ≤ (p-1:ℕ) := by exact_mod_cast (show 2^1023≤p-1 by omega)
  have lq : (2:ℝ)^1023 ≤ (q-1:ℕ) := by exact_mod_cast (show 2^1023≤q-1 by omega)
  have bound := below_separate (by omega : 2<p) order (by omega : q<2*p)
  have positive : (0:ℝ)<2^1023 := by positivity
  calc
    _ < _ := bound
    _ ≤ 1/(2:ℝ)^1023+1/(2:ℝ)^1023 := add_le_add (one_div_le_one_div_of_le positive lp)
      (one_div_le_one_div_of_le positive lq)
    _ = _ := by
      rw [show 1023=1022+1 by decide, pow_succ]
      ring

theorem example_77 : best 7 11=1/4 := by norm_num [best,longRate,shortRate]
theorem example_143 : best 11 13=9/50 := by norm_num [best,longRate,shortRate]

end PrimeFactors.TwoDrawSampling

namespace PrimeFactors.TwoDrawBalancedArithmetic

private theorem strict_floor_cover {p q b : ℕ} (hp : 2≤p) (gap : p+2≤q)
    (large : p≤b) (away : b≠q-1) :
    b<(q-1)*(b/p)+(p-1)*(b/q) := by
  have pp : 0<p := by omega
  have qq : 0<q := by omega
  have first : 1≤b/p := (Nat.le_div_iff_mul_le pp).mpr (by simpa)
  by_cases low : b<q
  · have term := Nat.mul_le_mul_left (q-1) first
    rw [Nat.mul_one] at term
    omega
  · have second : 1≤b/q := (Nat.le_div_iff_mul_le qq).mpr (by simpa using le_of_not_gt low)
    have l := Nat.mul_lt_mul_of_pos_right (by omega : p<q-1) (by omega : 0<b/p)
    have r := Nat.mul_le_mul_left (p-1) second
    have rem := Nat.mod_lt b pp
    have eq := Nat.mod_add_div b p
    rw [Nat.mul_one] at r
    omega

/-- The long rate B is unattainable away from b=q−1, even for the
unadjusted sum of the two prime-hit counts u and v. -/
theorem large_count_strict {p q a b u v : ℕ} (hp : 2≤p) (gap : p+2≤q) (pa : 0<a)
    (large : p≤b) (away : b≠q-1)
    (hitP : (p-1)*u+a*(b/p)≤a*b) (hitQ : (q-1)*v+a*(b/q)≤a*b) :
    (u+v)*(p-1)*(q-1)<a*b*(p+q-3) := by
  have cover := strict_floor_cover hp gap large away
  have cu := Nat.mul_le_mul_left (q-1) hitP
  have cv := Nat.mul_le_mul_left (p-1) hitQ
  have cf := Nat.mul_lt_mul_of_pos_left cover pa
  have eq : p+q-3+1=(p-1)+(q-1) := by omega
  nlinarith only [cu,cv,cf,congrArg (fun z => (a*b)*z) eq]

/-- Write P=p−1 and Q=q−1. When both diagonals start, equality with C
fails if the second length b<P, provided the first length is positive. -/
theorem small_both_count_strict {P Q a b : ℕ} (pa : 0<a) (ha : a≤P) (hb : b<P)
    (order : P<Q) (both : Q≤a+b) :
    ((a+b-P)+(a+b-Q))*P^2 < (3*P-Q)*(a*b) := by
  have ap : P≤a+b := by omega
  have cap : Q≤3*P := by omega
  zify [ap,both,cap] at *
  have inc := mul_nonneg (mul_nonneg (show 0≤(P:ℤ)-a by omega) (by omega : 0≤(P:ℤ)))
    (show 0≤(P:ℤ)+Q-2*b by omega)
  have strict := mul_pos (mul_pos (show 0<(a:ℤ) by omega) (show 0<(P:ℤ)-b by omega))
    (show 0<(Q:ℤ)-P by omega)
  nlinarith only [inc,strict]

/-- With no q hits, even the best one-prime rate 1/(p−1) is strictly below
B if p>2. This also handles the end case q=2p−1. -/
theorem small_one_long_strict {p q a b u : ℕ} (hp : 2<p) (hq : 1≤q)
    (pa : 0<a) (pb : 0<b) (one : (p-1)*u≤a*b) :
    u*(p-1)*(q-1)<a*b*(p+q-3) := by
  calc
    u*(p-1)*(q-1) ≤ a*b*(q-1) := Nat.mul_le_mul_right _ (by simpa [mul_comm] using one)
    _ < _ := Nat.mul_lt_mul_of_pos_left (by omega : q-1<p+q-3) (Nat.mul_pos pa pb)

end PrimeFactors.TwoDrawBalancedArithmetic

namespace PrimeFactors.TwoDrawSampling

open TwoDrawBalancedArithmetic

/-- For two distinct odd balanced primes, any ordered positive rectangle of
globally maximal proper-gcd frequency reveals a prime: add one to its longer
prefix length and take a single gcd. -/
theorem maximizer_splits {p q a b : ℕ} (pp : p.Prime) (qp : q.Prime)
    (odd : 2<p) (order : p<q) (balanced : q<2*p) (pa : 0<a) (lengths : a≤b)
    (maximal : ∀ A B : ℕ, 0<A → 0<B →
      (properCount (p*q) A B : ℝ)/((A:ℝ)*B) ≤ (properCount (p*q) a b : ℝ)/((a:ℝ)*b)) :
    (b+1=p ∨ b+1=q) ∧ Nat.gcd (p*q) (b+1)=b+1 ∧ 1<b+1 ∧ b+1<p*q := by
  have pb := lt_of_lt_of_le pa lengths
  have posP : (0:ℝ)<(p-1:ℕ) := by exact_mod_cast (show 0<p-1 by omega)
  have posQ : (0:ℝ)<(q-1:ℕ) := by exact_mod_cast (show 0<q-1 by omega)
  have posAB : 0<(a:ℝ)*b := by exact_mod_cast Nat.mul_pos pa pb
  obtain ⟨A,B,hA,hB,win⟩ := attained pp qp order balanced
  have lower := maximal A B hA hB
  rw [win,le_div_iff₀ posAB,mul_comm (best p q)] at lower
  have not_long (h : properCount (p*q) a b*(p-1)*(q-1)<a*b*(p+q-3)) : False := by
    have c : (properCount (p*q) a b:ℝ)*((p-1:ℕ):ℝ)*((q-1:ℕ):ℝ) <
        (a:ℝ)*b*((p+q-3:ℕ):ℝ) := by exact_mod_cast h
    have less : (properCount (p*q) a b:ℝ)<(a:ℝ)*b*longRate p q := by
      rw [longRate,←mul_div_assoc,lt_div_iff₀ (mul_pos posP posQ)]
      simpa only [mul_assoc] using c
    exact (not_lt_of_ge lower) (less.trans_le (mul_le_mul_of_nonneg_left (le_max_left ..) posAB.le))
  have not_short (h : properCount (p*q) a b*(p-1)^2<a*b*(3*(p-1)-(q-1))) : False := by
    have c : (properCount (p*q) a b:ℝ)*((p-1:ℕ):ℝ)^2 <
        (a:ℝ)*b*((3*(p-1)-(q-1):ℕ):ℝ) := by exact_mod_cast h
    have less : (properCount (p*q) a b:ℝ)<(a:ℝ)*b*shortRate p q := by
      rw [shortRate,←mul_div_assoc,lt_div_iff₀ (sq_pos_of_pos posP)]
      exact c
    exact (not_lt_of_ge lower) (less.trans_le (mul_le_mul_of_nonneg_left (le_max_right ..) posAB.le))
  have upper : properCount (p*q) a b ≤ hits p a b+hits q a b := by
    have h := overlap pp qp order.ne a b
    omega
  have which : b+1=p ∨ b+1=q := by
    by_contra! away
    by_cases long : p≤b
    · have gap : p+2≤q := by
        obtain ⟨u,hu⟩ := pp.odd_of_ne_two (by omega)
        obtain ⟨v,hv⟩ := qp.odd_of_ne_two (by omega)
        omega
      have h := large_count_strict pp.two_le gap pa long (by omega : b≠q-1)
        (period_deficit pp.pos a b) (period_deficit qp.pos a b)
      exact not_long ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ upper)).trans_lt h)
    · have ap : a<p := by omega
      have bp : b<p := by omega
      rw [hits_small ap bp,hits_small (ap.trans order) (bp.trans order)] at upper
      by_cases two : q-1≤a+b
      · have h := small_both_count_strict pa (by omega : a≤p-1) (by omega : b<p-1)
          (by omega : p-1<q-1) two
        have c : properCount (p*q) a b ≤ (a+b-(p-1))+(a+b-(q-1)) := by omega
        apply not_short
        rw [Nat.mul_comm (a*b)]
        exact (Nat.mul_le_mul_right _ c).trans_lt h
      · have one : properCount (p*q) a b ≤ hits p a b := by rw [hits_small ap bp]; omega
        have single := period_deficit pp.pos a b
        have weight : (p-1)*properCount (p*q) a b≤a*b :=
          (Nat.mul_le_mul_left _ one).trans (by omega)
        exact not_long (small_one_long_strict odd (by omega) pa pb weight)
  refine ⟨which,?_⟩
  rcases which with e|e
  · rw [e,Nat.gcd_eq_right (dvd_mul_right p q)]
    exact ⟨rfl,pp.one_lt,by simpa using Nat.mul_lt_mul_of_pos_left qp.one_lt pp.pos⟩
  · rw [e,Nat.gcd_eq_right (dvd_mul_left q p)]
    exact ⟨rfl,qp.one_lt,by simpa using Nat.mul_lt_mul_of_pos_right pp.one_lt qp.pos⟩

end PrimeFactors.TwoDrawSampling
