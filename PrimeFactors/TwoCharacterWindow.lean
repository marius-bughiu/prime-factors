import PrimeFactors.ReciprocalDivisorClasses
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Tactic

/-! The two-character upper bound on any finite progression. The only external
analytic input is explicitly quantified as `PublishedPV`, Corollary 1 of
Frolenkov and Soundararajan (2013). -/
namespace PrimeFactors.TwoCharacterWindow
open Finset ReciprocalSumCharacter

noncomputable def char (d x : ℕ) : ℤ := jacobiSym (x:ℤ) d

noncomputable def total (d first step len : ℕ) : ℤ :=
  ∑ i ∈ range len, char d (first+step*i)

noncomputable def hits (a b first step len : ℕ) : Finset ℕ := by
  classical
  exact (range len).filter fun i =>
    char a (first+step*i)=1 ∧ char b (first+step*i)=1

/-- Checking the two public roots makes every actual odd divisor a survivor. -/
theorem divisor_mem {n a b f s j i len : ℕ} {A B : ℤ} (aa : a%4=3) (bb : b%4=3)
    (ca : n.Coprime a) (cb : n.Coprime b) (ra : (n:ℤ) ∣ A^2+a) (rb : (n:ℤ) ∣ B^2+b)
    (odd : Odd f) (div : f∣n) (point : f=s+j*i) (inRow : i<len) : i ∈ hits a b s j len := by
  classical
  rw [hits,mem_filter]
  refine ⟨mem_range.mpr inRow,?_⟩
  rw [←point]
  exact ⟨ReciprocalDivisorClasses.divisor_of_witness aa odd div ca ra,
          ReciprocalDivisorClasses.divisor_of_witness bb odd div cb rb⟩

/-- A direct indicator majorant. Jacobi zeros are permitted anywhere. -/
theorem majorant {a b : ℕ} (an : a≠0) (bn : b≠0) (first step len : ℕ) :
    4*((hits a b first step len).card:ℤ) ≤ len + total a first step len +
      total b first step len + total (a*b) first step len := by
  classical
  simp only [hits,card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,total]
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ i ∈ range len, (1 + char a (first+step*i) +
         char b (first+step*i) + char (a*b) (first+step*i)) := by
      apply sum_le_sum
      intro i _
      dsimp [char]
      rw [jacobiSym.mul_right' _ an bn]
      rcases jacobiSym.trichotomy ((first+step*i:ℕ):ℤ) a with ha|ha|ha <;>
        rcases jacobiSym.trichotomy ((first+step*i:ℕ):ℤ) b with hb|hb|hb <;>
        rw [ha,hb] <;> decide
    _ = _ := by simp [sum_add_distrib]

/-- Standard contiguous-interval form of the published bound specialized to
odd Jacobi characters. A value -1 certifies that the character is nonprincipal. -/
def PublishedPV : Prop := ∀ (d : ℕ), 100≤d → Odd d → (∃ x, char d x = -1) →
  ∀ first len, (|total d first 1 len|:ℝ) ≤
    Real.sqrt d * ((Real.log d+6)/(Real.pi*Real.sqrt 2)+1)

/-- A unit stride multiplies a translated ordinary character sum by a sign. -/
theorem progression_eq {d : ℕ} [NeZero d] (first step len : ℕ) (cop : step.Coprime d) :
    ∃ shift, |total d first step len| = |total d shift 1 len| := by
  let u := ZMod.unitOfCoprime step cop
  let t : ZMod d := (↑u⁻¹ : ZMod d)*first
  have eq : (step:ZMod d)*t=(first:ZMod d) := by
    rw [←ZMod.coe_unitOfCoprime step cop]
    change (u:ZMod d)*((↑u⁻¹:ZMod d)*first)=first
    rw [←mul_assoc,Units.mul_inv,one_mul]
  have eqv (i : ℕ) : (first+step*i : ZMod d) = step*(t.val+i) := by
    rw [ZMod.natCast_zmod_val,mul_add,eq]
  have asSign (x : ℕ) : char d x = sign (x : ZMod d) := by
    simpa [char] using (sign_cast (d:=d) (x:ℤ)).symm
  have factor : total d first step len = char d step * total d t.val 1 len := by
    unfold total
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro i _
    simp only [one_mul,asSign,Nat.cast_add,Nat.cast_mul,eqv,ReciprocalSumCharacter.sign_mul]
  have signed := jacobiSym.eq_one_or_neg_one (show (step:ℤ).gcd d=1 by
    rw [Int.gcd_natCast_natCast]; exact cop)
  refine ⟨t.val,?_⟩
  rw [factor,abs_mul]
  rcases signed with h|h <;> simp [char,h]

/-- A purely integer upper certificate for the real analytic error. The root
and binary-length bounds can both be checked with integer arithmetic. -/
theorem integer_error {d r b E : ℕ} (hd : 0<d) (root : d≤r^2) (bits : d≤2^b)
    (rounding : r*(5220+347*b) ≤ 2220*E) :
    Real.sqrt d * ((Real.log d+6)/(Real.pi*Real.sqrt 2)+1) ≤ E := by
  have sr : Real.sqrt d ≤ r := (Real.sqrt_le_iff.mpr ⟨by positivity,by exact_mod_cast root⟩)
  have db : (d:ℝ)≤(2:ℝ)^b := by exact_mod_cast bits
  have lg := Real.log_le_log (show 0<(d:ℝ) by exact_mod_cast hd) db
  rw [Real.log_pow] at lg
  have logBound : Real.log d ≤ (b:ℝ)*(347/500) := by
    exact lg.trans (mul_le_mul_of_nonneg_left (by linarith [Real.log_two_lt_d9]) (by positivity))
  have pi : (3.1415:ℝ) ≤ Real.pi := Real.pi_gt_d4.le
  have sqrtTwo : (1.414:ℝ) ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have denominator : (4.44:ℝ) ≤ Real.pi*Real.sqrt 2 :=
    (by norm_num : (4.44:ℝ) ≤ 3.1415*1.414).trans (mul_le_mul pi sqrtTwo (by norm_num) Real.pi_pos.le)
  have frac : (Real.log d+6)/(Real.pi*Real.sqrt 2) ≤ (347*b+3000)/2220 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have m := mul_le_mul_of_nonneg_left denominator (show 0≤(347*(b:ℝ)+3000)/2220 by positivity)
    linarith
  have m := mul_le_mul_of_nonneg_left (add_le_add_right frac 1) (Real.sqrt_nonneg (d:ℝ))
  have m' := mul_le_mul_of_nonneg_right sr (show 0≤(347*(b:ℝ)+3000)/2220+1 by positivity)
  have rr : (r:ℝ)*(5220+347*b) ≤ 2220*E := by exact_mod_cast rounding
  exact m.trans (m'.trans (by linarith only [rr]))

theorem progression_bound (pv : PublishedPV) {d r b E first step len : ℕ}
    (large : 100≤d) (odd : Odd d) (nonprincipal : ∃ x, char d x = -1) (stride : step.Coprime d)
    (root : d≤r^2) (bits : d≤2^b) (rounding : r*(5220+347*b) ≤ 2220*E) :
    total d first step len ≤ E := by
  have pos : 0<d := by omega
  letI : NeZero d := ⟨pos.ne'⟩
  obtain ⟨s,hs⟩ := progression_eq first step len stride
  have main := (pv d large odd nonprincipal s len).trans (integer_error pos root bits rounding)
  have bound : |total d s 1 len|≤(E:ℤ) := by exact_mod_cast main
  exact (le_abs_self _).trans (hs ▸ bound)

/-- All sixteen residue classes coprime to 60. -/
noncomputable def wheel : Finset ℕ := (range 60).filter fun r => r.Coprime 60

theorem wheel_card : wheel.card=16 := by decide +kernel

def rowStart (lo r : ℕ) := lo + (r+60-lo%60)%60

def rowLength (lo hi r : ℕ) :=
  let start := rowStart lo r
  if start≤hi then (hi-start)/60+1 else 0

/-- The inclusive public interval for the smaller factor when both factors are
bounded by B. The usual bit-width choice is B=2^bits-1. -/
def lower (n B : ℕ) := (n-1)/B+1

theorem locate {f lo hi : ℕ} (after : lo≤f) (before : f≤hi) (cop : f.Coprime 60) :
    ∃ r∈wheel, ∃ i<rowLength lo hi r, f = rowStart lo r+60*i := by
  let r := f%60
  let s := rowStart lo r
  have fe : s+60*((f-s)/60) = f := by dsimp [s,r,rowStart]; omega
  have sh : s≤hi := by omega
  refine ⟨r,mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (by decide)),?_⟩,
    (f-s)/60, ?_,fe.symm⟩
  · show (f%60).gcd 60=1
    rw [←Nat.gcd_rec,Nat.gcd_comm]
    exact cop
  · simp only [rowLength,if_pos (show rowStart lo r≤hi from sh)]
    change (f-s)/60<(hi-s)/60+1
    omega

theorem factors_located {p q B a b : ℕ} {A C : ℤ} (pos : 0<p) (ordered : p≤q) (bounded : q≤B)
    (wheelUnit : p.Coprime 60) (odd : Odd p) (aa : a%4=3) (bb : b%4=3)
    (ca : (p*q).Coprime a) (cb : (p*q).Coprime b)
    (ra : ((p*q:ℕ):ℤ) ∣ A^2+a) (rb : ((p*q:ℕ):ℤ) ∣ C^2+b) :
    ∃ r∈wheel, ∃ i∈hits a b (rowStart (lower (p*q) B) r) 60
      (rowLength (lower (p*q) B) (p*q).sqrt r), p=rowStart (lower (p*q) B) r+60*i := by
  have qp : 0<q := lt_of_lt_of_le pos ordered
  have bp : 0<B := lt_of_lt_of_le qp bounded
  have low : lower (p*q) B ≤ p := by
    apply (Nat.div_lt_iff_lt_mul bp).mpr
    exact (Nat.sub_lt (Nat.mul_pos pos qp) (by decide)).trans_le (Nat.mul_le_mul_left p bounded)
  have high := Nat.le_sqrt.mpr (Nat.mul_le_mul_left p ordered)
  obtain ⟨r,hr,i,hi,eq⟩ := locate low high wheelUnit
  exact ⟨r,hr,i,divisor_mem aa bb ca cb ra rb odd (dvd_mul_right p q) eq hi,eq⟩

/-- A per-class bound implies the same ratio for the aggregate over all wheel
classes, including the shorter final classes. -/
theorem window_bound {a b lo hi E F G scale cap : ℕ} (ap : a≠0) (bp : b≠0)
    (ea : ∀ s l, total a s 60 l ≤ E) (eb : ∀ s l, total b s 60 l ≤ F)
    (ec : ∀ s l, total (a*b) s 60 l ≤ G)
    (budget : ∀ r∈wheel, scale*(rowLength lo hi r+E+F+G) ≤ 4*cap*rowLength lo hi r) :
    scale*(∑ r ∈ wheel, (hits a b (rowStart lo r) 60 (rowLength lo hi r)).card)
      ≤ cap*(∑ r ∈ wheel, rowLength lo hi r) := by
  rw [Finset.mul_sum,Finset.mul_sum]
  apply sum_le_sum
  intro r hr
  let l := rowLength lo hi r
  let s := rowStart lo r
  have major := majorant ap bp s 60 l
  have totalE := ea s l
  have totalF := eb s l
  have totalG := ec s l
  have localCap : 4*(hits a b s 60 l).card ≤ l+E+F+G := by omega
  have h := budget r hr
  change scale*(hits a b s 60 l).card ≤ cap*l
  change scale*(l+E+F+G) ≤ 4*cap*l at h
  have scaled := (Nat.mul_le_mul_left scale localCap).trans h
  rw [Nat.mul_left_comm scale 4, Nat.mul_assoc 4 cap] at scaled
  exact (Nat.le_of_mul_le_mul_left scaled (by decide))

/-- Every lane length differs from floor((hi-lo+1)/60) by at most one. -/
theorem lengths {lo hi r : ℕ} (le : lo≤hi) :
    (hi-lo+1)/60 ≤ rowLength lo hi r ∧ rowLength lo hi r ≤ (hi-lo+1)/60+1 := by
  simp only [rowLength,rowStart]
  split <;> omega

/-- One finite integer inequality checks the desired fraction simultaneously
on every lane, down to its final position. -/
theorem wheel_budget {lo hi E F G scale cap : ℕ} (le : lo≤hi)
    (numeric : scale*((hi-lo+1)/60+1+E+F+G) ≤ 4*cap*((hi-lo+1)/60)) :
    ∀ r∈wheel, scale*(rowLength lo hi r+E+F+G) ≤ 4*cap*rowLength lo hi r := by
  intro r _
  have lens := lengths (r:=r) le
  exact (Nat.mul_le_mul_left scale (by omega)).trans (numeric.trans (Nat.mul_le_mul_left _ lens.1))

end PrimeFactors.TwoCharacterWindow
