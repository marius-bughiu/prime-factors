import PrimeFactors.ChebyshevFactorialRatio
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-! The prime-power form of the least common multiple through n and the
factorial ratio used in Chebyshev's prime estimates. -/

namespace PrimeFactors.ChebyshevPrimePowers
open Finset

noncomputable def L (n : ℕ) : ℕ :=
  ∏ p ∈ (range (n+1)).filter Nat.Prime, p^(Nat.log p n)

theorem L_pos (n : ℕ) : 0<L n :=
  prod_pos fun _ hp => pow_pos (mem_filter.mp hp).2.pos _

theorem valuation_L {p : ℕ} (hp : p.Prime) (n : ℕ) : (L n).factorization p=Nat.log p n := by
  classical
  unfold L
  rw [Nat.factorization_prod (fun _ hm => pow_ne_zero _ (mem_filter.mp hm).2.ne_zero),
    Finsupp.finset_sum_apply]
  rw [sum_eq_single p]
  · simp [hp.factorization_pow]
  · intro q hq ne
    simp [(mem_filter.mp hq).2.factorization_pow,Finsupp.single_apply,ne]
  · intro notIn
    have hi : n<p := by
      by_contra! low
      exact notIn (mem_filter.mpr ⟨mem_range.mpr (by omega),hp⟩)
    simp [hp.factorization_pow,hi]

theorem L_mono : Monotone L := by
  intro n m nm
  apply Nat.le_of_dvd (L_pos m)
  apply (Nat.factorization_le_iff_dvd (L_pos n).ne' (L_pos m).ne').mp
  intro p
  by_cases hp : p.Prime
  · simpa [valuation_L hp] using (Nat.log_mono_right (b:=p) nm)
  · simp [Nat.factorization_eq_zero_of_non_prime _ hp]

theorem L_crude {n B : ℕ} (bound : n≤B) : L n≤B^n := by
  by_cases zero : n=0
  · simp [zero,L]
  have hpBound {p} (h : p ∈ (range (n+1)).filter Nat.Prime) :
      p^(Nat.log p n)≤B := (Nat.pow_log_le_self p zero).trans bound
  have size : ((range (n+1)).filter Nat.Prime).card≤n := by
    have sub : (range (n+1)).filter Nat.Prime ⊆ Icc 1 n := by
      intro p hp
      obtain ⟨lo,pr⟩ := mem_filter.mp hp
      exact mem_Icc.mpr ⟨pr.one_le,by have := mem_range.mp lo; omega⟩
    simpa only [Nat.card_Icc,Nat.add_sub_cancel] using card_le_card sub
  have mul := prod_le_prod' (fun p hp => hpBound hp)
  rw [prod_const] at mul
  exact mul.trans (Nat.pow_le_pow_right (by omega) size)

private theorem floors (j : ℕ) : j/2 + j/3 + j/5 ≤ j+j/30 ∧ j+j/30≤j/2+j/3+j/5+1 := by
  let r := j%30
  have split : j=r+30*(j/30) := (Nat.mod_add_div ..).symm
  have per (i k : ℕ) (ik : i*k=30) (ip : 0 < i) :
      j/i = r/i+k*(j/30) := by
    calc
      j/i = (r+30*(j/30))/i := congrArg (·/i) split
      _ = (r+i*(k*(j/30)))/i := by rw [←Nat.mul_assoc i k,ik]
      _ = r/i+k*(j/30) := Nat.add_mul_div_left _ _ ip
  have a := per 2 15 (by decide) (by decide)
  have b := per 3 10 (by decide) (by decide)
  have c := per 5 6 (by decide) (by decide)
  have table : ∀ r : Fin 30, r.val/2 + r.val/3 +r.val/5 ≤ r.val ∧
      r.val ≤ r.val/2 + r.val/3+r.val/5+1 := by decide +kernel
  have small := table ⟨r,Nat.mod_lt _ (by decide)⟩
  dsimp only at small
  omega

def numerator (n : ℕ) := n.factorial * (n/30).factorial

def denominator (n : ℕ) := (n/2).factorial * (n/3).factorial * (n/5).factorial

private theorem exponent_bounds {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (denominator n).factorization p ≤ (numerator n).factorization p ∧
    (numerator n).factorization p ≤ (denominator n).factorization p + Nat.log p n ∧
    (denominator n).factorization p + Nat.log p n ≤
      (numerator n).factorization p + Nat.log p (n/6) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let I := Ico 1 (Nat.log p n+1)
  let J (i : ℕ) := n / p^i
  let bot (i : ℕ) := J i / 2 + J i / 3 + J i / 5
  let top (i : ℕ) := J i + J i / 30
  have factorial (c : ℕ) :
      ((n/c).factorial).factorization p = ∑ i ∈ I, J i / c := by
    rw [Nat.factorization_def _ hp, padicValNat_factorial
      (show Nat.log p (n/c) < Nat.log p n+1 by
        have := Nat.log_mono_right (b:=p) (Nat.div_le_self n c)
        omega)]
    apply sum_congr rfl
    intro i _
    simp only [J,Nat.div_div_eq_div_mul,mul_comm c]
  have base : n.factorial.factorization p = ∑ i ∈ I, J i := by simpa using factorial 1
  have upperEq : (numerator n).factorization p = ∑ i ∈ I, top i := by
    simp only [numerator, Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
      Finsupp.add_apply,base,factorial,top,sum_add_distrib]
  have lowerEq : (denominator n).factorization p = ∑ i ∈ I, bot i := by
    simp only [denominator, Nat.factorization_mul (Nat.mul_ne_zero (Nat.factorial_ne_zero _)
      (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _),
      Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
      Finsupp.add_apply,factorial,bot,sum_add_distrib]
  have size : I.card = Nat.log p n := by simp [I,Nat.card_Ico]
  rw [upperEq, lowerEq]
  refine ⟨sum_le_sum (fun i _ => (floors (J i)).1), ?_⟩
  constructor
  · have h : ∑ i ∈ I, top i ≤ ∑ i ∈ I, (bot i + 1) :=
      sum_le_sum fun i _ => (floors (J i)).2
    simpa only [sum_add_distrib,sum_const,nsmul_eq_mul,mul_one,size] using h
  · have each (i : ℕ) (hi : i ∈ I) :
        bot i + 1 ≤ top i + (if p^i ≤ n/6 then 1 else 0) := by
      split_ifs with small
      · exact Nat.add_le_add_right (floors (J i)).1 1
      · have nz : n ≠ 0 := by
          intro z
          simp [I,z] at hi
        have pw : p^i ≤ n := Nat.pow_le_of_le_log nz (by have := (mem_Ico.mp hi).2; omega)
        have pp : 0 < p^i := pow_pos hp.pos _
        have positive : 1 ≤ J i := (Nat.le_div_iff_mul_le pp).mpr (by simpa using pw)
        have less : J i < 6 := (Nat.div_lt_iff_lt_mul pp).mpr (by
          have h := (Nat.le_div_iff_mul_le (by decide : 0<6)).not.mp small
          simpa only [mul_comm (p^i)] using lt_of_not_ge h)
        have early (t : ℕ) (one : 1 ≤ t) (ltSix : t < 6) :
            t/2+t/3+t/5+1 ≤ t+t/30 := by interval_cases t <;> decide
        simpa only [Nat.add_zero] using early (J i) positive less
    have cover : (I.filter fun i => p^i ≤ n/6) ⊆ Ico 1 (Nat.log p (n/6)+1) := by
      intro i hi
      obtain ⟨hi,small⟩ := mem_filter.mp hi
      exact mem_Ico.mpr ⟨(mem_Ico.mp hi).1, Nat.lt_succ_of_le (Nat.le_log_of_pow_le hp.one_lt small)⟩
    have many : (I.filter fun i => p^i ≤ n/6).card ≤ Nat.log p (n/6) := by
      simpa [Nat.card_Ico] using card_le_card cover
    have total := sum_le_sum each
    rw [sum_add_distrib (f := bot) (g := fun _ => 1),
      sum_add_distrib (f := top) (g := fun i => if p^i ≤ n/6 then 1 else 0)] at total
    simp only [sum_const,nsmul_eq_mul,mul_one,size,Finset.sum_boole] at total
    exact total.trans (Nat.add_le_add_left many _)

private theorem dvd_by_prime {a b : ℕ} (ha : 0<a) (hb : 0<b)
    (byPrime : ∀ p, p.Prime → a.factorization p ≤ b.factorization p) : a ∣ b := by
  apply (Nat.factorization_le_iff_dvd ha.ne' hb.ne').mp
  intro p
  by_cases hp : p.Prime
  · exact byPrime p hp
  · simp [Nat.factorization_eq_zero_of_non_prime _ hp]

/-- The cleared factorial ratio is integral. Its prime exponents are all at
most those of the full prime-power product, and it contains the entire
contribution of the prime powers in the upper five sixths. -/
theorem divisibilities (n : ℕ) :
    denominator n ∣ numerator n ∧ numerator n ∣ denominator n * L n ∧
    denominator n * L n ∣ numerator n * L (n/6) := by
  have hn : 0<numerator n := Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  have hd : 0<denominator n := Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
    (Nat.factorial_pos _)
  refine ⟨dvd_by_prime hd hn (fun _ hp => (exponent_bounds hp n).1), ?_⟩
  constructor
  · apply dvd_by_prime hn (Nat.mul_pos hd (L_pos n))
    intro p hp
    simpa only [Nat.factorization_mul hd.ne' (L_pos n).ne', Finsupp.add_apply,valuation_L hp]
      using (exponent_bounds hp n).2.1
  · apply dvd_by_prime (Nat.mul_pos hd (L_pos n)) (Nat.mul_pos hn (L_pos (n/6)))
    intro p hp
    simpa only [Nat.factorization_mul hd.ne' (L_pos n).ne',
      Nat.factorization_mul hn.ne' (L_pos _).ne',Finsupp.add_apply,valuation_L hp]
      using (exponent_bounds hp n).2.2

def ratio (n : ℕ) := numerator n / denominator n

theorem ratio_dvd (n : ℕ) : ratio n ∣ L n ∧ L n ∣ ratio n * L (n/6) := by
  obtain ⟨exactDen, left, right⟩ := divisibilities n
  have denPos : 0 < denominator n := by unfold denominator; positivity
  have product : denominator n * ratio n = numerator n :=
    (Nat.mul_comm ..).trans (Nat.div_mul_cancel exactDen)
  rw [←product] at left right
  rw [Nat.mul_assoc] at right
  exact ⟨Nat.dvd_of_mul_dvd_mul_left denPos left, Nat.dvd_of_mul_dvd_mul_left denPos right⟩

theorem bridge (n : ℕ) :
    numerator n ≤ denominator n * L n ∧ denominator n * L n ≤ numerator n * L (n/6) := by
  obtain ⟨_, left, right⟩ := divisibilities n
  have denPos : 0 < denominator n := by unfold denominator; positivity
  have numPos : 0 < numerator n := by unfold numerator; positivity
  exact ⟨Nat.le_of_dvd (Nat.mul_pos denPos (L_pos n)) left,
    Nat.le_of_dvd (Nat.mul_pos numPos (L_pos _)) right⟩

theorem bounds (m : ℕ) :
    ChebyshevFactorialRatio.num m ≤ ChebyshevFactorialRatio.den m * L (30*m) ∧
    ChebyshevFactorialRatio.den m * L (30*m) ≤ ChebyshevFactorialRatio.num m * L (5*m) := by
  simpa only [ChebyshevFactorialRatio.num,ChebyshevFactorialRatio.den,numerator,denominator,
    show 30*m/30=m by omega,show 30*m/2=15*m by omega,show 30*m/3=10*m by omega,
    show 30*m/5=6*m by omega,show 30*m/6=5*m by omega] using bridge (30*m)

private theorem combine_lower {d k h n L₀ : ℕ} (pos : 0 < d) (ratioLB : k*d≤h*n)
    (lc : n≤d*L₀) : k≤h*L₀ := by
  refine Nat.le_of_mul_le_mul_right ?_ pos
  calc
    k*d ≤ h*n := ratioLB
    _ ≤ h*(d*L₀) := Nat.mul_le_mul_left _ lc
    _ = (h*L₀)*d := by ac_rfl

private theorem combine_upper {d k n L₀ L₁ : ℕ} (pos : 0 < d) (lc : d*L₀≤n*L₁)
    (ratioUB : n≤k*d) : L₀≤k*L₁ := by
  refine Nat.le_of_mul_le_mul_left ?_ pos
  calc
    d*L₀ ≤ n*L₁ := lc
    _ ≤ (k*d)*L₁ := Nat.mul_le_mul_right _ ratioUB
    _ = d*(k*L₁) := by ac_rfl

theorem lower (m : ℕ) : 2^(39*m) ≤ 2^32768 * L (30*m) := by
  refine combine_lower (d := ChebyshevFactorialRatio.den m) ?_ (ChebyshevFactorialRatio.lower m) (bounds m).1
  unfold ChebyshevFactorialRatio.den
  positivity

theorem step (m : ℕ) : L (30*m) ≤ 2^(40*m+32768) * L (5*m) := by
  refine combine_upper (d := ChebyshevFactorialRatio.den m) ?_ (bounds m).2 (ChebyshevFactorialRatio.upper m)
  unfold ChebyshevFactorialRatio.den
  positivity

end PrimeFactors.ChebyshevPrimePowers
