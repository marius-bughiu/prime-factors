import PrimeFactors.WeightedCrowdingEstimates

/-! Explicit arithmetic for the five distinct multipliers from 512 to 516. -/
namespace PrimeFactors.FiveWeightEstimates
open Finset Real WeightedCrowdingEstimates
set_option exponentiation.threshold 8192
set_option maxRecDepth 4096

private abbrev U : ℕ := 2^1024
private abbrev A : ℕ := 3*U/4
private abbrev B : ℕ := 7*U/8

/-- A common upper bound for primes at the same weight in a bucket. -/
abbrev cap : ℕ := 2^512/5600+1
/-- The interval from 384 U to 451.5 U has this many buckets of length 2^516. -/
abbrev bins : ℕ := 135*2^507

private theorem log_bounds {x : ℕ} (lo : 2^1023≤x) (hi : x≤2^1024) :
    (700:ℝ)≤log x-11/10 ∧ log x-1≤710 := by
  have positive : (0:ℝ)<x := by
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0<(2:ℕ)^1023) lo)
  have low := log_le_log (by positivity : 0<(2:ℝ)^1023) (by exact_mod_cast lo : (2:ℝ)^1023≤x)
  have high := log_le_log positive (by exact_mod_cast hi : (x:ℝ)≤2^1024)
  rw [log_pow] at low high
  norm_num only [Nat.cast_ofNat] at low high
  constructor
  · linarith only [low,log_two_gt_d9]
  · linarith only [high,log_two_lt_d9]

private theorem endpoint_difference {a b u l r k p : ℕ}
    (left : 700*l≤a) (right : b≤710*r) (split : l+k=r) (incl : k≤p)
    (ends : 710*a+80*u=700*b) : 2*u≤12425*p := by omega

/-- Dusart (6.6) gives at least 2 U / 12425 primes in the closed public pool. -/
theorem population (dusart : Dusart) : 2*U ≤ 12425*WeightedPrimeCrowding.pool.card := by
  have la := (log_bounds (x:=A) (by decide +kernel) (by decide +kernel)).1
  have lb := log_bounds (x:=B) (by decide +kernel) (by decide +kernel)
  have upper := (le_div_iff₀ ((by norm_num : (0:ℝ)<700).trans_le la)).mp
    (dusart A (by decide +kernel)).2
  have pos {t : ℝ} (h : 700≤t-11/10) : 0<t-1 := by linarith
  have lower := (div_le_iff₀ (pos lb.1)).mp (dusart B (by decide +kernel)).1
  have left : 700*A.primeCounting≤A := by
    have h := (mul_le_mul_of_nonneg_left la (Nat.cast_nonneg A.primeCounting)).trans upper
    rw [mul_comm] at h
    exact_mod_cast h
  have right : B≤710*B.primeCounting := by
    have h := lower.trans (mul_le_mul_of_nonneg_left lb.2 (Nat.cast_nonneg B.primeCounting))
    rw [mul_comm] at h
    exact_mod_cast h
  have split := count_eq A B (by decide +kernel)
  have pool_eq : WeightedPrimeCrowding.pool=(Icc A B).filter Nat.Prime := by
    unfold A B U
    exact WeightedPrimeCrowding.pool_def
  have incl : ((Ioc A B).filter Nat.Prime).card≤WeightedPrimeCrowding.pool.card := by
    rw [pool_eq]
    exact card_le_card (filter_subset_filter Nat.Prime Ioc_subset_Icc_self)
  have endpts : 710*A+80*U=700*B := by decide +kernel
  exact endpoint_difference left right split incl endpts

/-- Brun–Titchmarsh bounds the open-left interval; the closed interval gains
at most the prime at n. Here 507 log 2 > 350 and 2*2^507/350 = 2^512/5600. -/
theorem short_intervals (bt : BrunTitchmarsh) (n : ℕ) (hn : A≤n) :
    ((Icc n (n+2^507)).filter Nat.Prime).card ≤ cap := by
  have hn' := (by decide +kernel : 0<A).trans_le hn
  have bound := bt n (2^507) hn' (by decide +kernel)
  have big : (350:ℝ)≤log (2^507:ℕ) := by
    rw [Nat.cast_pow,Nat.cast_ofNat,log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [log_two_gt_d9]
  let k := ((Ioc n (n+2^507)).filter Nat.Prime).card
  have counts := count_eq n (n+2^507) (by omega)
  change n.primeCounting + k = (n+2^507).primeCounting at counts
  have kc : (k:ℝ)<2*((2^507:ℕ):ℝ)/log (2^507:ℕ) := by
    rw [←counts,Nat.cast_add,add_sub_cancel_left] at bound
    exact bound
  have prod := (lt_div_iff₀ ((by norm_num : (0:ℝ)<350).trans_le big)).mp kc
  have small := (mul_le_mul_of_nonneg_left big (Nat.cast_nonneg k)).trans_lt prod
  have product : k*350 < 2*2^507 := by exact_mod_cast small
  have rounded : k≤2^512/5600 := by omega
  have incl : (Icc n (n+2^507)).filter Nat.Prime ⊆ insert n ((Ioc n (n+2^507)).filter Nat.Prime) := by
    intro p hp
    obtain ⟨mem,pr⟩ := mem_filter.mp hp
    obtain ⟨lo,hi⟩ := mem_Icc.mp mem
    rcases lo.eq_or_lt with eq|lt
    · exact mem_insert.mpr (Or.inl eq.symm)
    · exact mem_insert.mpr (Or.inr (mem_filter.mpr ⟨mem_Ioc.mpr ⟨lt,hi⟩,pr⟩))
  exact ((card_le_card incl).trans (card_insert_le _ _)).trans (Nat.succ_le_succ rounded)

/-- Numerical end of the collision argument. A 50-fold upper bound on the number
of ordered witnesses for a product already gives more than 2^1503 products. -/
theorem product_lower_bound {points total diagonal hits products : ℕ}
    (density : 10*U ≤ 12425*points) (energy : points^2≤bins*total)
    (same : diagonal≤points*cap) (partition : diagonal+hits=total)
    (copies : hits≤50*products) : 2^1503<products := by
  let floorPoints := 10*U/12425
  have enough : floorPoints≤points := by dsimp only [floorPoints]; omega
  have slack : bins*(cap+2^495)≤floorPoints := by decide +kernel
  have weighted : bins*(points*(cap+2^495))≤bins*total := calc
    _ = (bins*(cap+2^495))*points := by ring
    _ ≤ points*points := Nat.mul_le_mul_right _ (slack.trans enough)
    _ ≤ _ := by simpa only [sq] using energy
  have all := Nat.le_of_mul_le_mul_left weighted (by decide +kernel : 0<bins)
  rw [Nat.mul_add] at all
  have count : points*2^495≤hits := by omega
  have minimum := (Nat.mul_le_mul_right (2^495) enough).trans count
  have lower : 50*2^1503<floorPoints*2^495 := by decide +kernel
  omega

end PrimeFactors.FiveWeightEstimates
