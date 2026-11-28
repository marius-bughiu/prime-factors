import PrimeFactors.CircleMarkEarlyReadout
import PrimeFactors.CircleMarkStoppingPrecision

/-! Sampling the probability of an early hit on a fixed product. Each draw is
uniform on the Jacobi-negative target classes and stops at the first hit or at
a public cutoff. The precision bounds apply to the empirical hit frequency
divided by the cutoff. -/

namespace PrimeFactors.CircleMarkCappedSampling

open Finset CircleMarkTargetFrequency CircleMarkEarlyReadout CircleMarkStoppingPrecision
open scoped Classical BigOperators
open private PrimeFactors.CircleMarkStoppingPrecision.split_draw from PrimeFactors.CircleMarkStoppingPrecision

/-- One uniform draw is a single eligible residue class at the product. -/
abbrev Draw (n : ℕ) [NeZero n] := ↥(targets n)

/-- The observable records whether one of the first L coordinates hit. -/
noncomputable def flag (n L : ℕ) [NeZero n] (t : Draw n) : ℚ :=
  if t.val ∈ hits n (Icc 1 L) then 1 else 0

theorem flag_mean (n L : ℕ) [NeZero n] :
    (𝔼 t : Draw n, flag n L t) = rate n (Icc 1 L) := by
  rw [Fintype.expect_eq_sum_div_card, rate, Fintype.card_coe]
  congr 1
  have subset : (targets n).filter (fun t => t ∈ hits n (Icc 1 L)) = hits n (Icc 1 L) := by
    ext t
    exact ⟨fun h => (mem_filter.mp h).2,fun h => mem_filter.mpr ⟨(mem_filter.mp h).1,h⟩⟩
  change (∑ t ∈ (targets n).attach, (if t.val ∈ hits n (Icc 1 L) then (1:ℚ) else 0)) = _
  rw [sum_attach (targets n) (fun t => if t ∈ hits n (Icc 1 L) then (1:ℚ) else 0),
    sum_boole, subset]

private theorem draws_nonempty {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) : Nonempty (Draw (p*q)) := by
  have P := hp.out.two_le
  have Q := hq.out.two_le
  have total := (counts diff op oq ∅).1
  have non : (targets (p*q)).Nonempty := card_pos.mp (by
    rw [total]
    have pp : 0<(p-1)/2 := by omega
    have qq : 0<(q-1)/2 := by omega
    positivity)
  obtain ⟨t,ht⟩ := non
  exact ⟨⟨t,ht⟩⟩

/-- Averaging these per-target scores is the observed fraction of hits divided by L. -/
noncomputable def score (n L : ℕ) [NeZero n] (t : Draw n) : ℚ := flag n L t / L

/-- Exact mean squared error on the full Cartesian space of T independent
uniform eligible targets, sampled with replacement. -/
theorem error {p q L T : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q) (op : p≠2) (oq : q≠2)
    (lp : 0<L) (tp : 0<T) (pl : L≤(p-1)/2) (ql : L≤(q-1)/2) :
    meanSquare (score (p*q) L) (early (p*q)) T =
      early (p*q) * (1-L*early (p*q)) / (L*T) := by
  letI := draws_nonempty diff op oq
  let n := p*q
  let d := early n
  have Ln : (L:ℚ) ≠ 0 := by exact_mod_cast lp.ne'
  have avg : (𝔼 t : Draw n, flag n L t) = L*d :=
    (flag_mean n L).trans (flat_prefix diff op oq pl ql)
  have first : (𝔼 t : Draw n, score n L t) = d := by
    simp only [score,←expect_div,avg]
    field_simp
  have expand (t : Draw n) : (score n L t - d)^2 =
      flag n L t * (1/(L:ℚ)^2-2*d/L) + d^2 := by
    simp only [score,flag]
    split <;> field_simp
    ring
  rw [sample_variance _ first tp]
  change (𝔼 t : Draw n, (score n L t-d)^2)/T=d*(1-L*d)/(L*T)
  simp only [expand,expect_add_distrib,←expect_mul,Fintype.expect_const,avg]
  field_simp
  ring

/-- Number of scalar gcds used before the cap. The test at k+1 is performed
exactly when the prefix through k has missed. -/
noncomputable def cost (n L : ℕ) [NeZero n] (t : Draw n) : ℚ :=
  ∑ k ∈ range L, (1 - flag n k t)

private theorem sum_indices (L : ℕ) : (∑ k ∈ range L, (k:ℚ)) = L*(L-1)/2 := by
  induction L with
  | zero => norm_num
  | succ L ih => rw [sum_range_succ, ih, Nat.cast_succ]; ring

/-- Exact expected scalar gcd count when the search stops on success. -/
theorem expected_cost {p q L : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q) (op : p≠2) (oq : q≠2)
    (pl : L≤(p-1)/2) (ql : L≤(q-1)/2) :
    (𝔼 t : Draw (p*q), cost (p*q) L t) = L - early (p*q)*L*(L-1)/2 := by
  letI := draws_nonempty diff op oq
  simp only [cost,expect_sum_comm,expect_sub_distrib,Fintype.expect_const,flag_mean]
  have flat (k) (hk : k ∈ range L) : rate (p*q) (Icc 1 k) = k*early (p*q) :=
    flat_prefix diff op oq ((mem_range.mp hk).le.trans pl) ((mem_range.mp hk).le.trans ql)
  rw [sum_congr rfl (fun k hk => congrArg (fun x : ℚ => 1-x) (flat k hk)),sum_sub_distrib,
    sum_const,card_range,nsmul_eq_mul,mul_one,←sum_mul,sum_indices]
  ring


set_option exponentiation.threshold 4096

private theorem full_half {r L : ℕ} (lo : 2^1023 ≤ r) (cap : L ≤ 2^256) :
    L ≤ (r-1)/2 := by
  have small : 2*(2:ℕ)^256+1 ≤ 2^1023 := by decide +kernel
  omega

/-- At these widths d exceeds 2^-1023, while even the full capped prefix hits
less than half the target population. -/
theorem full_probabilities {p q L : ℕ} [Fact p.Prime] [Fact q.Prime]
    (lo : 2^1023 ≤ p) (order : p < q) (hi : q < 2^1024) (cap : L ≤ 2^256) :
    1/(2:ℚ)^1023 < early (p*q) ∧ (L:ℚ)*early (p*q) < 1/2 := by
  have pgt := (by decide +kernel : 2<2^1023).trans_le lo
  rw [early_eq order.ne pgt.ne' (pgt.trans order).ne']
  have localBounds (r : ℕ) (rlo : 2^1023≤r) (rhi : r<2^1024) :
      1/(2:ℚ)^1024 < 1/((r:ℚ)-1) ∧ 1/((r:ℚ)-1) < 1/(2:ℚ)^1021 := by
    have lower : (2:ℚ)^1023 ≤ r := by exact_mod_cast rlo
    have upper : (r:ℚ) < 2^1024 := by exact_mod_cast rhi
    have short : (2:ℚ)^1021 < (r:ℚ)-1 :=
      calc (2:ℚ)^1021 < 2^1023-1 := by norm_num
           _ ≤ _ := sub_le_sub_right lower _
    exact ⟨one_div_lt_one_div_of_lt (by linarith only [short,show (0:ℚ)<2^1021 by positivity])
      (by linarith only [upper]),one_div_lt_one_div_of_lt (by positivity) short⟩
  obtain ⟨a,b⟩ := localBounds p lo (order.trans hi)
  obtain ⟨c,e⟩ := localBounds q (lo.trans order.le) hi
  constructor
  · calc (1:ℚ)/2^1023 = 1/2^1024 + 1/2^1024 := by norm_num
         _ < _ := add_lt_add a c
  · calc
      _ ≤ (2:ℚ)^256 * (1/2^1021 + 1/2^1021) := by
        apply mul_le_mul (by exact_mod_cast cap) (add_le_add b.le e.le)
        · linarith only [a,c,show (0:ℚ)<1/2^1024 by positivity]
        · positivity
      _ < 1/2 := by norm_num

/-- The expected scalar gcd cost per target exceeds three quarters of the full
cap even though a successful draw stops immediately. -/
theorem full_expected_cost {p q L : ℕ} [Fact p.Prime] [Fact q.Prime]
    (lo : 2^1023 ≤ p) (order : p < q) (hi : q < 2^1024) (lp : 0<L) (cap : L ≤ 2^256) :
    3*(L:ℚ)/4 < 𝔼 t : Draw (p*q), cost (p*q) L t := by
  have pgt := (by decide +kernel : 2<2^1023).trans_le lo
  rw [expected_cost order.ne pgt.ne' (pgt.trans order).ne'
    (full_half lo cap) (full_half (lo.trans order.le) cap)]
  obtain ⟨d,θ⟩ := full_probabilities lo order hi cap
  have pos : 0<(L:ℚ) := by exact_mod_cast lp
  have upper := mul_lt_mul_of_pos_right θ pos
  have saved := mul_nonneg pos.le ((by positivity : (0:ℚ)≤1/2^1023).trans d.le)
  nlinarith only [upper,saved]

/-- Total work averaged over all ordered tuples of eligible targets. -/
theorem total_expected_cost (n : ℕ) [NeZero n] [Nonempty (Draw n)] (L T : ℕ) :
    (𝔼 s : Fin T → Draw n, ∑ j, cost n L (s j)) = T * (𝔼 t : Draw n, cost n L t) := by
  induction T with
  | zero => simp
  | succ k ih =>
    rw [PrimeFactors.CircleMarkStoppingPrecision.split_draw _ (fun a t => cost n L a + ∑ j, cost n L (t j))
      (fun _ => Fin.sum_univ_succ _)]
    simp only [expect_add_distrib,Fintype.expect_const,ih,Nat.cast_succ]
    ring

/-- For the empirical hit fraction divided by L, RMS error below 2^-2046
requires T·L > 2^3068. With early stopping, the expected total number of scalar
gcds across T draws is greater than 3·2^3066. -/
theorem full_precision {p q L T : ℕ} [Fact p.Prime] [Fact q.Prime]
    (lo : 2^1023 ≤ p) (order : p < q) (hi : q < 2^1024) (lp : 0<L) (tp : 0<T) (cap : L ≤ 2^256)
    (rms : Real.sqrt ((meanSquare (score (p*q) L) (early (p*q)) T : ℚ) : ℝ) < 1/(2:ℝ)^2046) :
    2^3068 < T*L ∧ 3*(2:ℚ)^3066 < 𝔼 s : Fin T → Draw (p*q), ∑ j, cost (p*q) L (s j) := by
  let d := early (p*q)
  have pgt := (by decide +kernel : 2<2^1023).trans_le lo
  have mse := error order.ne pgt.ne' (pgt.trans order).ne' lp tp
    (full_half lo cap) (full_half (lo.trans order.le) cap)
  have sqR := (Real.sqrt_lt' (by positivity : (0:ℝ)<1/2^2046)).mp rms
  have sqQ : meanSquare (score (p*q) L) (early (p*q)) T < ((1:ℚ)/2^2046)^2 := by
    apply (Rat.cast_lt (K:=ℝ)).mp
    push_cast
    exact sqR
  rw [mse] at sqQ
  have Lp : 0<(L:ℚ) := by exact_mod_cast lp
  have Tp : 0<(T:ℚ) := by exact_mod_cast tp
  have work := (div_lt_iff₀ (mul_pos Lp Tp)).mp sqQ
  obtain ⟨dlo,θ⟩ := full_probabilities lo order hi cap
  have signal : (1:ℚ)/2^1024 < d*(1-L*d) := by
    calc (1:ℚ)/2^1024 = (1/2^1023)*(1/2) := by norm_num
         _ < d*(1/2) := mul_lt_mul_of_pos_right dlo (by norm_num)
         _ < _ := mul_lt_mul_of_pos_left (by dsimp [d]; linarith only [θ])
           ((by positivity : (0:ℚ)<1/2^1023).trans dlo)
  have budget : (2:ℚ)^3068 < T*L := by
    rw [show (2:ℚ)^3068 = (1/2^1024)/((1/2^2046)^2) by norm_num]
    apply (div_lt_iff₀ (by positivity)).mpr
    simpa only [mul_comm,mul_left_comm,mul_assoc] using signal.trans work
  refine ⟨by exact_mod_cast budget,?_⟩
  letI := draws_nonempty order.ne pgt.ne' (pgt.trans order).ne'
  rw [total_expected_cost]
  have final := mul_lt_mul_of_pos_left (full_expected_cost lo order hi lp cap) Tp
  have lower := mul_lt_mul_of_pos_left budget (by norm_num : (0:ℚ)<3/4)
  rw [show (3:ℚ)/4*2^3068 = 3*2^3066 by norm_num] at lower
  linarith only [lower,final]

end PrimeFactors.CircleMarkCappedSampling
