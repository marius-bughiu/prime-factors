import PrimeFactors.SingleBasePopulation

/-! Draw a public integer between 1 and 2^1152 once. Count failures when that
same integer is reused across the finite sample of eligible prime products. -/

namespace PrimeFactors.ReusableSumBase
open Finset MixedPrefixSample SingleBasePopulation
set_option exponentiation.threshold 8192

/-- A nonunit gives a gcd; only units with a short positive period are charged. -/
def Repeats (g n W : ℕ) : Prop :=
  g.Coprime n ∧ ∃ e∈Icc 1 W, (g : ZMod n)^e=1

noncomputable def badSeeds (K n W : ℕ) : Finset ℕ := by
  classical exact (Icc 1 K).filter (fun g => Repeats g n W)

/-- Since all seeds fit below n, reduction to units counts each bad base at most once. -/
theorem seed_injection {K n W : ℕ} [NeZero n] (fits : K<n) :
    (badSeeds K n W).card ≤ (SingleBaseRepeat.repeated n W).card := by
  classical
  let unit (g : ℕ) := if h : g.Coprime n then ZMod.unitOfCoprime g h else 1
  apply card_le_card_of_injOn unit
  · intro g hg
    obtain ⟨hc,e,he,pow⟩ : Repeats g n W := (mem_filter.mp hg).2
    refine SingleBaseRepeat.mem_repeated.mpr ⟨e,he,Units.ext ?_⟩
    simpa only [unit,dif_pos hc,Units.val_pow_eq_pow_val,ZMod.coe_unitOfCoprime,Units.val_one] using pow
  · intro g hg h hh same
    have info {j : ℕ} (hj : j∈badSeeds K n W) : j.Coprime n ∧ j<n :=
      ⟨((mem_filter.mp hj).2 : Repeats j n W).1,((mem_Icc.mp (mem_filter.mp hj).1).2).trans_lt fits⟩
    have gv := info hg
    have hv := info hh
    have e := congrArg (fun w : (ZMod n)ˣ => (w : ZMod n).val) same
    simpa only [unit,dif_pos gv.1,dif_pos hv.1,ZMod.coe_unitOfCoprime,
      ZMod.val_natCast_of_lt gv.2,ZMod.val_natCast_of_lt hv.2] using e

attribute [local irreducible] MixedPrefixSample.ordered

private theorem bounds {z : ℕ×ℕ} (hz : z∈eligible) :
    2^1152<z.1*z.2 ∧ z.1*z.2<2^2048 := by
  have hzOrd : z∈ordered (fun _ => True) := (mem_filter.mp hz).1
  have both := mem_ordered.mp hzOrd
  have pmax := (mem_Ico.mp (mem_filter.mp both.1).1).2
  have qmax := (mem_Ico.mp (mem_filter.mp both.2.1).1).2
  exact ⟨(by decide +kernel : 2^1152<2*X^2).trans_le both.2.2.2.1,
    (Nat.mul_lt_mul_of_lt_of_lt pmax qmax).trans_eq (by decide +kernel)⟩

attribute [local irreducible] MixedPrefixSample.eligible

private theorem row {z : ℕ×ℕ} (hz : z∈eligible) :
    let n := z.1*z.2
    ((badSeeds (2^1152) n (balancedWidth n)).card : ℚ) ≤ 2^2048*shortRate n (balancedWidth n) := by
  let n := z.1*z.2
  obtain ⟨lo,hi⟩ := bounds hz
  have nz : n≠0 := Nat.ne_zero_of_lt lo
  letI : NeZero n := ⟨nz⟩
  let a := (SingleBaseRepeat.repeated n (balancedWidth n)).card
  let m := Fintype.card (ZMod n)ˣ
  have gr : (0:ℚ)<m := by exact_mod_cast (Fintype.card_pos : 0<m)
  have mlim : m < 2^2048 :=
    (ZMod.card_units_eq_totient n).le.trans_lt ((Nat.totient_le n).trans_lt hi)
  have lim : (m:ℚ)≤2^2048 := by exact_mod_cast mlim.le
  have rr : shortRate n (balancedWidth n)=(a:ℚ)/m := by simp only [shortRate,dif_neg nz]; rfl
  change ((badSeeds _ n _).card:ℚ) ≤ _
  calc
    _ ≤ (a:ℚ) := by exact_mod_cast seed_injection (W:=balancedWidth n) lo
    _ = (m:ℚ)*(a/m) := (mul_div_cancel₀ _ gr.ne').symm
    _ ≤ 2^2048*shortRate n (balancedWidth n) := by
      rw [rr]; exact mul_le_mul_of_nonneg_right lim (div_nonneg (Nat.cast_nonneg a) gr.le)

/-- Count failed (seed, pair) draws, charging any short-period unit conservatively. -/
noncomputable def incidents :=
  ∑ z∈eligible, (badSeeds (2^1152) (z.1*z.2) (balancedWidth (z.1*z.2))).card

private theorem incident_bound (count : PrimeCountInput) : incidents < 2^1076*eligible.card := by
  have den := MixedPrefixSample.denominator count
  have pos : (0:ℚ)<eligible.card := by exact_mod_cast (by omega : 0<eligible.card)
  have rate := balanced count
  rw [balancedFailure,div_lt_div_iff₀ pos (by positivity),one_mul] at rate
  have scale := mul_lt_mul_of_pos_left rate (by positivity : 0<(2:ℚ)^1076)
  have raw := sum_le_sum fun z (hz : z∈eligible) => row hz
  change (∑ z∈eligible, ((_ : ℕ):ℚ)) ≤ ∑ z∈eligible, 2^2048*shortRate _ _ at raw
  rw [←mul_sum,←Nat.cast_sum] at raw
  change (incidents:ℚ) ≤ _ at raw
  have final : (incidents:ℚ) < (2:ℚ)^1076*eligible.card := by
    apply raw.trans_lt
    have eq : (2:ℚ)^2048=2^1076*2^972 := by rw [←pow_add]
    rw [eq,mul_assoc]
    simpa only [mul_comm _ ((2:ℚ)^972)] using scale
  exact_mod_cast final

attribute [local irreducible] incidents

/-- A seed and pair chosen independently fail with probability strictly below 2^-76. -/
theorem raw_failure (count : PrimeCountInput) :
    2^76*incidents < 2^1152*eligible.card := by
  have h := Nat.mul_lt_mul_of_pos_left (incident_bound count) (by decide +kernel : 0<2^76)
  simpa only [←Nat.mul_assoc,show (2:ℕ)^76*2^1076=2^1152 by decide +kernel] using h

noncomputable def badPairs (g : ℕ) : Finset (ℕ×ℕ) := by
  classical exact eligible.filter fun z => Repeats g (z.1*z.2) (balancedWidth (z.1*z.2))

private def heavy {α : Type*} (S : Finset α) (P M : ℕ) (f : α → ℕ) : Finset α :=
  S.filter (fun a => P≤M*f a)

-- Keep the kernel from evaluating the entire finite population when it converts a
-- closed natural inequality. The value and its exact certificate travel together.
private opaque threshold : {M : ℕ // M=2^38} := ⟨_,rfl⟩

/-- Seeds whose short-period events touch at least a 2^-38 fraction of all eligible pairs. -/
noncomputable def heavySeeds : Finset ℕ :=
  heavy (Icc 1 (2^1152)) eligible.card threshold.1 (fun g => (badPairs g).card)

theorem mem_heavySeeds (g : ℕ) : g∈heavySeeds ↔
    g∈Icc 1 (2^1152) ∧ eligible.card ≤ 2^38*(badPairs g).card := by
  change _ ∈ filter _ _ ↔ _
  rw [mem_filter,threshold.2]

private theorem transpose : ∑ g∈Icc 1 (2^1152), (badPairs g).card = incidents := by
  classical
  unfold incidents badPairs badSeeds
  simp only [card_filter]; rw [sum_comm]

private theorem finite_markov {α : Type*} (S : Finset α) (P M : ℕ) (f : α → ℕ) :
    (heavy S P M f).card*P ≤ M*(∑ a∈S, f a) := by
  let charged := heavy S P M f
  calc
    _ = ∑ _a∈charged, P := by simp only [sum_const,nsmul_eq_mul,Nat.cast_id,charged]
    _ ≤ ∑ a∈charged, M*f a := sum_le_sum fun _ ha => (mem_filter.mp ha).2
    _ ≤ ∑ a∈S, M*f a := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => Nat.zero_le _)
    _ = _ := (mul_sum ..).symm

private theorem markov (M : ℕ) :
    (heavy (Icc 1 (2^1152)) eligible.card M (fun g => (badPairs g).card)).card*eligible.card
      ≤ M*incidents :=
  (finite_markov (Icc 1 (2^1152)) eligible.card M (fun g => (badPairs g).card)).trans_eq
    (congrArg (fun x : ℕ => M*x) transpose)

private theorem seed_limit (M : ℕ) (is38 : M=2^38) (count : PrimeCountInput) :
    M*(heavy (Icc 1 (2^1152)) eligible.card M (fun g => (badPairs g).card)).card < 2^1152 := by
  have mp : 0<M := is38 ▸ (by decide +kernel)
  have rare := (markov M).trans_lt (Nat.mul_lt_mul_of_pos_left (incident_bound count) mp)
  have eq : M*2^1076=2^1114 := by rw [is38,←pow_add]
  rw [←Nat.mul_assoc,eq] at rare
  have h := Nat.mul_lt_mul_of_pos_left (Nat.lt_of_mul_lt_mul_right rare) mp
  exact h.trans_eq (by rw [is38,←pow_add])

/-- Strictly fewer than a 2^-38 fraction of the 2^1152 seeds are heavy. -/
theorem reusable (count : PrimeCountInput) : 2^38*heavySeeds.card < 2^1152 :=
  (congrArg (fun M : ℕ => M*heavySeeds.card) threshold.2.symm).trans_lt
    (seed_limit threshold.1 threshold.2 count)

/-- On a good seed–product pair, the gcd is proper or the known modular power
identifies exactly the true sum among all candidates in the public interval. -/
theorem usable {p q g : ℕ} [NeZero (p*q)] (hz : (p,q)∈eligible)
    (hg : g∈Icc 1 (2^1152)) (good : (p,q)∉badPairs g) :
    (1<g.gcd (p*q) ∧ g.gcd (p*q)<p*q ∧ g.gcd (p*q)∣p*q) ∨
      ∃ hc : g.Coprime (p*q), ∀ s∈Icc (ceilSqrt (4*(p*q))) (9*(p*q)/2).sqrt,
        (ZMod.unitOfCoprime g hc)^s=(ZMod.unitOfCoprime g hc)^(p*q+1) ↔ s=p+q := by
  classical
  by_cases hc : g.Coprime (p*q)
  · right
    refine ⟨hc,fun s hs => identify hz _ ?_ hs⟩
    intro rep
    obtain ⟨e,he,hpow⟩ := SingleBaseRepeat.mem_repeated.mp rep
    apply good
    refine mem_filter.mpr ⟨hz,hc,e,he,?_⟩
    simpa only [Units.val_pow_eq_pow_val,ZMod.coe_unitOfCoprime,Units.val_one] using
      congrArg (fun u : (ZMod (p*q))ˣ => (u:ZMod (p*q))) hpow
  · left
    have gp := (mem_Icc.mp hg).1
    have glt := (mem_Icc.mp hg).2.trans_lt (bounds hz).1
    exact ⟨by have := Nat.gcd_pos_of_pos_left (p*q) gp; change g.gcd (p*q) ≠ 1 at hc; omega,
      (Nat.gcd_le_left _ gp).trans_lt glt,Nat.gcd_dvd_right ..⟩

end PrimeFactors.ReusableSumBase
