import PrimeFactors.JacobiPeriodSquareClass
import PrimeFactors.SquareAnchorCoverage
import PrimeFactors.FareyWrap

/-! A finite upper fraction for the increasing search through square scales,
counting its actual successful factor sums on the full-width prime-pair sample. -/
namespace PrimeFactors.JacobiSquareClassPopulation

open Finset MixedPrefixSample

/-- The earlier direct decoder recovers the true factor sum at one of the allowed scales. -/
noncomputable def direct (L : ℕ) : Finset (ℕ × ℕ) := by
  classical exact eligible.filter fun z => ∃ t : ℕ, 0 < t ∧ t ≤ L ∧
    predecessorSquareSum (z.1*z.2) t=z.1+z.2

/-- An upper cover of predecessor products of the form t*y² up to H². -/
private def values (H L : ℕ) : Finset ℕ :=
  (range L).biUnion fun i => (Icc 1 ((H^2/(i+1)).sqrt)).image fun y => (i+1)*y^2

private theorem root_cap (H i : ℕ) :
    (((H^2/(i+1)).sqrt : ℕ) : ℝ) ≤ H*(1/Real.sqrt ((i:ℝ)+1)) := by
  let y := (H^2/(i+1)).sqrt
  have hn : y^2*(i+1) ≤ H^2 :=
    (Nat.le_div_iff_mul_le (Nat.succ_pos i)).mp (Nat.sqrt_le' _)
  have hr : (y:ℝ)^2*((i:ℝ)+1) ≤ (H:ℝ)^2 := by exact_mod_cast hn
  have ip : (0:ℝ) < (i:ℝ)+1 := by positivity
  have sq : ((y:ℝ)*Real.sqrt ((i:ℝ)+1))^2 ≤ (H:ℝ)^2 := by
    simpa only [mul_pow, Real.sq_sqrt ip.le] using hr
  rw [mul_one_div]
  apply (le_div_iff₀ (Real.sqrt_pos.mpr ip)).mpr
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp sq

/-- At most 2H sqrt(L) totients occur, before checking primality or squarefreeness. -/
private theorem values_card (H L : ℕ) : ((values H L).card : ℝ) ≤ H*(2*Real.sqrt L) := by
  have count : (values H L).card ≤ ∑ i ∈ range L, (H^2/(i+1)).sqrt := by
    apply card_biUnion_le.trans
    apply sum_le_sum
    intro i _
    exact card_image_le.trans (by simp)
  calc
    _ ≤ ((∑ i ∈ range L, (H^2/(i+1)).sqrt : ℕ) : ℝ) := by exact_mod_cast count
    _ ≤ ∑ i ∈ range L, (H:ℝ)*(1/Real.sqrt ((i:ℝ)+1)) := by
      rw [Nat.cast_sum]; exact sum_le_sum fun i _ => root_cap H i
    _ = (H:ℝ)*∑ i ∈ range L, 1/Real.sqrt ((i:ℝ)+1) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (FareyWrap.reciprocal_sqrt_sum L) (Nat.cast_nonneg H)

attribute [local irreducible] X eligible primes ordered
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

private theorem info {p q : ℕ} (ok : (p,q) ∈ eligible) :
    1 < p ∧ p ≤ q ∧ q ≤ 2*p ∧ p < 2^1024 ∧ q < 2^1024 := by
  rw [eligible,sample] at ok
  obtain ⟨ord,lt⟩ := mem_filter.mp ok
  obtain ⟨pm,qm,_,_,_⟩ := mem_ordered.mp ord
  rw [primes,mem_filter,mem_Ico] at pm qm
  change p < q at lt
  have lo : X ≤ p := pm.1.1
  have pu : p < 2*X := pm.1.2
  have qu : q < 2*X := qm.1.2
  have boundary : 2*X = 2^1024 := by unfold X; decide +kernel
  exact ⟨pm.2.one_lt,lt.le,by omega,by omega,by omega⟩

/-- The event being counted is precisely that the squarefree part of the residual
product is at most L, and can equivalently be stated using the actual decoder. -/
theorem mem_direct_iff {p q c z L : ℕ} (ok : (p,q) ∈ eligible) (free : Squarefree c)
    (period : JacobiPeriodCount.residualProduct p q = c*z^2) : (p,q) ∈ direct L ↔ c ≤ L := by
  classical
  obtain ⟨hp,le,bal,_,_⟩ := info ok
  have least := JacobiPeriodSquareClass.first_scale hp le bal free period
  constructor
  · intro h
    obtain ⟨_,t,tp,tL,hit⟩ := mem_filter.mp h
    have min : c ≤ t := least.2 ⟨tp,hit⟩
    exact min.trans tL
  · intro cL
    exact mem_filter.mpr ⟨ok,c,least.1.1,cL,least.1.2⟩

private theorem cover (L : ℕ) :
    direct L ⊆ eligible.filter (fun z => SquareAnchorCoverage.predProduct z ∈ values (2^1024) L) := by
  classical
  rintro ⟨p,q⟩ hz
  obtain ⟨ok,t,tp,tL,hit⟩ := mem_filter.mp hz
  obtain ⟨hp,le,bal,pu,qu⟩ := info ok
  have pg : 0 < p-1 := Nat.sub_pos_of_lt hp
  have qg : 0 < q-1 := Nat.sub_pos_of_lt (hp.trans_le le)
  have p1 : 1 ≤ p := hp.le
  have q1 : 1 ≤ q := p1.trans le
  have eq := JacobiPeriodScales.sum_iff_square (P:=p-1) (Q:=q-1) pg (Nat.sub_le_sub_right le 1)
    (by simpa only [Nat.sub_add_cancel p1,Nat.sub_add_cancel q1] using bal) tp
  simp only [Nat.sub_add_cancel p1,Nat.sub_add_cancel q1] at eq
  obtain ⟨y,hy⟩ := eq.mp hit
  have positive : t*y^2 ≠ 0 := hy.trans_ne (Nat.mul_pos pg qg).ne'
  have yp : 0 < y := Nat.pos_of_ne_zero (by intro zy; simp [zy] at positive)
  have bound : y^2*t ≤ (2^1024)^2 := calc
    _ = (p-1)*(q-1) := (Nat.mul_comm ..).trans hy
    _ ≤ _ := by rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)
  have root := (Nat.le_sqrt').mpr ((Nat.le_div_iff_mul_le tp).mpr bound)
  have idx : t-1+1=t := Nat.sub_add_cancel tp
  apply mem_filter.mpr
  refine ⟨ok,mem_biUnion.mpr ⟨t-1,mem_range.mpr (by omega),mem_image.mpr ⟨y,?_,?_⟩⟩⟩
  · rw [mem_Icc,idx]; exact ⟨yp,root⟩
  · change (t-1+1)*y^2=(p-1)*(q-1)
    rw [idx,hy]

/-- Exact finite denominator and a uniform divisor bound for each possible totient. -/
theorem direct_fraction : 2^736*(direct (2^40)).card < eligible.card := by
  have root : Real.sqrt (((2^40 : ℕ):ℝ)) = (2^20:ℕ) := by
    rw [show (2^40:ℕ) = (2^20)^2 by decide +kernel, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _)]
  have nvalues : (values (2^1024) (2^40)).card ≤ (2^1024)*(2*(2^20)) := by
    have h := values_card (2^1024) (2^40)
    rw [root] at h
    exact_mod_cast h
  have cap := (card_le_card (cover (2^40))).trans (SquareAnchorCoverage.pair_capacity _)
  have arith : 21000000*(2^736*((2^1024)*(2*(2^20))*2^240)) < 2^2046 := by decide +kernel
  exact Nat.lt_of_mul_lt_mul_left <| (Nat.mul_le_mul_left 21000000
    (Nat.mul_le_mul_left (2^736) (cap.trans (Nat.mul_le_mul_right _ nvalues)))).trans_lt
      (arith.trans ChebyshevPrimeSample.eligible_count)

end PrimeFactors.JacobiSquareClassPopulation
