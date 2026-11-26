import PrimeFactors.MixedPrefixSample
import PrimeFactors.SingleBaseRepeat
import PrimeFactors.DivisorSecondMoment

/-! Average short-period risk for one uniformly drawn unit, conditional on its
prime product. Each eligible prime pair receives the same probability. -/

namespace PrimeFactors.SingleBasePopulation

open Finset MixedPrefixSample
set_option exponentiation.threshold 8192

/-- A fixed gap e is charged once for each possible gcd with a predecessor.
Positive multiples of d through M have at most M/d possible quotients. -/
theorem gcd_sum {e M : ℕ} (ep : 0<e) (P : Finset ℕ)
    (bounds : ∀ p∈P, 1<p ∧ p-1≤M) :
    ∑ p∈P, e.gcd (p-1) ≤ M*e.divisors.card := by
  let g (p : ℕ) := e.gcd (p-1)
  have into : ∀ p∈P, g p∈e.divisors := fun p _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left ..,ep.ne'⟩
  have local_bound (d : ℕ) (hd : d∈e.divisors) :
      ∑ p∈P.filter (fun p => g p=d), g p ≤ M := by
    let row := P.filter (fun p => g p=d)
    have info {p : ℕ} (hp : p∈row) : 0<p-1 ∧ p-1≤M ∧ d∣p-1 := by
      obtain ⟨pm,eq⟩ := mem_filter.mp hp
      obtain ⟨lo,hi⟩ := bounds p pm
      exact ⟨by omega,hi,eq ▸ Nat.gcd_dvd_right ..⟩
    have dp := Nat.pos_of_mem_divisors hd
    have size : row.card ≤ (Icc 1 (M/d)).card := by
      apply card_le_card_of_injOn (fun p : ℕ => (p-1)/d)
      · intro p hp
        obtain ⟨pos,hi,dvd⟩ := info hp
        exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd pos dvd) dp,Nat.div_le_div_right hi⟩
      · intro p hp q hq eq
        have hp' := info hp; have hq' := info hq
        have he := congrArg (·*d) eq
        dsimp at he
        rw [Nat.div_mul_cancel hp'.2.2,Nat.div_mul_cancel hq'.2.2] at he
        omega
    have cost : row.card*d≤M := (Nat.mul_le_mul_right _ (by simpa [Nat.card_Icc] using size : row.card≤M/d)).trans (Nat.div_mul_le_self ..)
    calc
      _ = ∑ _p∈row, d := sum_congr rfl fun _ hp => (mem_filter.mp hp).2
      _ ≤ M := by simpa using cost
  calc
    _ = ∑ d∈e.divisors, ∑ p∈P.filter (fun p => g p=d), g p := (sum_fiberwise_of_maps_to into g).symm
    _ ≤ ∑ _d∈e.divisors, M := sum_le_sum local_bound
    _ = _ := by simp [mul_comm]

/-- A strict smaller-first sample contains at most half of the weighted square
of the full sum, including when an eligibility test drops some pairs. -/
private theorem half_square (P : Finset ℕ) (S : Finset (ℕ×ℕ)) (f : ℕ → ℕ)
    (valid : ∀ z∈S, z.1∈P ∧ z.2∈P ∧ z.1<z.2) :
    2*(∑ z∈S, f z.1*f z.2) ≤ (∑ p∈P, f p)^2 := by
  let rev := S.image Prod.swap
  let F (z : ℕ×ℕ) := f z.1*f z.2
  have disjoint : Disjoint S rev := by
    apply disjoint_left.mpr
    intro z hz hr
    obtain ⟨y,hy,eq⟩ := mem_image.mp hr
    have h := (valid z hz).2.2; rw [←eq] at h; exact (lt_asymm (valid y hy).2.2 h)
  have sub : S∪rev⊆P×ˢP := by
    intro z hz
    rcases mem_union.mp hz with h|h
    · exact mem_product.mpr ⟨(valid z h).1,(valid z h).2.1⟩
    · obtain ⟨y,hy,rfl⟩ := mem_image.mp h
      exact mem_product.mpr ⟨(valid y hy).2.1,(valid y hy).1⟩
  have eq : ∑ z∈rev, F z = ∑ z∈S, F z := by
    rw [sum_image (fun a _ b _ e => Prod.swap_injective e)]
    apply sum_congr rfl; intro _ _; exact mul_comm ..
  calc
    _ = ∑ z∈S∪rev, F z := by rw [sum_union disjoint,eq,two_mul]
    _ ≤ ∑ z∈P×ˢP, F z := sum_le_sum_of_subset sub
    _ = _ := by rw [sum_product]; dsimp only [F]; simp only [←Finset.mul_sum,←Finset.sum_mul,sq]

private theorem prime_props {p : ℕ} (hp : p∈primes) :
    X≤p-1 ∧ p-1≤2*X ∧ p.Prime := by
  obtain ⟨band,pp⟩ := mem_filter.mp hp
  obtain ⟨lo,hi⟩ := mem_Ico.mp band
  have notp : ¬X.Prime := Nat.Prime.not_prime_pow (by decide : 2≤1023)
  have ne : X≠p := fun eq => notp (eq ▸ pp)
  exact ⟨by omega,by omega,pp⟩

attribute [local irreducible] MixedPrefixSample.primes MixedPrefixSample.ordered

private theorem eligible_props {z : ℕ×ℕ} (hz : z∈eligible) :
    z.1∈primes ∧ z.2∈primes ∧ z.1<z.2 := by
  obtain ⟨h,lt⟩ := mem_filter.mp hz
  have both := mem_ordered.mp h
  exact ⟨both.1,both.2.1,lt⟩

attribute [local irreducible] MixedPrefixSample.eligible

/-- Price all gaps through W on the concrete finite sample. -/
theorem incident_bound (W : ℕ) :
    2*(∑ z∈eligible, ∑ e∈Icc 1 W, e.gcd (z.1-1)*e.gcd (z.2-1)) ≤
      (2*X)^2 * ∑ e∈Icc 1 W, e.divisors.card^2 := by
  rw [sum_comm,mul_sum,mul_sum]
  apply sum_le_sum
  intro e he
  have one := gcd_sum (mem_Icc.mp he).1 primes fun p hp => ⟨(prime_props hp).2.2.one_lt,(prime_props hp).2.1⟩
  calc
    _ ≤ _ := half_square primes eligible (fun p => e.gcd (p-1)) (fun _ => eligible_props)
    _ ≤ ((2*X)*e.divisors.card)^2 := Nat.pow_le_pow_left one _
    _ = _ := mul_pow ..

/-- Conditional on a given modulus, sample uniformly from its units. The
zero-modulus branch is outside the target sample. -/
noncomputable def shortRate (n W : ℕ) : ℚ :=
  if hz : n=0 then 0 else
    letI : NeZero n := ⟨hz⟩
    ((SingleBaseRepeat.repeated n W).card : ℚ) / Fintype.card (ZMod n)ˣ

/-- First draw the two primes uniformly from the eligible sorted pairs and
then draw one unit uniformly for that product. -/
noncomputable def failure (W : ℕ) : ℚ :=
  (∑ z∈eligible, shortRate (z.1*z.2) W) / eligible.card

private theorem rate_bound {z : ℕ×ℕ} (hz : z∈eligible) (W : ℕ) :
    (X:ℚ)^2*shortRate (z.1*z.2) W ≤
      ((∑ e∈Icc 1 W, e.gcd (z.1-1)*e.gcd (z.2-1) : ℕ):ℚ) := by
  obtain ⟨p,q,lt⟩ := eligible_props hz
  obtain ⟨lo,_,pp⟩ := prime_props p
  obtain ⟨lo',_,qp⟩ := prime_props q
  have nz := Nat.mul_ne_zero pp.ne_zero qp.ne_zero
  letI : NeZero (z.1*z.2) := ⟨nz⟩
  have group := SingleBaseRepeat.unit_count pp qp lt.ne
  have size : X^2≤Fintype.card (ZMod (z.1*z.2))ˣ := by rw [group,sq]; exact Nat.mul_le_mul lo lo'
  let a := (SingleBaseRepeat.repeated (z.1*z.2) W).card
  let m := Fintype.card (ZMod (z.1*z.2))ˣ
  have gp : (0:ℚ)<m := by exact_mod_cast (Fintype.card_pos : 0<m)
  have xr : (X:ℚ)^2≤m := by exact_mod_cast size
  have eq : shortRate (z.1*z.2) W=(a:ℚ)/m := by simp only [shortRate,dif_neg nz]; rfl
  rw [eq]
  calc
    _ ≤ (m:ℚ)*(a/m) := mul_le_mul_of_nonneg_right xr (by positivity)
    _ = a := mul_div_cancel₀ _ gp.ne'
    _ ≤ _ := by exact_mod_cast SingleBaseRepeat.elements_bound pp qp lt.ne W

/-- Replace the several conditional denominators by their common lower bound
only after summing the actual per-product conditional probabilities. -/
theorem total_rate (W : ℕ) :
    (∑ z∈eligible, shortRate (z.1*z.2) W) ≤ 2*((∑ e∈Icc 1 W, e.divisors.card^2 : ℕ):ℚ) := by
  have localBound := sum_le_sum (fun z (hz : z∈eligible) => rate_bound hz W)
  rw [←mul_sum,←Nat.cast_sum] at localBound
  have incident := incident_bound W
  have xr : (0:ℚ)<(X:ℚ)^2 := by exact_mod_cast (by decide +kernel : 0<X^2)
  have H : (2:ℚ)*((∑ z∈eligible, ∑ e∈Icc 1 W, e.gcd (z.1-1)*e.gcd (z.2-1) : ℕ):ℚ) ≤
      (2*(X:ℚ))^2*((∑ e∈Icc 1 W, e.divisors.card^2 : ℕ):ℚ) := by exact_mod_cast incident
  apply (le_of_mul_le_mul_left (a:=(X:ℚ)^2) (b:=_) (c:=_) ?_ xr)
  linarith only [localBound,H]

private theorem fraction {W E C : ℕ} (analytic : PrimeCountInput)
    (cost : (∑ e∈Icc 1 W, e.divisors.card^2) ≤ C) (budget : 2^E*2*C*21000000≤2^2046) :
    failure W < 1/(2:ℚ)^E := by
  have den := MixedPrefixSample.denominator analytic
  have pe : (0:ℚ)<eligible.card := by exact_mod_cast (by omega : 0<eligible.card)
  have aggregate := total_rate W
  have cost' : ((∑ e∈Icc 1 W, e.divisors.card^2 : ℕ):ℚ)≤C := by exact_mod_cast cost
  have weight := budget.trans_lt den
  have price : (2:ℚ)^E*2*C<eligible.card := by
    exact_mod_cast (Nat.lt_of_mul_lt_mul_right (by simpa only [mul_comm 21000000] using weight) :
      2^E*2*C<eligible.card)
  rw [failure,div_lt_div_iff₀ pe (by positivity)]
  have scale := mul_le_mul_of_nonneg_left (aggregate.trans (mul_le_mul_of_nonneg_left cost' (by positivity))) (show 0≤(2:ℚ)^E by positivity)
  linarith only [scale,price]

private theorem choose_three (b : ℕ) :
    6*(b+3).choose 3=(b+3)*(b+2)*(b+1) := by
  have eq := Nat.descFactorial_eq_factorial_mul_choose (b+3) 3
  simpa [Nat.descFactorial_succ,Nat.factorial_succ,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using eq.symm

/-- A gap budget reaching the full factor-scale X. -/
theorem full_width {W : ℕ} (cap : W≤X) (count : PrimeCountInput) : failure W<1/(2:ℚ)^970 := by
  apply fraction count (DivisorSecondMoment.binomial 1023 W cap)
  have weight : W*(1023+3).choose 3≤X*179481600 := Nat.mul_le_mul cap (by have := choose_three 1023; omega)
  exact (Nat.mul_le_mul_right 21000000 (Nat.mul_le_mul_left _ weight)).trans (by decide +kernel)

/-- The public balanced interval is [ceil(sqrt(4n)), floor(sqrt(9n/2))]. -/
def balancedWidth (n : ℕ) : ℕ := (9*n/2).sqrt-ceilSqrt (4*n)

private theorem width_limit {z : ℕ×ℕ} (hz : z∈eligible) : balancedWidth (z.1*z.2)≤2^1021 := by
  obtain ⟨p,q,pq⟩ := eligible_props hz
  obtain ⟨pl,_,_⟩ := prime_props p
  obtain ⟨_,qh,_⟩ := prime_props q
  let n := z.1*z.2
  let U := (9*n/2).sqrt
  let L := ceilSqrt (4*n)
  change U-L ≤ 2^1021
  by_cases nonempty : L≤U
  · have lo : 4*n≤L^2 := ceilSqrt_le_iff.mp le_rfl
    have hi : 2*U^2≤9*n := (Nat.mul_le_mul_left 2 (Nat.sqrt_le' _)).trans (Nat.mul_div_le ..)
    have minP : 64≤X := by decide +kernel
    have maxQ : z.2≤2*z.1 := by omega
    have h := (SumSignatureProbability.diameter (p:=z.1) (q:=z.2) (by omega) pq.le maxQ lo hi nonempty).2
    have cutoff : 2*X=8*2^1021 := by decide +kernel
    omega
  · omega

/-- Actual repeat probability when the tested exponent span depends on N. -/
noncomputable def balancedFailure : ℚ :=
  (∑ z∈eligible, shortRate (z.1*z.2) (balancedWidth (z.1*z.2))) / eligible.card

private theorem rate_mono (n : ℕ) {u v : ℕ} (le : u≤v) : shortRate n u≤shortRate n v := by
  by_cases hz : n=0
  · simp only [shortRate,dif_pos hz,le_refl]
  · letI : NeZero n := ⟨hz⟩
    have sub : SingleBaseRepeat.repeated n u⊆SingleBaseRepeat.repeated n v := by
      intro g hg
      obtain ⟨e,he,pow⟩ := SingleBaseRepeat.mem_repeated.mp hg
      exact SingleBaseRepeat.mem_repeated.mpr ⟨e,Icc_subset_Icc_right le he,pow⟩
    simp only [shortRate,dif_neg hz]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast card_le_card sub

/-- With the actual balanced interval at each sampled product, one uniform unit
admits a positive exponent repeat in the interval with probability < 2^(-972). -/
theorem balanced (count : PrimeCountInput) : balancedFailure<1/(2:ℚ)^972 := by
  have major : balancedFailure ≤ failure (2^1021) := div_le_div_of_nonneg_right
    (sum_le_sum fun z hz => rate_mono _ (width_limit (z:=z) hz)) (by positivity)
  apply major.trans_lt
  apply fraction count (DivisorSecondMoment.binomial 1021 (2^1021) le_rfl)
  decide +kernel

/-- Outside that product's repeated-unit set, the known power g^(N+1)
identifies exactly the true sum among the integers of the balanced interval. -/
theorem identify {p q s : ℕ} [NeZero (p*q)] (inSample : (p,q)∈eligible) (g : (ZMod (p*q))ˣ)
    (regular : g∉SingleBaseRepeat.repeated (p*q) (balancedWidth (p*q)))
    (candidate : s∈Icc (ceilSqrt (4*(p*q))) (9*(p*q)/2).sqrt) :
    g^s=g^(p*q+1) ↔ s=p+q := by
  obtain ⟨pm,qm,pq⟩ := eligible_props inSample
  obtain ⟨pl,_,hp⟩ := prime_props pm
  obtain ⟨_,qh,hq⟩ := prime_props qm
  change X≤p-1 at pl
  change q-1≤2*X at qh
  have pp : 0<p := hp.pos
  have balance : q≤2*p := by omega
  obtain ⟨lo,hi⟩ := balanced_factorSum_bounds (p:=p) (q:=q) pq.le balance
  have trueSum : p+q∈Icc (ceilSqrt (4*(p*q))) (9*(p*q)/2).sqrt := mem_Icc.mpr ⟨ceilSqrt_le_iff.mpr lo,Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le (by decide : 0<2)).mpr (by simpa only [mul_comm 2] using hi))⟩
  let gs (_ : Fin 1) := g
  have ok : gs∉SumSignatureProbability.short (ZMod (p*q))ˣ 1 (balancedWidth (p*q)) := by
    intro bad
    obtain ⟨e,range,h⟩ := SumSignatureProbability.mem_short.mp bad
    exact regular (SingleBaseRepeat.mem_repeated.mpr ⟨e,range,h 0⟩)
  simpa only [gs,forall_const] using SumSignatureProbability.identify hp hq pq.ne gs ok candidate trueSum

end PrimeFactors.SingleBasePopulation
