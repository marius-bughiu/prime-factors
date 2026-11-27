import PrimeFactors.SixTraceBudget
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Complex.ExponentialBounds

/-! Discretizing an explicit Selberg integral at the centers 3p/2.
The analytic premise is Theorem 1 of Cully-Hugill and Dudek at a single
pair (U,δ); the paper proves the estimate assuming RH. -/
namespace PrimeFactors.MeanSquarePrimePartners
open MeasureTheory
open InteriorBatchPopulation

set_option exponentiation.threshold 8192
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

abbrev H : ℕ := 2^512
noncomputable abbrev δ : ℝ := 1 / H

/-- The cap 2U exceeds every endpoint in the integral on [1,U]. -/
noncomputable def window (x z : ℝ) : Finset ℕ :=
  (Finset.Icc 0 (2*U)).filter (fun q => q.Prime ∧ x < q ∧ q ≤ z)

noncomputable def mass (x z : ℝ) : ℝ := ∑ q ∈ window x z, Real.log q

noncomputable def center (p : ℕ) : ℝ := 3*(p:ℝ)/2
noncomputable def slab (p : ℕ) : Set ℝ := Set.Ico (center p) (center p+1)
noncomputable def partners (p : ℕ) := window (center p) (center p+H+1)
noncomputable def poor := InteriorBatchPopulation.interior.filter (fun p => (partners p).card < 2^501)
noncomputable def errorSq (t : ℝ) := (mass t (t+δ*t)-δ*t)^2

/-- One specialization of the published estimate for the Chebyshev θ function. -/
def SelbergEstimate : Prop :=
  IntegrableOn errorSq (Set.Icc 1 (U:ℝ)) ∧
    (∫ t in Set.Icc 1 (U:ℝ), errorSq t) < 202*δ*(U:ℝ)^2*(Real.log U)^2

attribute [local irreducible] SixTraceBudget.population SixTraceBudget.successes neighbors window mass partners poor errorSq InteriorBatchPopulation.interior firstPrimes

private theorem interior_bounds {p : ℕ} (hp : p ∈ InteriorBatchPopulation.interior) :
    79*(U/128) ≤ p ∧ p ≤ 82*(U/128) ∧ p.Prime := by
  obtain ⟨h, prime⟩ := Finset.mem_filter.mp (by simpa only [InteriorBatchPopulation.interior,firstPrimes] using hp)
  exact ⟨(Finset.mem_Icc.mp h).1,(Finset.mem_Icc.mp h).2,prime⟩

private theorem slab_bounds {p : ℕ} (hp : p ∈ InteriorBatchPopulation.interior)
    {t : ℝ} (ht : t ∈ slab p) : (7:ℝ)/8*U ≤ t ∧ t ≤ U := by
  obtain ⟨lo,hi,_⟩ := interior_bounds hp
  have pl : ((79*(U/128):ℕ):ℝ) ≤ p := by exact_mod_cast lo
  have ph : (p:ℝ) ≤ ((82*(U/128):ℕ):ℝ) := by exact_mod_cast hi
  obtain ⟨tl,th⟩ := ht
  simp only [center] at tl th
  constructor
  · calc
      _ ≤ 3*(((79*(U/128):ℕ):ℝ))/2 := by norm_num [U]
      _ ≤ _ := le_trans (by linarith only [pl]) tl
  · calc
      t ≤ 3*((82*(U/128):ℕ):ℝ)/2+1 := by linarith only [th,ph]
      _ ≤ _ := by norm_num [U]

private theorem log_bound {q : ℕ} (hq : q≤2*U) (pos : 0<q) : Real.log q ≤ 768 := by
  have bound : (q:ℝ) ≤ (2:ℝ)^1025 := by exact_mod_cast hq
  have step := Real.log_le_log (by exact_mod_cast pos) bound
  rw [Real.log_pow] at step
  refine step.trans ?_
  apply le_trans (mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (by positivity))
  norm_num

private theorem large_error {p : ℕ} (hp : p ∈ poor) {t : ℝ} (ht : t∈slab p) :
    (2:ℝ)^1022 ≤ errorSq t := by
  obtain ⟨member,small⟩ := Finset.mem_filter.mp (by simpa only [poor] using hp)
  obtain ⟨tl,tu⟩ := slab_bounds member ht
  have scale : δ*(U:ℝ) = H := by norm_num [δ,H,U]
  have incl : window t (t+δ*t) ⊆ partners p := by
    intro q hq
    rw [partners,window]
    obtain ⟨bounds,prime,lo,hi⟩ := Finset.mem_filter.mp (by simpa only [window] using hq)
    have upper := mul_le_mul_of_nonneg_left tu (by positivity : 0≤δ)
    rw [scale] at upper
    exact Finset.mem_filter.mpr ⟨bounds,prime,lt_of_le_of_lt ht.1 lo,hi.trans (by linarith only [ht.2,upper])⟩
  have weight : mass t (t+δ*t) ≤ ((window t (t+δ*t)).card:ℝ)*768 := by
    rw [mass]
    calc
      _ ≤ ∑ _q ∈ window t (t+δ*t), (768:ℝ) := by
        apply Finset.sum_le_sum
        intro q hq
        obtain ⟨hq,prime,_⟩ := Finset.mem_filter.mp (by simpa only [window] using hq)
        exact log_bound (Finset.mem_Icc.mp hq).2 prime.pos
      _ = _ := by simp
  have size : ((window t (t+δ*t)).card:ℝ) < (2:ℝ)^501 := by
    exact_mod_cast (Finset.card_le_card incl).trans_lt small
  have floor := mul_le_mul_of_nonneg_left tl (by positivity : 0≤δ)
  have lower : (2:ℝ)^511 ≤ δ*t - mass t (t+δ*t) := by
    calc
      _ = δ*((7:ℝ)/8*U) - (2:ℝ)^501*768 := by norm_num [δ,U,H]
      _ ≤ _ := sub_le_sub floor (weight.trans (mul_le_mul_of_nonneg_right size.le (by norm_num)))
  have sq := pow_le_pow_left₀ (by positivity) lower 2
  calc
    _ = ((2:ℝ)^511)^2 := by norm_num
    _ ≤ _ := sq
    _ = _ := by unfold errorSq; ring

/-- Fewer than 2^542 of the interior primes have fewer than 2^501 partners. -/
theorem exceptional_count (estimate : SelbergEstimate) : poor.card < 2^542 := by
  classical
  obtain ⟨int,upper⟩ := estimate
  let domain := Set.Icc (1:ℝ) (U:ℝ)
  have subset (p) (hp : p∈poor) : slab p ⊆ domain := by
    intro t ht
    obtain ⟨lo,hi⟩ := slab_bounds (Finset.mem_filter.mp (by simpa only [poor] using hp)).1 ht
    exact ⟨le_trans (by norm_num [U]) lo,hi⟩
  have disj : Set.Pairwise (poor : Set ℕ) (fun p q => Disjoint (slab p) (slab q)) := by
    intro p _ q _ neq
    apply Set.disjoint_left.mpr
    intro t hp hq
    obtain ⟨pl,ph⟩ := hp
    obtain ⟨ql,qh⟩ := hq
    simp only [center] at pl ph ql qh
    rcases lt_or_gt_of_ne neq with lt|gt
    · have : (p:ℝ)+1≤q := by exact_mod_cast lt
      linarith
    · have : (q:ℝ)+1≤p := by exact_mod_cast gt
      linarith
  have integrate (p) (hp : p∈poor) : IntegrableOn errorSq (slab p) := int.mono_set (subset p hp)
  have one (p) (hp : p∈poor) : (2:ℝ)^1022 ≤ ∫ t in slab p, errorSq t := by
    have h := setIntegral_ge_of_const_le (μ := volume) measurableSet_Ico
      (by simp [Real.volume_Ico]) (fun t ht => large_error hp (show t ∈ slab p from ht)) (integrate p hp)
    simpa [Real.volume_real_Ico] using h
  have into : (⋃ p ∈ poor, slab p) ⊆ domain := Set.iUnion₂_subset subset
  have bound : (poor.card:ℝ)*(2:ℝ)^1022 ≤ ∫ t in domain, errorSq t := by
    calc
      _ = ∑ _p ∈ poor, (2:ℝ)^1022 := by simp
      _ ≤ ∑ p ∈ poor, ∫ t in slab p, errorSq t := Finset.sum_le_sum (fun p hp => one p hp)
      _ = ∫ t in ⋃ p ∈ poor, slab p, errorSq t := (integral_finset_biUnion poor
        (fun _ _ => measurableSet_Ico) disj integrate).symm
      _ ≤ _ := setIntegral_mono_set int (ae_of_all _ (fun t => by unfold errorSq; exact sq_nonneg _)) into.eventuallyLE
  have L : Real.log (U:ℝ) ≤ 1024 := (log_bound (q:=U) (by omega) (by norm_num [U])).trans (by norm_num)
  have Lsq := pow_le_pow_left₀ (Real.log_nonneg (by norm_num [U])) L 2
  have mult := mul_le_mul_of_nonneg_left Lsq (by positivity : (0:ℝ)≤202*δ*(U:ℝ)^2)
  have bound' := bound.trans_lt upper
  have final : (poor.card:ℝ) < (2:ℝ)^542 := by
    apply (mul_lt_mul_right (show (0:ℝ)<2^1022 by positivity)).mp
    exact bound'.trans (mult.trans_lt (by norm_num [δ,U,H]))
  exact_mod_cast final

private theorem partner_bounds {p q : ℕ} (hq : q∈partners p) :
    q.Prime ∧ 3*p < 2*q ∧ 2*q ≤ 3*p+2*H+2 := by
  obtain ⟨_,pr,lo,hi⟩ := Finset.mem_filter.mp (by simpa only [partners,window] using hq)
  simp only [center] at lo hi
  refine ⟨pr,?_,?_⟩
  · exact_mod_cast (show 3*(p:ℝ)<2*q by linarith only [lo])
  · have h : 2*(q:ℝ) ≤ 3*(p:ℝ)+2*(H:ℝ)+2 := by
      convert mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ)≤2) using 1
      ring
    exact_mod_cast h

/-- The public first label is the true sum, even before skipping modulo six. -/
theorem first_label {p q : ℕ} (hp : p∈InteriorBatchPopulation.interior) (hq : q∈partners p) :
    ceilSqrt (24*(p*q)) = 3*p+2*q := by
  obtain ⟨lo,_,_⟩ := interior_bounds hp
  obtain ⟨_,left,right⟩ := partner_bounds hq
  have scale : U=128*(U/128) := by decide +kernel
  have lower : 3*U ≤ 3*p+2*q := by omega
  have id := multiplier_sum_square p q 3 2
  change (3*p+2*q)^2=24*(p*q)+(3*p).dist (2*q)^2 at id
  rw [Nat.dist_eq_sub_of_le left.le] at id
  have err : 2*q-3*p ≤ 2*H+2 := by omega
  have ds := Nat.pow_le_pow_left err 2
  have room : (2*H+2)^2 + 1 < 6*U := by decide +kernel
  have pos : 3*p+2*q-1+1=3*p+2*q := by omega
  apply SixTraceBudget.first_of_squares _ (by omega)
  nlinarith only [congrArg (fun n : ℕ => n^2) pos, id, ds, room,lower,pos]

private theorem row_info {p q : ℕ} (hp : p∈InteriorBatchPopulation.interior) (hq : q∈partners p) :
    2^1023≤p ∧ p<q ∧ q<U ∧ p.Prime ∧ q.Prime ∧ bin p q ∧
      SixTraceBudget.unitHit (p*q) (ceilSqrt (24*(p*q))) 1 := by
  obtain ⟨pp,lo,hi⟩ := partner_bounds hq
  have width : H+1≤V := by decide +kernel
  have near : q∈neighbors p := by
    rw [neighbors]
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,pp⟩
  obtain ⟨bn,pl,pq,qu,_⟩ := interior_split hp near
  have qp := (interior_bounds hp).2.2
  have cop {l : ℕ} (pr : l.Prime) (large : 6<l) : l.Coprime 6 :=
    pr.coprime_iff_not_dvd.mpr (fun d => (not_le_of_gt large) (Nat.le_of_dvd (by decide) d))
  have unit := (Nat.Coprime.mul_right (cop qp (by omega)).symm (cop pp (by omega)).symm).symm
  refine ⟨pl,pq,qu,qp,pp,bn,?_⟩
  rw [first_label hp hq]
  exact SixTraceBudget.unit_hit_at_minimum qp pp unit le_rfl (by omega)

private noncomputable def good := InteriorBatchPopulation.interior \ poor
private noncomputable def rows := good.sigma (fun p => partners p)
attribute [local irreducible] good rows

private theorem good_count (est : SelbergEstimate) (hc : 2^1009 < InteriorBatchPopulation.interior.card) :
    2^1008 < good.card := by
  have cap := exceptional_count est
  have total := Finset.card_le_card_sdiff_add_card (s:=InteriorBatchPopulation.interior) (t:=poor)
  rw [good]
  omega

private theorem row_count {p : ℕ} (hp : p∈good) : 2^501 ≤ (partners p).card := by
  rw [good] at hp
  obtain ⟨mem,out⟩ := Finset.mem_sdiff.mp hp
  apply Nat.le_of_not_gt
  intro h
  apply out
  rw [poor]
  exact Finset.mem_filter.mpr ⟨mem,h⟩

private theorem cards {P : Finset ℕ} {Q : ℕ → Finset ℕ} {k : ℕ}
    (h : ∀ p∈P, k ≤ (Q p).card) : P.card*k ≤ (P.sigma Q).card := calc
  _ = ∑ _p ∈ P, k := by simp
  _ ≤ ∑ p ∈ P, (Q p).card := Finset.sum_le_sum h
  _ = _ := (Finset.card_sigma _ _).symm

private theorem pairs_count (hc : 2^1008 < good.card) : 2^1509 < rows.card := by
  have n : 2^1509 = 2^1008*2^501 := by decide +kernel
  rw [n,rows]
  exact (Nat.mul_lt_mul_of_pos_right hc (by decide : 0<2^501)).trans_le (cards fun _ hp => row_count hp)

private theorem inj_products {R : Finset ((_ : ℕ) × ℕ)} {T : Finset ℕ}
    (info : ∀ (z : (_ : ℕ) × ℕ), z∈R → z.1.Prime ∧ z.2.Prime ∧ z.1<z.2 ∧ z.1*z.2∈T) :
    R.card ≤ T.card := by
  apply Finset.card_le_card_of_injOn (s:=R) (fun z => z.1*z.2)
  · intro z hz
    exact (info z hz).2.2.2
  · rintro ⟨p,q⟩ h ⟨r,s⟩ k (eq : p*q=r*s)
    obtain ⟨pp,_,pq,_⟩ := info _ h
    obtain ⟨rp,sp,rs,_⟩ := info _ k
    obtain ⟨e,f⟩ := ordered_semiprime_pair_unique rp sp rs.le pq.le pp.one_lt eq
    subst_vars
    rfl

private theorem successful {p q : ℕ} (hp : p∈InteriorBatchPopulation.interior) (hq : q∈partners p) :
    p.Prime ∧ q.Prime ∧ p<q ∧ p*q ∈ SixTraceBudget.successes SixTraceBudget.unitHit 1 := by
  obtain ⟨pl,pq,qu,pp,qp,bn,hit⟩ := row_info hp hq
  have bit : 16*2^2047 ≤ 9*U^2 := by decide +kernel
  have full : 2^2047 ≤ p*q := Nat.le_of_mul_le_mul_left (bit.trans bn.1) (by decide)
  refine ⟨pp,qp,pq,SixTraceBudget.mem_success.mpr ⟨?_,hit⟩⟩
  exact SixTraceBudget.mem_population.mpr ⟨p,q,pl,pq,qu,pp,qp,full,rfl⟩

private theorem to_products : rows.card ≤ (SixTraceBudget.successes SixTraceBudget.unitHit 1).card := by
  apply inj_products
  intro z hz
  rw [rows] at hz
  obtain ⟨hg,hq⟩ := Finset.mem_sigma.mp hz
  rw [good] at hg
  exact successful (Finset.mem_sdiff.mp hg).1 hq

/-- Count distinct public products, including only two distinct 1024-bit
primes with a 2048-bit product. The fixed macroscopic count is independent
of the short-interval Selberg estimate. -/
theorem many_products (estimate : SelbergEstimate)
    (primeCount : 2^1009 < InteriorBatchPopulation.interior.card) :
    2^1509 < (SixTraceBudget.successes SixTraceBudget.unitHit 1).card := by
  exact (pairs_count (good_count estimate primeCount)).trans_le to_products

end PrimeFactors.MeanSquarePrimePartners
