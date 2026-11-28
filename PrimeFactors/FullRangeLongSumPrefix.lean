import PrimeFactors.FullRangePrimeSumShare
import PrimeFactors.Fermat

/-! The frequency of the distinguished sum classes after excluding sums less
than 10,000 or 2^900 above the arithmetic lower endpoint. The counting measure gives
one vote to each canonical pair of distinct primes. -/

namespace PrimeFactors.FullRangeLongSumPrefix

open Finset PrimeProductRegion FullRangeResidueEstimates
open WideResiduePrimeSupply (B)
open WidePrimePairSumFrequency (selected local_counts)

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

noncomputable def shortAt (width : ℕ) : Finset (ℕ×ℕ) := (population univ).filter
  (fun v => v.1+v.2 < ceilSqrt (4*(v.1*v.2))+width)

noncomputable def selectedAfter (width : ℕ) : Finset (ℕ×ℕ) := (population selected).filter
  (fun v => ceilSqrt (4*(v.1*v.2))+width ≤ v.1+v.2)

noncomputable abbrev shortPairs := shortAt 10000
noncomputable abbrev longSelected := selectedAfter 10000
noncomputable abbrev wideSelected := selectedAfter (2^900)

theorem mem_selectedAfter {p q width : ℕ} : (p,q)∈selectedAfter width ↔
    (p,q)∈population selected ∧ ceilSqrt (4*(p*q))+width≤p+q := by
  simp only [selectedAfter,mem_filter]

theorem mem_longSelected {p q : ℕ} :
    (p,q)∈longSelected ↔ (p,q)∈population selected ∧ ceilSqrt (4*(p*q))+10000≤p+q :=
  mem_selectedAfter

theorem mem_wideSelected {p q : ℕ} :
    (p,q)∈wideSelected ↔ (p,q)∈population selected ∧ ceilSqrt (4*(p*q))+2^900≤p+q :=
  mem_selectedAfter

attribute [local irreducible] population cell shortAt selectedAfter

/-- A sum within the given width of the rounded lower endpoint bounds the
squared factor gap by twice that width times the factor sum. -/
theorem short_gap_sq_at {p q width : ℕ} (order : p≤q)
    (short : p+q<ceilSqrt (4*(p*q))+width) : (q-p)^2≤width*(2*(p+q)) := by
  let a := (4*(p*q)).sqrt
  let s := p+q
  have gap : (q-p)^2+4*(p*q)=s^2 := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le order
    dsimp [s]; rw [Nat.add_sub_cancel_left]; ring
  have low : a^2≤4*(p*q) := Nat.sqrt_le' _
  have rounded : ceilSqrt (4*(p*q))≤a+1 := ceilSqrt_le_iff.mpr (Nat.lt_succ_sqrt' _).le
  have below : a≤s := (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp (by omega)
  have close : s-a≤width := by dsimp only [s]; omega
  have difference : (s-a)*(s+a)+a^2=s^2 := by
    obtain ⟨k,rep⟩ := Nat.exists_eq_add_of_le below
    rw [rep,Nat.add_sub_cancel_left]; ring
  have product := Nat.mul_le_mul close (show s+a≤2*s by omega)
  change (q-p)^2≤width*(2*s)
  omega

theorem short_gap_sq {p q : ℕ} (order : p≤q)
    (short : p+q<ceilSqrt (4*(p*q))+10000) : (q-p)^2≤10000*(2*(p+q)) :=
  short_gap_sq_at order short

private theorem gap_bound {p q width G : ℕ} (order : p<q) (top : q<B) (pos : 0<width)
    (cap : width*(2*(2*B))≤G^2) (short : p+q<ceilSqrt (4*(p*q))+width) : q-p<G := by
  have sum : p+q<2*B := by omega
  have result := (short_gap_sq_at order.le short).trans_lt
    ((Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_left sum (by decide : 0<2)) pos).trans_le cap)
  exact lt_of_not_ge (fun le => (not_le_of_gt result) (Nat.pow_le_pow_left le 2))

theorem short_gap {p q : ℕ} (order : p<q) (top : q<B)
    (short : p+q<ceilSqrt (4*(p*q))+10000) : q-p<2^520 :=
  gap_bound order top (by decide) (by decide +kernel) short

private theorem gap_grid (P : Finset (ℕ×ℕ)) (A H G : ℕ)
    (bounds : ∀ v∈P, A≤v.1 ∧ v.1<v.2 ∧ v.1-A<H ∧ v.2-v.1<G) : P.card≤H*G := by
  let code (v : ℕ×ℕ) := (v.1-A,v.2-v.1)
  have into : ∀ v∈P, code v∈range H ×ˢ range G := by
    intro v ok
    obtain ⟨_,_,first,last⟩ := bounds v ok
    exact mem_product.mpr ⟨mem_range.mpr first,mem_range.mpr last⟩
  have inj : ∀ v∈P, ∀ w∈P, code v=code w → v=w := by
    rintro ⟨p,q⟩ hp ⟨a,b⟩ ha eq
    obtain ⟨pl,pq,_⟩ := bounds (p,q) hp
    obtain ⟨al,ab,_⟩ := bounds (a,b) ha
    have fst : p-A=a-A := congrArg Prod.fst eq
    have snd : q-p=b-a := congrArg Prod.snd eq
    exact Prod.ext (by dsimp at pl al; omega) (by dsimp at pl al pq ab; omega)
  simpa only [card_product,card_range] using card_le_card_of_injOn code into inj

private theorem count_subset (P : Finset (ℕ×ℕ)) {width G : ℕ}
    (pos : 0<width) (cap : width*(2*(2*B))≤G^2)
    (data : ∀ v∈P, X≤v.1 ∧ v.1<v.2 ∧ v.2<B ∧ v.1+v.2<ceilSqrt (4*(v.1*v.2))+width) :
    P.card≤2^1023*G := by
  apply gap_grid P X
  intro v hv
  obtain ⟨lo,order,hi,short⟩ := data v hv
  have twice : B=X+2^1023 := by decide +kernel
  exact ⟨lo,order,by omega,gap_bound order hi pos cap short⟩

/-- Store p−2^1023 and q−p to bound any subset in the same-width box with
the given short prefix. The bound allows all product and sum residues. -/
theorem wide_short_bound (P : Finset (ℕ×ℕ))
    (data : ∀ v∈P, X≤v.1 ∧ v.1<v.2 ∧ v.2<B ∧
      v.1+v.2<ceilSqrt (4*(v.1*v.2))+2^900) : P.card≤2^1986 := by
  rw [show (2:ℕ)^1986=2^1023*2^963 by decide +kernel]
  exact count_subset P (by decide) (by decide +kernel) data

theorem count_at {width G : ℕ} (pos : 0<width) (cap : width*(2*(2*B))≤G^2) :
    (shortAt width).card≤2^1023*G := by
  apply count_subset (shortAt width) pos cap
  rintro ⟨p,q⟩ ok
  obtain ⟨member,short⟩ := mem_filter.mp (show (p,q)∈(population univ).filter
    (fun v => v.1+v.2<ceilSqrt (4*(v.1*v.2))+width) by simpa only [shortAt] using ok)
  obtain ⟨lo,order,hi,_⟩ := mem_population.mp member
  exact ⟨lo,order,hi,short⟩

theorem short_count : (shortAt 10000).card≤2^1543 := by
  rw [show (2:ℕ)^1543=2^1023*2^520 by decide +kernel]
  exact count_at (by decide) (by decide +kernel)

theorem wide_short_count : (shortAt (2^900)).card≤2^1986 := by
  rw [show (2:ℕ)^1986=2^1023*2^963 by decide +kernel]
  exact count_at (by decide) (by decide +kernel)

/-- All twenty ordered residue cells contribute the common proven lower
bound; swapping the distinct factors counts each unordered pair twice. -/
theorem population_lower {D U M : ℕ} (h : Estimates D U M) :
    10*(M*(M-1))≤(population univ).card := by
  have lower (v : ZMod 25 × ZMod 25) (ok : v∈ResiduePairWeights.cells (1:ZMod 25) univ) :
      M*(M-1) ≤ cell v := by
    have units : IsUnit v.1 ∧ IsUnit v.2 := (Commute.all _ _).isUnit_mul_iff.mp
      (by rw [(mem_filter.mp ok).2.1]; exact isUnit_one)
    exact cell_lower h units.1 units.2
  have sum := sum_le_sum lower
  rw [sum_const,smul_eq_mul,local_counts.2.1,←twice_count] at sum
  omega

/-- Using the published BMOR endpoint input, fewer than one in 2^476
eligible prime pairs has a short prefix. -/
theorem short_fraction {li : ℕ → ℝ} (h : EndpointEstimates bmorError25 li) :
    2^476*(shortAt 10000).card<(population univ).card := by
  have enough : 2^476*2^1543<10*(M*(M-1)) := by decide +kernel
  exact (Nat.mul_le_mul_left _ short_count).trans_lt (enough.trans_le (population_lower (bmor h)))

/-- Even the prefix of length 2^900 excludes fewer than one in 2^33
eligible pairs, under the supplied unconditional BMOR estimate. -/
theorem wide_short_fraction {li : ℕ → ℝ} (h : EndpointEstimates bmorError25 li) :
    2^33*(shortAt (2^900)).card<(population univ).card := by
  have enough : 2^33*2^1986<10*(M*(M-1)) := by decide +kernel
  exact (Nat.mul_le_mul_left _ wide_short_count).trans_lt (enough.trans_le (population_lower (bmor h)))

private theorem lost_le (width : ℕ) :
    (population selected).card≤(selectedAfter width).card+(shortAt width).card := by
  classical
  let S := population selected
  let long (v : ℕ×ℕ) := ceilSqrt (4*(v.1*v.2))+width≤v.1+v.2
  have partition := filter_card_add_filter_neg_card_eq_card (s:=S) long
  have sub : S.filter (fun v => ¬long v) ⊆ shortAt width := by
    rintro ⟨p,q⟩ hv
    obtain ⟨ok,ne⟩ := mem_filter.mp hv
    obtain ⟨lo,order,hi,pp,qp,w,prod,_⟩ := mem_population.mp ok
    rw [shortAt,mem_filter]
    exact ⟨mem_population.mpr ⟨lo,order,hi,pp,qp,w,prod,mem_univ _⟩,lt_of_not_ge ne⟩
  have bound := card_le_card sub
  have same : S.filter long=selectedAfter width := by unfold selectedAfter; rfl
  rw [same] at partition
  change S.card≤(selectedAfter width).card+(shortAt width).card
  omega

private theorem card_at {li : ℕ → ℝ} (h : EndpointEstimates bmorError25 li) (width k : ℕ)
    (enough : 10000≤k) (rare : k*(shortAt width).card<(population univ).card) :
    499*(population univ).card<1000*(selectedAfter width).card := by
  let T := (population univ).card
  let G := (population selected).card
  let S := (shortAt width).card
  let H := (selectedAfter width).card
  change k*S<T at rare
  have thin : 10000*S<T := (Nat.mul_le_mul_right S enough).trans_lt rare
  have tp : (0:ℚ)<T := Nat.cast_pos.mpr (by omega)
  have lower := (abs_le.mp (FullRangePrimeSumShare.bmor_accuracy h)).1
  change -(1/1648:ℚ)≤(G:ℚ)/T-1/2 at lower
  have lower' := (le_div_iff₀ tp).mp (show (1/2-1/1648 : ℚ)≤(G:ℚ)/T by linarith)
  have freq : 1648*G≥823*T := by
    exact_mod_cast (show 823*(T:ℚ)≤1648*(G:ℚ) by linarith only [lower'])
  have lost : G≤H+S := lost_le width
  change 499*T<1000*H
  omega

/-- More than 49.9% of the full product-one population belongs to the two
distinguished sum classes and has at least 10,000 units of sum distance. -/
theorem bmor_card {li : ℕ → ℝ} (h : EndpointEstimates bmorError25 li) :
    499*(population univ).card<1000*(selectedAfter 10000).card :=
  card_at h 10000 (2^476) (by decide +kernel) (short_fraction h)

/-- The same percentage bound holds even when at least 2^900 units of sum
distance are required on every pair counted in the numerator. -/
theorem bmor_wide_card {li : ℕ → ℝ} (h : EndpointEstimates bmorError25 li) :
    499*(population univ).card<1000*(selectedAfter (2^900)).card :=
  card_at h (2^900) (2^33) (by decide +kernel) (wide_short_fraction h)

private theorem ratio_gt {a b : ℕ} (positive : 0<b) (h : 499*b<1000*a) :
    (499:ℚ)/1000<(a:ℚ)/b := by
  apply (div_lt_div_iff₀ (by norm_num) (Nat.cast_pos.mpr positive)).mpr
  exact_mod_cast (show 499*b<a*1000 by simpa [Nat.mul_comm] using h)

theorem bmor_share {li : ℕ → ℝ} (h : EndpointEstimates bmorError25 li) :
    499/1000 < ((selectedAfter 10000).card:ℚ)/(population univ).card :=
  ratio_gt ((Nat.zero_le _).trans_lt (short_fraction h)) (bmor_card h)

theorem bmor_wide_share {li : ℕ → ℝ} (h : EndpointEstimates bmorError25 li) :
    499/1000 < ((selectedAfter (2^900)).card:ℚ)/(population univ).card :=
  ratio_gt ((Nat.zero_le _).trans_lt (wide_short_fraction h)) (bmor_wide_card h)

end PrimeFactors.FullRangeLongSumPrefix
