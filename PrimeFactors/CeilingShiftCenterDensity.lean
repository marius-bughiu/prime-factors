import PrimeFactors.CeilingShiftDistances
import PrimeFactors.SquareAnchorCoverage
import PrimeFactors.SmoothSignedStructure

/-! Sum the number of successful earlier centers over the full population.
A divisor of the square of a half-gap can be encoded by three small factors.
Only the first prime contributes a further independent choice. -/
namespace PrimeFactors.CeilingShiftCenterDensity

open Finset MixedPrefixSample CeilingShiftDistances SeparatedMonotonePopulation
open private PrimeFactors.SeparatedMonotonePopulation.prime_first from PrimeFactors.SeparatedMonotonePopulation
open private PrimeFactors.SmoothSignedStructure.harmonic_cap from PrimeFactors.SmoothSignedStructure
open scoped Classical
set_option exponentiation.threshold 4096
attribute [local irreducible] eligible far primes

/-- All divisor choices for every squared gap up to the height are
bounded together. The proof counts encodings before dropping coprimality. -/
theorem square_divisor_sum (U : ℕ) :
    ((∑ d∈Icc 1 U,(d^2).divisors.card : ℕ):ℚ) ≤ U*(harmonic U)^2 := by
  let I := Icc 1 U
  let pairs : Finset (Σ _ : ℕ, ℕ) := I.sigma fun d => (d^2).divisors
  let row (a b : ℕ) := (Icc 1 (U/(a*b))).image fun t => (⟨t*(a*b),t*a^2⟩ : Σ _ : ℕ, ℕ)
  have cover : pairs ⊆ I.biUnion (fun a => I.biUnion (row a)) := by
    rintro ⟨d,g⟩ hz
    obtain ⟨hd,hg⟩ := mem_sigma.mp hz
    obtain ⟨dp,dh⟩ := mem_Icc.mp hd
    obtain ⟨a,b,t,ap,bp,tp,_,eqn,value⟩ :=
      SquareAnchorCoverage.square_parameters dp (Nat.mem_divisors.mp hg).1
    have ab := (Nat.le_mul_of_pos_left (a*b) tp).trans (eqn ▸ dh)
    have aU := (Nat.le_mul_of_pos_right a bp).trans ab
    have bU := (Nat.le_mul_of_pos_left b ap).trans ab
    have tU := (Nat.le_div_iff_mul_le (Nat.mul_pos ap bp)).mpr (eqn ▸ dh)
    exact mem_biUnion.mpr ⟨a,mem_Icc.mpr ⟨ap,aU⟩,mem_biUnion.mpr
      ⟨b,mem_Icc.mpr ⟨bp,bU⟩,mem_image.mpr ⟨t,mem_Icc.mpr ⟨tp,tU⟩,by rw [←eqn,←value]⟩⟩⟩
  have cap : pairs.card ≤ ∑ a∈I, ∑ b∈I,U/(a*b) := by
    apply (card_le_card cover).trans
    apply card_biUnion_le.trans
    apply sum_le_sum
    intro a _
    apply card_biUnion_le.trans
    apply sum_le_sum
    intro b _
    exact card_image_le.trans_eq (by simp)
  rw [show pairs.card=∑ d∈I,(d^2).divisors.card from card_sigma ..] at cap
  exact (Nat.cast_le (α:=ℚ)).mpr cap |>.trans (SquareAnchorCoverage.square_parameter_sum U)

private abbrev D : ℕ := 2^1022

private theorem encoded_cost (A : Finset (ℕ×ℕ)) (P : Finset ℕ) (U : ℕ)
    (C : ℕ→ℕ→Finset ℕ) (g : ℕ×ℕ→ℕ)
    (supply : ∀ z∈A, z.1∈P ∧ 0<g z ∧ g z≤U ∧ z.2=z.1+2*g z)
    (weight : ∀ z∈A, (C z.1 z.2).card≤((g z)^2).divisors.card) :
    ∑ z∈A, (C z.1 z.2).card ≤ P.card*(∑ d∈Icc 1 U,(d^2).divisors.card) := by
  let encode (z : ℕ×ℕ) := (z.1,g z)
  let price (z : ℕ×ℕ) := (z.2^2).divisors.card
  have inside : A.image encode ⊆ P ×ˢ Icc 1 U := by
    intro t ht
    obtain ⟨z,ok,rfl⟩ := mem_image.mp ht
    obtain ⟨pr,dp,cap,_⟩ := supply z ok
    exact mem_product.mpr ⟨pr,mem_Icc.mpr ⟨dp,cap⟩⟩
  have inj : A.toSet.InjOn encode := by
    intro z hz w hw same
    obtain ⟨left,right⟩ := Prod.mk.inj same
    obtain ⟨_,_,_,first⟩ := supply z hz
    obtain ⟨_,_,_,second⟩ := supply w hw
    exact Prod.ext left (by omega)
  calc
    _ ≤ ∑ z∈A,price (encode z) := sum_le_sum weight
    _ = ∑ t∈A.image encode,price t := (sum_image inj).symm
    _ ≤ ∑ t∈P ×ˢ Icc 1 U,price t := sum_le_sum_of_subset inside
    _ = P.card*(∑ d∈Icc 1 U,(d^2).divisors.card) := by simp [sum_product,price]

private theorem divisor_cap : (∑ d∈Icc 1 D,(d^2).divisors.card) ≤ D*711^2 := by
  have bound := PrimeFactors.SmoothSignedStructure.harmonic_cap 1022 (by decide)
  have pos : 0≤harmonic D := by rw [harmonic_eq_sum_Icc]; positivity
  exact_mod_cast (square_divisor_sum D).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ pos bound 2) (Nat.cast_nonneg D))

private theorem sum_bound :
    ∑ z∈eligible,(centers z.1 z.2).card ≤ primes.card*(D*711^2) := by
  apply (encoded_cost eligible primes D centers halfGap ?_ ?_).trans (Nat.mul_le_mul_left _ divisor_cap)
  · rintro ⟨p,q⟩ ok
    obtain ⟨eqn,dp,cap⟩ := gap_data ok
    exact ⟨PrimeFactors.SeparatedMonotonePopulation.prime_first ok,dp,cap.le,eqn⟩
  · rintro ⟨p,q⟩ ok
    exact count_pair ok

private theorem mean_price {s p e : ℕ} (sum : s≤p*(D*711^2))
    (marginal : (2*D)*p<41056*e) : s<(20528*711^2)*e := by
  have both : 2*(D*p)<2*(20528*e) := by
    calc 2*(D*p) = (2*D)*p := by ac_rfl
         _ < 41056*e := marginal
         _ = (2*20528)*e := rfl
         _ = _ := by ac_rfl
  have half := Nat.lt_of_mul_lt_mul_left both
  calc s ≤ p*(D*711^2) := sum
       _ = (D*p)*711^2 := by ac_rfl
       _ < (20528*e)*711^2 := Nat.mul_lt_mul_of_pos_right half (by decide)
       _ = _ := by ac_rfl

/-- The arithmetic mean number of valid centers over the eligible products
is below 20528 · 711², even with the correct shift supplied at each center. -/
theorem mean_bound :
    ∑ z∈eligible,(centers z.1 z.2).card < (20528*711^2)*eligible.card :=
  mean_price sum_bound (by
    rw [show 2*D=X by decide +kernel]
    exact SquareRootPhasePopulation.marginal)

private theorem lower_from (F E : Finset (ℕ×ℕ)) (V : ℕ→ℕ→Finset ℕ) (sub : F⊆E)
    (rows : ∀ z∈F, 2^985≤(V z.1 z.2).card) :
    F.card*2^985≤∑ z∈E,(V z.1 z.2).card := by
  calc _ = ∑ _z∈F,(2^985:ℕ) := by simp
       _ ≤ ∑ z∈F,(V z.1 z.2).card := sum_le_sum rows
       _ ≤ _ := sum_le_sum_of_subset sub

private theorem density_price {s t e f : ℕ} (mean : s<(20528*711^2)*e)
    (lower : f*2^985≤t) (share : 2*e<3*f) : 2^951*s<t := by
  have scale : 3*(2^951*(20528*711^2):ℕ) ≤ 2*2^985 := by decide +kernel
  apply lt_of_lt_of_le _ lower
  apply Nat.lt_of_mul_lt_mul_left (a:=2)
  calc 2*(2^951*s) < 2*(2^951*((20528*711^2)*e)) :=
         Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_left mean (by positivity)) (by decide)
       _ = (2*e)*(2^951*(20528*711^2)) := by ac_rfl
       _ < (3*f)*(2^951*(20528*711^2)) := Nat.mul_lt_mul_of_pos_right share (by positivity)
       _ = f*(3*(2^951*(20528*711^2))) := by ac_rfl
       _ ≤ f*(2*2^985) := Nat.mul_le_mul_left _ scale
       _ = 2*(f*2^985) := by ac_rfl

/-- Sampling uniformly from all eligible (product, earlier center) pairs,
the chance of hitting any legal positive magnitude is below 2^-951. -/
theorem aggregate :
    2^951*(∑ z∈eligible,(centers z.1 z.2).card) < ∑ z∈eligible,(interval z.1 z.2).card :=
  density_price mean_bound (lower_from far eligible interval
    (fun _ hz => (mem_far.mp hz).1) (fun ⟨_,_⟩ hz => interval_lower hz)) two_thirds

end PrimeFactors.CeilingShiftCenterDensity
