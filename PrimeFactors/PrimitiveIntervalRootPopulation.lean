import PrimeFactors.PrimitiveIntervalRootBand
import PrimeFactors.ChebyshevPrimeSample

/-! Pointwise and population consequences of supplying a coarse estimate of
the character interval total. No estimate is inferred from the product here. -/
namespace PrimeFactors.PrimitiveIntervalRootPopulation

open Finset MixedPrefixSample PrimitiveIntervalMoment PrimitiveIntervalRootBand
set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
attribute [local irreducible] X eligible ordered primes

private theorem data_of_mem {p q : ℕ} (ok : (p,q)∈eligible) :
    p.Prime ∧ q.Prime ∧ p<q ∧ q<2*p ∧ q<2^1024 ∧ 2^2047≤p*q := by
  rw [eligible,sample,mem_filter] at ok
  obtain ⟨pm,qm,_,full,_⟩ := mem_ordered.mp ok.1
  rw [primes,mem_filter,mem_Ico] at pm qm
  have pl : X≤p := pm.1.1
  have qu : q<2*X := qm.1.2
  have top : 2*X=2^1024 := by unfold X; decide +kernel
  have bot : 2*X^2=2^2047 := by unfold X; decide +kernel
  exact ⟨pm.2,qm.2,ok.2,by omega,top ▸ qu,bot ▸ full⟩

noncomputable def smallGap (G : ℕ) : Finset (ℕ×ℕ) := eligible.filter (fun z => z.2-z.1<G)

theorem mem_smallGap {p q G : ℕ} : (p,q)∈smallGap G ↔ (p,q)∈eligible ∧ q-p<G := by
  simp only [smallGap,mem_filter]

attribute [local irreducible] smallGap

/-- Encode each ordered pair by its first coordinate and its nonnegative gap. -/
private theorem gap_grid (pairs : Finset (ℕ×ℕ)) (H G : ℕ)
    (bounds : ∀ z∈pairs, z.1<H ∧ z.1≤z.2 ∧ z.2-z.1<G) : pairs.card≤H*G := by
  let code (z : ℕ×ℕ) := (z.1,z.2-z.1)
  have into : ∀ z∈pairs, code z∈range H ×ˢ range G := by
    intro z hz
    obtain ⟨hi,_,gap⟩ := bounds z hz
    exact mem_product.mpr ⟨mem_range.mpr hi,mem_range.mpr gap⟩
  have unique : ∀ z∈pairs, ∀ w∈pairs, code z=code w → z=w := by
    rintro ⟨p,q⟩ first ⟨s,t⟩ second eq
    have same : p=s := congrArg Prod.fst eq
    subst s
    have diff : q-p=t-p := congrArg Prod.snd eq
    have lo : p≤q := (bounds (p,q) first).2.1
    have hi : p≤t := (bounds (p,t) second).2.1
    exact Prod.ext rfl (by omega)
  simpa only [card_product,card_range] using card_le_card_of_injOn code into unique

theorem small_gap_count (G : ℕ) : (smallGap G).card ≤ 2^1024*G := by
  apply gap_grid
  rintro ⟨p,q⟩ member
  obtain ⟨ok,short⟩ := (mem_smallGap (p:=p) (q:=q) (G:=G)).mp member
  obtain ⟨_,_,ord,_,qu,_⟩ := data_of_mem ok
  exact ⟨ord.trans qu,ord.le,short⟩

theorem gap_exceptions : 2^15*(smallGap (2^982)).card < eligible.card := by
  apply Nat.lt_of_mul_lt_mul_left (a:=21000000)
  exact (Nat.mul_le_mul_left 21000000 (Nat.mul_le_mul_left (2^15) (small_gap_count _))).trans_lt
    ((by decide +kernel : 21000000*(2^15*(2^1024*2^982))<2^2046).trans ChebyshevPrimeSample.eligible_count)

/-- For a typical product, an estimate of V with absolute error 2^1450
already places the smaller prime within 2^470 of an explicit real number. -/
theorem from_coarse_reading {p q : ℕ} (ok : (p,q)∈eligible) (typical : (p,q)∉smallGap (2^982))
    (v : ℝ) {actual : ℤ} (total : aggregate p q (cutoff (p*q))=(actual:ℂ))
    (error : |v-(actual:ℝ)|≤2^1450) :
    |estimatedFactor (p*q) (cutoff (p*q)) v-(p:ℝ)|≤2^470 := by
  obtain ⟨pp,qp,ord,balanced,top,full⟩ := data_of_mem ok
  letI : Fact p.Prime := ⟨pp⟩
  letI : Fact q.Prime := ⟨qp⟩
  let b := cutoff (p*q)
  have gap : 2^982≤q-p := by
    by_contra! small
    exact typical ((mem_smallGap (p:=p) (q:=q) (G:=2^982)).mpr ⟨ok,small⟩)
  have size := full_width_cutoff full
  have bp : b<p := (cutoff_bounds pp.pos balanced).1
  have valueEq : value (p*q) b (p+q) = actual := by
    exact_mod_cast (aggregate_value ord balanced).symm.trans total
  have realEq : (((p:ℝ)+q)-b-1)^2-2*((p:ℝ)*q)+2*b+1=(actual:ℝ) := by
    rw [←valueEq,value]; push_cast; ring
  have long : (b:ℝ)≤p+q-(b:ℝ)-1 := by
    have h : 2*b+1≤p+q := by omega
    exact_mod_cast (show (b:ℤ)≤(p:ℤ)+q-b-1 by omega)
  have estimated := estimate (v:=v) (E:=(2:ℝ)^1450) (H:=(2:ℝ)^1024) (Nat.cast_nonneg p)
    (show (p:ℝ)≤q by exact_mod_cast ord.le) (show (q:ℝ)≤2^1024 by exact_mod_cast top.le)
    (Nat.cast_nonneg b) long (by rwa [realEq])
  have sep : (2:ℝ)^982 ≤ (q:ℝ)-p := by
    exact_mod_cast (show (2:ℤ)^982 ≤ (q:ℤ)-p by omega)
  have height : (2:ℝ)^1023 ≤ b := by exact_mod_cast size
  have coeff := mul_le_mul sep height (by positivity) (sub_nonneg.mpr (by exact_mod_cast ord.le))
  have nonneg := abs_nonneg (estimatedFactor ((p:ℝ)*q) b v-p)
  have bound := (mul_le_mul_of_nonneg_right coeff nonneg).trans estimated
  apply le_of_mul_le_mul_left (a:=(2:ℝ)^982*2^1023) _ (by positivity)
  convert bound using 1
  rw [←pow_add,←pow_add,show (2:ℝ)*2^1024*2^1450=2^2475 by
    rw [←pow_succ',←pow_add]]

end PrimeFactors.PrimitiveIntervalRootPopulation
