import PrimeFactors.ChebyshevPrimeSample
import PrimeFactors.EndpointOffsetProduct
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! Count the endpoint-offset window (U-p)(U-q)<24U on the project's
uniform finite sample of full-size balanced semiprimes. -/
namespace PrimeFactors.EndpointOffsetPopulation
open Finset MixedPrefixSample
set_option exponentiation.threshold 8192
set_option maxRecDepth 4096

private abbrev U : ℕ := 2^1024

/-- Each dyadic shell on the first coordinate has at most H positive
integer pairs when their product is at most H. -/
theorem shells (s : Finset (ℕ×ℕ)) (k H : ℕ)
    (bounds : ∀ z∈s, 0<z.1 ∧ z.1<2^k ∧ 0<z.2 ∧ z.1*z.2≤H) : s.card≤k*H := by
  classical
  let box (i : ℕ) := Ico (2^i) (2^i+2^i) ×ˢ Icc 1 (H/2^i)
  have cover : s⊆(range k).biUnion box := by
    intro z hz
    obtain ⟨pos,top,ypos,small⟩ := bounds z hz
    let i := Nat.log 2 z.1
    have il : i<k := Nat.log_lt_of_lt_pow pos.ne' top
    have a : 2^i≤z.1 := Nat.pow_log_le_self 2 pos.ne'
    have b : z.1<2^i+2^i := by
      simpa only [pow_succ,Nat.mul_two] using Nat.lt_pow_succ_log_self (by decide : 1<2) z.1
    have y : z.2≤H/2^i := (Nat.le_div_iff_mul_le (by positivity)).mpr
      (by simpa only [mul_comm z.2] using (Nat.mul_le_mul_right z.2 a).trans small)
    exact mem_biUnion.mpr ⟨i,mem_range.mpr il,mem_product.mpr
      ⟨mem_Ico.mpr ⟨a,b⟩,mem_Icc.mpr ⟨ypos,y⟩⟩⟩
  have per (i : ℕ) : (box i).card≤H := by
    simp only [box,card_product,Nat.card_Ico,Nat.card_Icc,Nat.add_sub_cancel_left,
      Nat.add_sub_cancel_right,Nat.add_one_sub_one]
    exact Nat.mul_div_le H (2^i)
  calc s.card ≤ _ := card_le_card cover
       _ ≤ _ := card_biUnion_le
       _ ≤ ∑ _i∈range k,H := sum_le_sum (fun i _ => per i)
       _ = k*H := by simp

/-- The integer hyperbola bound before requiring prime or ordered coordinates. -/
theorem all_offsets (s : Finset (ℕ×ℕ))
    (bounds : ∀ z∈s, 0<z.1 ∧ z.1<U ∧ 0<z.2 ∧ z.1*z.2<24*U) :
    s.card≤1024*(24*U) :=
  shells s 1024 (24*U) (fun z hz =>
    let h := bounds z hz
    ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.le⟩)

noncomputable irreducible_def hits : Finset (ℕ×ℕ) :=
  eligible.filter fun z => (U-z.1)*(U-z.2)<24*U

private theorem prime_data {p : ℕ} (pmem : p∈primes) :
    X≤p ∧ p<U ∧ ((U-p)%6=3 ∨ (U-p)%6=5) := by
  obtain ⟨interval,prime⟩ := mem_filter.mp pmem
  obtain ⟨l,r⟩ := mem_Ico.mp interval
  have scale : 2*X=U := by decide +kernel
  rw [scale] at r
  have large : 3<X := by decide +kernel
  have cop {d : ℕ} (pd : Nat.Prime d) (dl : d≤3) : p%d≠0 := by
    intro h
    have eq := (Nat.prime_dvd_prime_iff_eq pd prime).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  have two := cop Nat.prime_two (by decide)
  have three := cop Nat.prime_three (by decide)
  have residue : U%6=4 := by decide +kernel
  exact ⟨l,r,by omega⟩

/-- Rank of a positive allowed offset. Since U=4 mod 6, offsets from primes
above three occupy residues 3 and 5. Their ranks are 1,2,3,4,... in order. -/
private def rank (a : ℕ) := (a+1)/3

private theorem rank_inj {a b : ℕ} (ra : a%6=3 ∨ a%6=5)
    (rb : b%6=3 ∨ b%6=5) (same : rank a=rank b) : a=b := by
  dsimp only [rank] at same
  rcases ra with h|h <;> rcases rb with h'|h' <;> omega

attribute [local irreducible] primes ordered

private theorem data {z : ℕ×ℕ} (hz : z∈hits) :
    z.1∈primes ∧ z.2∈primes ∧ z.1<z.2 ∧ (U-z.1)*(U-z.2)<24*U := by
  rw [hits_def,mem_filter] at hz
  obtain ⟨he,small⟩ := hz
  rw [eligible,sample,mem_filter] at he
  obtain ⟨ord,lt⟩ := he
  obtain ⟨p,q,_⟩ := mem_ordered.mp ord
  exact ⟨p,q,lt,small⟩

attribute [local irreducible] eligible

private def encode (z : ℕ×ℕ) := (rank (U-z.2),rank (U-z.1))

private theorem encode_inj : Set.InjOn encode (hits : Set _) := by
  intro z hz w hw same
  obtain ⟨p,q,_,_⟩ := data hz
  obtain ⟨u,v,_,_⟩ := data hw
  obtain ⟨_,pU,rp⟩ := prime_data p
  obtain ⟨_,qU,rq⟩ := prime_data q
  obtain ⟨_,uU,ru⟩ := prime_data u
  obtain ⟨_,vU,rv⟩ := prime_data v
  have a := rank_inj rp ru (congrArg Prod.snd same)
  have b := rank_inj rq rv (congrArg Prod.fst same)
  exact Prod.ext (by omega) (by omega)

private theorem rank_product {a b u : ℕ} (ab : a*b<24*u) (ub : a+b≤u) :
    rank b*rank a≤25*u/9 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0<9)).mpr
  have pair := Nat.mul_le_mul (Nat.mul_div_le (b+1) 3) (Nat.mul_div_le (a+1) 3)
  change 3*rank b*(3*rank a)≤(b+1)*(a+1) at pair
  nlinarith only [pair,ab,ub]

private theorem encode_bounds {w : ℕ×ℕ} (hw : w∈hits) :
    0<(encode w).1 ∧ (encode w).1<2^513 ∧ 0<(encode w).2 ∧ (encode w).1*(encode w).2≤25*U/9 := by
  obtain ⟨p,q,lt,small⟩ := data hw
  obtain ⟨pl,pu,rp⟩ := prime_data p
  obtain ⟨ql,qu,rq⟩ := prime_data q
  let a := U-w.1
  let b := U-w.2
  change 0<rank b ∧ rank b<2^513 ∧ 0<rank a ∧ rank b*rank a≤25*U/9
  have positive {d : ℕ} (res : d%6=3 ∨ d%6=5) : 0<rank d := by unfold rank; omega
  have ub : a+b≤U := by
    have scale : 2*X=U := by decide +kernel
    dsimp only [a,b]
    omega
  have cap := rank_product (a:=a) (b:=b) small ub
  have order : rank b≤rank a :=
    Nat.div_le_div_right (Nat.add_le_add_right (Nat.sub_le_sub_left lt.le U) 1)
  have limit : rank b<2^513 := by
    by_contra! h
    have high := (Nat.mul_le_mul h (h.trans order)).trans cap
    exact (show ¬ (2^513:ℕ)*2^513≤25*U/9 by decide +kernel) high
  exact ⟨positive rq,limit,positive rp,cap⟩

/-- Count the genuine exact-offset pairs by their ordered ranks, using the
prime residues modulo six. The smaller rank needs only 513 dyadic shells. -/
theorem hit_count : hits.card≤513*(25*U/9) := by
  rw [←card_image_of_injOn encode_inj]
  apply shells _ 513 (25*U/9)
  intro z hz
  obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
  exact encode_bounds hw

/-- For a uniformly chosen sorted eligible prime pair, the fraction satisfying
this endpoint-product condition is strictly less than 2^(-987). -/
theorem eligible_fraction : 2^987*hits.card<MixedPrefixSample.eligible.card := by
  have cap := Nat.mul_le_mul_left (21000000*2^987) hit_count
  have compare : (21000000*2^987)*(513*(25*U/9))≤2^2046 := by decide +kernel
  have strict := (cap.trans compare).trans_lt ChebyshevPrimeSample.eligible_count
  apply Nat.lt_of_mul_lt_mul_left (a:=21000000)
  simpa only [Nat.mul_assoc] using strict

/-- The ceiling applies directly to this checked probe returning the actual
prime pair at the endpoint U. -/
theorem probe_fraction :
    2^987*(eligible.filter (fun z => EndpointOffsetProduct.probe U (z.1*z.2)=some z)).card <
      eligible.card := by
  apply lt_of_le_of_lt (Nat.mul_le_mul_left _ (card_le_card (t:=hits) ?_)) eligible_fraction
  intro z hz
  obtain ⟨eligibleZ,hit⟩ := mem_filter.mp hz
  rw [eligible,sample,mem_filter] at eligibleZ
  obtain ⟨pm,qm,_⟩ := mem_ordered.mp eligibleZ.1
  have qU := (prime_data qm).2.1.le
  have l := (prime_data pm).1
  rw [primes,mem_filter] at pm
  have prime := pm.2
  have large : 6<z.1 := lt_of_lt_of_le (by decide +kernel : 6<X) l
  have unit := prime.coprime_iff_not_dvd.mpr (show ¬z.1∣6 from fun h =>
    (not_le_of_gt large) (Nat.le_of_dvd (by decide) h))
  have small := (EndpointOffsetProduct.probe_iff unit (by omega) eligibleZ.2.le qU).mp
    (by simpa only [Prod.mk.eta] using hit)
  have stride : weightedStride (z.1*z.2) 1 1≤24 := Nat.gcd_le_left _ (by decide)
  rw [hits_def,mem_filter]
  refine ⟨?_,small.trans_le (by simpa only [mul_comm U] using Nat.mul_le_mul_left U stride)⟩
  rwa [eligible,sample,mem_filter]

end PrimeFactors.EndpointOffsetPopulation
