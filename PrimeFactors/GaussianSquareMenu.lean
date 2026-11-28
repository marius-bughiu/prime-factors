import PrimeFactors.CyclotomicGaussianReading
import PrimeFactors.SmallNormSquarePopulation

/-! A product with a known two-squares representation gives its Gaussian
reading directly. Counting candidate coordinates measures coverage when
such a representation is sought by square tests. -/
namespace PrimeFactors.GaussianSquareMenu

open Finset MixedPrefixSample CyclotomicGaussianReading
open private PrimeFactors.SmallNormSquarePopulation.pair_data
  PrimeFactors.SmallNormSquarePopulation.parity_count from PrimeFactors.SmallNormSquarePopulation
open scoped Classical
set_option exponentiation.threshold 8192
attribute [local irreducible] sample eligible

theorem represented_sum {p q a b : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p<q)
    (op : Odd p) (oq : Odd q) (repr : p*q=a^2+b^2) : (p+q)%8=(p*q+1)%8 := by
  have y := (negative_iff_two_squares pp qp ord op oq).mpr ⟨a,b,repr⟩
  have s := sum_mod_eight pp qp ord op oq
  have ne : (-2*Complex.I : ℂ)≠2*Complex.I := by norm_num [Complex.ext_iff]
  simpa only [sumResidue,y,if_neg ne] using s.symm

/-- On N=t²+1 the very first Fermat midpoint is already in the right
class modulo four. Every fourth midpoint from there includes the true one. -/
theorem plus_one_stride {p q t : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p<q)
    (op : Odd p) (oq : Odd q) (repr : p*q=t^2+1) :
    ceilSqrt (p*q)=t+1 ∧ ∃ j : ℕ, (p+q)/2=t+1+4*j := by
  have sum8 := represented_sum pp qp ord op oq (a:=t) (b:=1) (by simpa only [one_pow] using repr)
  have oddN := Nat.odd_iff.mp (op.mul oq)
  obtain ⟨u,hu⟩ := op
  obtain ⟨v,hv⟩ := oq
  have evenT : t%2=0 := by
    rw [repr,Nat.add_mod,Nat.pow_mod] at oddN
    rcases Nat.mod_two_eq_zero_or_one t with h|h
    · exact h
    · norm_num [h] at oddN
  have base : (t^2+1+1)%8=(2*(t+1))%8 := by
    have h : ∀ a : Fin 8, a.val%2=0 → (a.val^2+1+1)%8=(2*(a.val+1))%8 := by decide +kernel
    have pm := Nat.mod_modEq t 8
    have eq := h ⟨t%8,Nat.mod_lt _ (by decide)⟩ (by simpa [Nat.mod_mod_of_dvd _ (by decide : 2∣8)] using evenT)
    exact (((pm.pow 2).add (Nat.ModEq.refl 1)).add (Nat.ModEq.refl 1)).symm.trans
      ((show _ ≡ _ [MOD 8] from eq).trans ((pm.add (Nat.ModEq.refl 1)).mul_left 2))
  have first : ceilSqrt (p*q)=t+1 := by
    rw [repr,ceilSqrt,Nat.sqrt_eq']
  have hit : p*q≤((p+q)/2)^2 := by
    have hm : p+q=2*((p+q)/2) := by omega
    have bound : 4*(p*q)≤(p+q)^2 := by
      zify
      nlinarith only [sq_nonneg ((p:ℤ)-q)]
    rw [hm,mul_pow] at bound
    omega
  have ge := ceilSqrt_le_iff.mpr hit
  rw [repr,base] at sum8
  refine ⟨first,((p+q)/2-(t+1))/4,?_⟩
  omega

/-- The squared coordinate can be selected independently from a fixed set;
the second coordinate may be any natural number. -/
def HasCoordinate (A : Finset ℕ) (N : ℕ) : Prop := ∃ a∈A, ∃ b : ℕ, N=a^2+b^2

private def other (a : ℕ) (v : ℕ×ℕ) := (v.1*v.2-a^2).sqrt

private theorem root_eq {a : ℕ} {v : ℕ×ℕ} (eq : ∃ b : ℕ, v.1*v.2=a^2+b^2) :
    v.1*v.2=a^2+(other a v)^2 := by
  obtain ⟨b,h⟩ := eq
  unfold other
  rw [h,Nat.add_sub_cancel_left,Nat.sqrt_eq']

theorem per_coordinate (a : ℕ) (cap : a≤2^513) :
    (sample (fun N => ∃ b : ℕ, N=a^2+b^2)).card≤75*2^1015 := by
  let E := fun N => ∃ b : ℕ, N=a^2+b^2
  let lo := 181*2^1016
  apply PrimeFactors.SmallNormSquarePopulation.parity_count (sample E) (other a) lo (75*2^1015) ((1+a%2)%2)
  · intro z hz
    obtain ⟨_,_,_,odd,low,high,eq⟩ := PrimeFactors.SmallNormSquarePopulation.pair_data hz
    have form := root_eq eq
    have lower : lo≤other a z := by
      by_contra! small
      have bound := Nat.pow_le_pow_left small.le 2
      have room : (2^513:ℕ)^2+lo^2<2^2047 := by decide +kernel
      have := Nat.pow_le_pow_left cap 2
      omega
    have top : other a z<2^1024 := by
      by_contra! large
      have := Nat.pow_le_pow_left large 2
      have : ((2^1024:ℕ)^2)=2^2048 := by decide +kernel
      omega
    have parity := Nat.odd_iff.mp odd
    rw [form,Nat.add_mod,Nat.pow_mod,Nat.pow_mod (other a z)] at parity
    refine ⟨lower,top.trans_le (by decide +kernel),?_⟩
    rcases Nat.mod_two_eq_zero_or_one a with h|h <;>
      rcases Nat.mod_two_eq_zero_or_one (other a z) with k|k <;> norm_num [h,k] at parity ⊢
  · intro x hx y hy same
    obtain ⟨xp,_,xo,_,_,_,ex⟩ := PrimeFactors.SmallNormSquarePopulation.pair_data hx
    obtain ⟨yp,yq,yo,_,_,_,ey⟩ := PrimeFactors.SmallNormSquarePopulation.pair_data hy
    have equal : x.1*x.2=y.1*y.2 := (root_eq ex).trans (same ▸ (root_eq ey).symm)
    obtain ⟨left,right⟩ := ordered_semiprime_pair_unique yp yq yo.le xo.le xp.one_lt equal
    exact Prod.ext left right

theorem menu_count (A : Finset ℕ) (small : ∀ a∈A,a≤2^513) :
    (sample (HasCoordinate A)).card≤A.card*(75*2^1015) := by
  let row := fun a => sample (fun N => ∃ b : ℕ, N=a^2+b^2)
  have cover : sample (HasCoordinate A) ⊆ A.biUnion row := by
    intro z hz
    simp only [sample,mem_filter,mem_ordered,HasCoordinate] at hz
    obtain ⟨⟨p,q,ne,size,a,ha,b,repr⟩,ord⟩ := hz
    exact mem_biUnion.mpr ⟨a,ha,by
      simp only [row,sample,mem_filter,mem_ordered]
      exact ⟨⟨p,q,ne,size,b,repr⟩,ord⟩⟩
  exact (card_le_card cover).trans (card_biUnion_le_card_mul A row _ (fun a ha => per_coordinate a (small a ha)))

theorem menu_frequency (A : Finset ℕ) (small : ∀ a∈A,a≤2^513) (budget : A.card≤2^40) :
    2^960*(sample (HasCoordinate A)).card<eligible.card := by
  have bound := menu_count A small
  have num : 21000000*2^960*((2:ℕ)^40*(75*2^1015))≤2^2046 := by decide +kernel
  have scaled := Nat.mul_le_mul_left (21000000*2^960) (bound.trans (Nat.mul_le_mul_right _ budget))
  apply Nat.lt_of_mul_lt_mul_left (a:=21000000)
  simpa only [Nat.mul_assoc] using (scaled.trans num).trans_lt ChebyshevPrimeSample.eligible_count

/-- On 698897, after detecting 836²+1, the fourth stride-four test hits.
An ordinary consecutive scan takes thirteen and an odd-midpoint scan seven. -/
theorem control : Nat.Prime 701 ∧ Nat.Prime 997 ∧ 701*997=698897 ∧
    698897=836^2+1 ∧ 849^2=698897+148^2 ∧ (849-837)/4+1=4 ∧
    (849-837)/2+1=7 ∧ 849-837+1=13 ∧
    ∀ j : Fin 3, ¬IsSquare ((837+4*j.val)^2-698897) := by
  refine ⟨by norm_num,by norm_num,by norm_num,by norm_num,by norm_num,by norm_num,by norm_num,by norm_num,?_⟩
  intro j
  have gap {n k : ℕ} (lo : k^2<n) (hi : n<(k+1)^2) : ¬IsSquare n := by
    rintro ⟨u,rfl⟩
    by_cases h : u≤k
    · exact (not_le_of_gt lo) (by simpa [sq] using Nat.pow_le_pow_left h 2)
    · exact (not_le_of_gt hi) (by simpa [sq] using Nat.pow_le_pow_left (by omega : k+1≤u) 2)
  fin_cases j
  · exact gap (k:=40) (by norm_num) (by norm_num)
  · exact gap (k:=91) (by norm_num) (by norm_num)
  · exact gap (k:=122) (by norm_num) (by norm_num)

end PrimeFactors.GaussianSquareMenu
