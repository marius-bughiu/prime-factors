import PrimeFactors.ResidueCount
import Mathlib.FieldTheory.Finite.Basic

/-! The first four moments of distinct sums of complementary factors modulo
a prime, when the specified nonzero product is a nonsquare. -/
namespace PrimeFactors.TraceGapMoments

open Finset
variable {ℓ : ℕ} [Fact ℓ.Prime]

private noncomputable def dom (ℓ : ℕ) [Fact ℓ.Prime] : Finset (ZMod ℓ) := univ.erase 0

/-- Each trace has its two preimages, counted once each for nonsquare n. -/
theorem twice (n : ZMod ℓ) (ns : ¬IsSquare n) (f : ZMod ℓ → ZMod ℓ) :
    2*(∑ t ∈ factorSumResidues ℓ n, f t) =
    ∑ x ∈ univ.erase (0:ZMod ℓ), f (x+n/x) := by
  have nonzero : n ≠ 0 := fun h => ns (h ▸ IsSquare.zero)
  have maps : ∀ x ∈ univ.erase (0:ZMod ℓ), x+n/x ∈ factorSumResidues ℓ n :=
    fun x hx => mem_image_of_mem _ hx
  rw [mul_sum, ←sum_fiberwise_of_maps_to' maps f]
  apply sum_congr rfl
  intro t ht
  obtain ⟨x,hx,rfl⟩ := mem_image.mp ht
  have xp := (mem_erase.mp hx).1
  have dist : x ≠ n/x := fun eq => ns ⟨x, by
    have h := mul_div_cancel₀ n xp
    rw [←eq] at h
    exact h.symm⟩
  rw [factorSum_fiber ℓ nonzero xp, sum_const, card_pair dist, two_nsmul, two_mul]

private theorem paired_powers {n : ZMod ℓ} (nonzero : n ≠ 0) (k : ℕ)
    (kp : 0<k) (small : k<ℓ-1) :
    ∑ x ∈ dom ℓ, (x^k+(n/x)^k) = 0 := by
  have total := FiniteField.sum_pow_lt_card_sub_one (ZMod ℓ) k (by simpa only [ZMod.card] using small)
  have part := sum_erase_add (univ : Finset (ZMod ℓ)) (fun x => x^k) (mem_univ 0)
  have zero : ∑ x ∈ dom ℓ, x^k = 0 := by
    simpa only [dom,zero_pow kp.ne',add_zero] using part.trans total
  have mem (x : ZMod ℓ) (hx : x∈dom ℓ) : n/x∈dom ℓ :=
    mem_erase.mpr ⟨div_ne_zero nonzero (mem_erase.mp hx).1,mem_univ _⟩
  have inv (x : ZMod ℓ) (_hx : x∈dom ℓ) : n/(n/x)=x := by
    field_simp [nonzero, (mem_erase.mp _hx).1]
  have swap : ∑ x ∈ dom ℓ, (n/x)^k = ∑ x ∈ dom ℓ, x^k :=
    sum_bij' (fun x _ => n/x) (fun x _ => n/x) mem mem inv inv (fun _ _ => rfl)
  rw [sum_add_distrib,swap,zero,add_zero]

/-- For all odd primes at least seven, the four normalized moments of
the distinct trace values are 0, −n, 0 and −3n². -/
theorem moments (large : 7 ≤ ℓ) (n : ZMod ℓ) (ns : ¬ IsSquare n) :
    (∑ t ∈ factorSumResidues ℓ n, t)=0 ∧
    (∑ t ∈ factorSumResidues ℓ n, t^2) = -n ∧
    (∑ t ∈ factorSumResidues ℓ n, t^3)=0 ∧
    (∑ t ∈ factorSumResidues ℓ n, t^4) = -3*n^2 := by
  have nz : n≠0 := fun h => ns (h ▸ IsSquare.zero)
  have h2 : (2 : ZMod ℓ) ≠ 0 := Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; omega)
  have card : ((dom ℓ).card : ZMod ℓ) = -1 := by
    rw [dom,card_erase_of_mem (mem_univ _),card_univ,ZMod.card,Nat.cast_sub (by omega),
      ZMod.natCast_self,Nat.cast_one,zero_sub]
  have u1 : ∑ x ∈ dom ℓ, (x+n/x)=0 := by
    simpa only [pow_one] using paired_powers nz 1 (by decide) (by omega)
  have u2 := paired_powers nz 2 (by decide) (by omega)
  have u3 := paired_powers nz 3 (by decide) (by omega)
  have u4 := paired_powers nz 4 (by decide) (by omega)
  have norm (x : ZMod ℓ) (hx : x∈dom ℓ) : x*(n/x)=n :=
    mul_div_cancel₀ _ (mem_erase.mp hx).1
  have term2 (x : ZMod ℓ) (hx : x∈dom ℓ) : (x+n/x)^2 = x^2+(n/x)^2+2*n := by
    linear_combination 2*norm x hx
  have term3 (x : ZMod ℓ) (hx : x∈dom ℓ) : (x+n/x)^3 = x^3+(n/x)^3+3*n*(x+n/x) := by
    linear_combination 3*(x+n/x)*norm x hx
  have term4 (x : ZMod ℓ) (hx : x∈dom ℓ) :
      (x+n/x)^4 = x^4+(n/x)^4+4*n*(x^2+(n/x)^2)+6*n^2 := by
    linear_combination (4*(x^2+(n/x)^2)+6*(x*(n/x)+n))*norm x hx
  have half (f : ZMod ℓ → ZMod ℓ) (r : ZMod ℓ)
      (eq : ∑ x ∈ dom ℓ, f (x+n/x) = 2*r) : ∑ t ∈ factorSumResidues ℓ n, f t = r :=
    mul_left_cancel₀ h2 ((twice n ns f).trans eq)
  refine ⟨half id 0 (by simpa only [id_eq,mul_zero] using u1),
    half (·^2) (-n) ?_, half (·^3) 0 ?_, half (·^4) (-3*n^2) ?_⟩
  · rw [sum_congr rfl term2, sum_add_distrib,u2,sum_const,nsmul_eq_mul,card]
    ring
  · rw [sum_congr rfl term3,sum_add_distrib,u3,←mul_sum,u1]
    ring
  · rw [sum_congr rfl term4,sum_add_distrib,sum_add_distrib,u4,←mul_sum,u2,
      sum_const,nsmul_eq_mul,card]
    ring

end PrimeFactors.TraceGapMoments
