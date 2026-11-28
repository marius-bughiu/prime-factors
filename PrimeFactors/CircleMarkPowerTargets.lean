import PrimeFactors.CircleMarkBinomialMask
import PrimeFactors.CircleMarkJacobiMaskDegree

/-! A mask with a single unrestricted power and several constants. Distinct
constants modulo a prime have disjoint root fibers. Their two quadratic signs
share one common fiber size, independent of the target value. -/
namespace PrimeFactors.CircleMarkPowerTargets

open Finset Polynomial CircleMarkJacobiMask CircleMarkJacobiMaskDegree
open CircleMarkMidcutReadout CircleMarkBinomialFibers
open scoped Classical
open private PrimeFactors.CircleMarkBinomialFibers.positiveUnits
  PrimeFactors.CircleMarkBinomialFibers.kernel PrimeFactors.CircleMarkBinomialFibers.fiber_count
  PrimeFactors.CircleMarkBinomialFibers.positive_size from PrimeFactors.CircleMarkBinomialFibers
open CircleMarkBinomialFibers (positiveUnits kernel fiber_count positive_size)

/-- Integer polynomial with one target for each listed constant. -/
noncomputable def mask (e : ℕ) (A : Finset ℤ) : ℤ[X] := ∏ c∈A, (X^e - C c)

/-- Integer constants congruent at r contribute one power fiber. -/
private theorem signed_count (r : ℕ) [Fact r.Prime] (e : ℕ) (A : Finset ℤ) (s : ℤ) :
    (signedRoots r (mask e A) s).card =
      ∑ c∈A.image (fun c : ℤ => (c:ZMod r)), (fiber r e c s).card := by
  let T := A.image (fun c : ℤ => (c:ZMod r))
  have sets : signedRoots r (mask e A) s = T.biUnion (fun c => fiber r e c s) := by
    ext x
    simp only [signedRoots,CircleMarkJacobiMask.rootSet,mem_filter,mem_univ,true_and,mask,
      Polynomial.map_prod,Polynomial.eval_prod,Polynomial.map_sub,Polynomial.map_pow,
      Polynomial.map_X,Polynomial.map_C,eval_sub,eval_pow,eval_X,eval_C,Int.coe_castRingHom,
      prod_eq_zero_iff,sub_eq_zero,T,mem_biUnion,mem_image,fiber]
    constructor
    · rintro ⟨⟨c,hc,xc⟩,xs⟩
      exact ⟨_,⟨c,hc,rfl⟩,xc,xs⟩
    · rintro ⟨_,⟨c,hc,rfl⟩,xc,xs⟩
      exact ⟨⟨c,hc,xc⟩,xs⟩
  rw [sets,card_biUnion]
  intro a _ b _ ne
  apply disjoint_left.mpr
  intro x ha hb
  exact ne ((mem_filter.mp ha).2.1.symm.trans (mem_filter.mp hb).2.1)

/-- A common divisor of the half-period and the local sum controls how many
signed roots a single constant can contribute. -/
theorem local_multiplicity {r : ℕ} [Fact r.Prime] (odd : r≠2) (e : ℕ) (A : Finset ℤ) :
    ∃ d : ℕ, d∣half r ∧ d∣(localSum r (mask e A)).natAbs ∧
      (localSum r (mask e A)).natAbs ≤ d*(A.image (fun c : ℤ => (c:ZMod r))).card := by
  let d := Nat.card (kernel r e)
  let T := A.image (fun c : ℤ => (c:ZMod r))
  have divr : d∣half r := by
    have h := Subgroup.card_dvd_of_le (show kernel r e ≤ positiveUnits r from inf_le_left)
    simpa only [positive_size r odd] using h
  have count (s : ℤ) (sn : s≠0) :
      d∣(signedRoots r (mask e A) s).card ∧ (signedRoots r (mask e A) s).card≤d*T.card := by
    rw [signed_count]
    constructor
    · apply dvd_sum
      intro c _
      rcases fiber_count r e c s sn with zero|full
      · rw [zero]; exact dvd_zero _
      · rw [full]
    · calc _ ≤ ∑ _c∈T, d := by
             apply sum_le_sum
             intro c _
             rcases fiber_count r e c s sn with h|h
             · rw [h]; exact Nat.zero_le _
             · exact h.le
           _ = _ := by simp [mul_comm]
  obtain ⟨neg,m⟩ := count (-1) (by decide)
  obtain ⟨pos,p⟩ := count 1 (by decide)
  refine ⟨d,divr,?_,?_⟩
  · change (d:ℤ).natAbs ∣ (localSum r (mask e A)).natAbs
    apply Int.natAbs_dvd_natAbs.mpr
    rw [CircleMarkJacobiMaskDegree.local_difference odd]
    exact dvd_sub (by exact_mod_cast neg) (by exact_mod_cast pos)
  · rw [CircleMarkJacobiMaskDegree.local_difference odd]
    change _ ≤ d*T.card
    omega

/-- For any exact match, the gcd of the required magnitude and the larger
half-period bounds the multiplicity gain per distinct residue target. -/
theorem constants_times_gcd {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) (e : ℕ) (A : Finset ℤ)
    (reading : (globalSum (p*q) (mask e A)).natAbs = cutoff (p*q)*half p) :
    cutoff (p*q) ≤ (half q).gcd (cutoff (p*q)*half p) *
      (A.image (fun c : ℤ => (c:ZMod q))).card := by
  rw [factorization order.ne,Int.natAbs_mul] at reading
  obtain ⟨d,dv,dl,size⟩ := local_multiplicity oq e A
  have divides : d ∣ cutoff (p*q)*half p := reading ▸ dl.trans (dvd_mul_left _ _)
  have qp := hq.out.two_le
  have vpos : 0<half q := by unfold half; omega
  have gain := Nat.le_of_dvd (Nat.gcd_pos_of_pos_left (cutoff (p*q)*half p) vpos) (Nat.dvd_gcd dv divides)
  have first : (localSum p (mask e A)).natAbs ≤ half p := by
    have h := (local_bound op (mask e A)).trans
      (show ((min (half p) (mask e A).natDegree:ℕ):ℤ) ≤ (half p:ℤ) by exact_mod_cast min_le_left ..)
    rw [←Int.natCast_natAbs] at h
    exact_mod_cast h
  have total := Nat.mul_le_mul first (size.trans (Nat.mul_le_mul_right _ gain))
  rw [reading,Nat.mul_comm (half p)] at total
  have pr := hp.out.two_le
  exact Nat.le_of_mul_le_mul_right total (by unfold half; omega)

/-- Whenever the desired magnitude is coprime to the larger half-period, an
exact match needs at least K distinct target values modulo the larger prime. -/
theorem constants_of_coprime {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) (e : ℕ) (A : Finset ℤ)
    (cop : (half q).Coprime (cutoff (p*q)*half p))
    (reading : (globalSum (p*q) (mask e A)).natAbs = cutoff (p*q)*half p) :
    cutoff (p*q) ≤ (A.image (fun c : ℤ => (c:ZMod q))).card := by
  simpa only [cop.gcd_eq_one,one_mul] using constants_times_gcd order op oq e A reading

/-- At a safe larger prime, all K targets are required, for any exponent.
This holds for all ordered distinct odd primes, with no ratio restriction. -/
theorem safe_prime {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) (safe : (half q).Prime) (e : ℕ) (A : Finset ℤ)
    (reading : (globalSum (p*q) (mask e A)).natAbs = cutoff (p*q)*half p) :
    cutoff (p*q) ≤ A.card := by
  have kpos := cutoff_pos order op
  have up := hp.out.two_le
  have u : 0<half p := by unfold half; omega
  have kv : cutoff (p*q) < half q := by
    obtain ⟨a,pa⟩ := hp.out.odd_of_ne_two op
    obtain ⟨b,qb⟩ := hq.out.odd_of_ne_two oq
    have cap := Nat.mul_le_mul_right q (show p+2≤q by omega)
    have root : (p*q).sqrt < q-1 := Nat.sqrt_lt'.mpr (by
      rw [qb] at cap ⊢
      rw [show 2*b+1-1=2*b by omega]
      nlinarith only [cap])
    unfold cutoff half
    omega
  have uv := (between order).1.trans_lt kv
  have cop : (half q).Coprime (cutoff (p*q)*half p) := by
    apply safe.coprime_iff_not_dvd.mpr
    rw [safe.dvd_mul]
    exact not_or.mpr ⟨Nat.not_dvd_of_pos_of_lt kpos kv,Nat.not_dvd_of_pos_of_lt u uv⟩
  exact (constants_of_coprime order op oq e A cop reading).trans card_image_le

/-- The ordinary prefix uses exponent one and exactly L distinct integer constants. -/
theorem attainable (L : ℕ) :
    ∃ A : Finset ℤ, A.card=L ∧ mask 1 A=prefixMask L := by
  let f := fun x : ℕ => (x:ℤ)^2
  have inj : Function.Injective f := by
    intro x y eq
    dsimp only [f] at eq
    have squares : x^2=y^2 := by exact_mod_cast eq
    exact Nat.mul_self_inj.mp (by simpa only [sq] using squares)
  refine ⟨(Icc 1 L).image f,?_,?_⟩
  · rw [card_image_of_injective _ inj,Nat.card_Icc]; omega
  · rw [mask,prod_image inj.injOn,prefixMask,squareMask]
    simp [f]

end PrimeFactors.CircleMarkPowerTargets
