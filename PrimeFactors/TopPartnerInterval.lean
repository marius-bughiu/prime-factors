import PrimeFactors.EndpointOffsetProduct
import PrimeFactors.WeightedCrowdingEstimates

/-! An unconditional published prime-count input for partners of a prime within
255 of the upper endpoint. Primality of the near-endpoint prime is a hypothesis. -/
namespace PrimeFactors.TopPartnerInterval
open Finset Real WeightedCrowdingEstimates
set_option exponentiation.threshold 8192

private abbrev U : ℕ := 2^1024
private abbrev A : ℕ := 63*U/64
private abbrev B : ℕ := 127*U/128

noncomputable irreducible_def partners : Finset ℕ := (Ioc A B).filter Nat.Prime

/-- Compare the prime counts at the two public endpoints using Dusart (6.6). -/
theorem many_partners (dusart : Dusart) : 2^1007 < partners.card := by
  have logs {x : ℕ} (lo : 2^2047≤x^2) (hi : x≤U) :
      (708:ℝ)≤log x-11/10 ∧ log x-1≤709 := by
    have pos : (0:ℝ)<x := by
      have nz : x≠0 := by intro z; simp [z] at lo
      exact_mod_cast Nat.pos_of_ne_zero nz
    have lower := log_le_log (by positivity : 0<(2:ℝ)^2047) (by exact_mod_cast lo : (2:ℝ)^2047≤(x:ℝ)^2)
    have upper := log_le_log pos (by exact_mod_cast hi : (x:ℝ)≤2^1024)
    rw [log_pow,log_pow] at lower
    rw [log_pow] at upper
    norm_num only [Nat.cast_ofNat] at lower upper
    constructor <;> linarith only [lower,upper,log_two_gt_d9,log_two_lt_d9]
  have la := logs (x:=A) (by decide +kernel) (by decide +kernel)
  have lb := logs (x:=B) (by decide +kernel) (by decide +kernel)
  have upper := (le_div_iff₀ (by linarith only [la.1] : 0<log (A:ℝ)-11/10)).mp
    (dusart A (by decide +kernel)).2
  have positive {t : ℝ} (h : 708≤t-11/10) : 0<t-1 := by linarith only [h]
  have lower := (div_le_iff₀ (positive lb.1)).mp
    (dusart B (by decide +kernel)).1
  have left : 708*A.primeCounting≤A := by
    have h := (mul_le_mul_of_nonneg_left la.1 (Nat.cast_nonneg A.primeCounting)).trans upper
    rw [mul_comm] at h
    exact_mod_cast h
  have right : B≤709*B.primeCounting := by
    have h := lower.trans (mul_le_mul_of_nonneg_left lb.2 (Nat.cast_nonneg B.primeCounting))
    rw [mul_comm] at h
    exact_mod_cast h
  have cnt := count_eq A B (by decide +kernel)
  rw [partners_def]
  have enough : 709*A+709*708*2^1007 < 708*B := by decide +kernel
  omega

theorem split_for_near_prime {p q : ℕ} (pm : p∈partners) (qp : q.Prime)
    (near : U-255≤q) (top : q<U) :
    2^2047≤p*q ∧ p*q<2^2048 ∧ EndpointOffsetProduct.probe U (p*q)=some (p,q) := by
  rw [partners_def,mem_filter,mem_Ioc] at pm
  obtain ⟨⟨lo,hi⟩,pp⟩ := pm
  have ord : p≤q := hi.trans ((by decide +kernel : B≤U-255).trans near)
  have unit := pp.coprime_iff_not_dvd.mpr (show ¬p∣6 from fun h =>
    (not_le_of_gt ((by decide +kernel : 6<A).trans lo)) (Nat.le_of_dvd (by decide) h))
  have oq := qp.odd_of_ne_two ((by decide +kernel : 2<U-255).trans_le near).ne'
  have op := Nat.coprime_two_right.mp (unit.of_dvd_right (by decide : 2∣6))
  obtain ⟨j,hj⟩ := op.mul oq
  have div : 4 ∣ weightedStride (p*q) 1 1 := by
    apply Nat.dvd_gcd (by decide)
    exact ⟨j+1,by rw [one_mul,hj]; ring⟩
  have stride := Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by decide : 0<24)) div
  have small := Nat.mul_le_mul (Nat.sub_le_sub_left lo.le U) (Nat.sub_le_sub_left near U)
  have sqhi := Nat.mul_lt_mul_of_pos_right (hi.trans_lt (by decide +kernel : B<U)) qp.pos
  exact ⟨(by decide +kernel : 2^2047≤A*(U-255)).trans (Nat.mul_le_mul lo.le near),
    sqhi.trans_le ((Nat.mul_le_mul_left U top.le).trans (by decide +kernel)),
    (EndpointOffsetProduct.probe_iff unit pp.one_lt ord top.le).mpr
      (small.trans_lt ((by decide +kernel : (U-A)*(U-(U-255))<U*4).trans_le (Nat.mul_le_mul_left U stride)))⟩

/-- Every partner in this band is far from the first ordinary Fermat midpoint. -/
theorem ordinary_misses {p q m : ℕ} (pm : p∈partners) (near : U-255≤q) (top : q<U)
    (midpoint : 2*m=p+q) : ceilSqrt (p*q)+2^1006≤m := by
  rw [partners_def,mem_filter,mem_Ioc] at pm
  obtain ⟨⟨lo,hi⟩,_⟩ := pm
  let d : ℕ := 2^1006
  let g : ℕ := 2^1017-255
  have gap : p+g≤q := by
    have h : B+g≤U-255 := by decide +kernel
    omega
  have mlo : d≤m := by
    have : 2*d≤A := by decide +kernel
    omega
  have mhi : m≤U := by
    have h : B≤U := by decide +kernel
    omega
  have sq := pow_le_pow_left₀ (by positivity : 0≤(g:ℤ))
    (by omega : (g:ℤ)≤(q:ℤ)-p) 2
  have slack := Nat.mul_le_mul_left (8*d) mhi
  have room : 8*d*U≤g^2 := by decide +kernel
  have fit : p*q≤(m-d)^2 := by
    zify [mlo] at slack room midpoint ⊢
    nlinarith only [sq,slack,room,sq_nonneg (d:ℤ),congrArg (fun x : ℤ => x^2) midpoint]
  have root := ceilSqrt_le_iff.mpr fit
  change ceilSqrt (p*q)+d≤m
  omega

/-- Distinct choices of the two primes in these disjoint intervals yield
distinct products. The decoder itself witnesses injectivity. -/
theorem product_count (qs : Finset ℕ) (quality : ∀ q∈qs, q.Prime ∧ U-255≤q ∧ q<U) :
    ((partners ×ˢ qs).image (fun z => z.1*z.2)).card=partners.card*qs.card := by
  have hit {z : ℕ×ℕ} (hz : z∈partners ×ˢ qs) :
      EndpointOffsetProduct.probe U (z.1*z.2)=some z := by
    obtain ⟨hp,hq⟩ := mem_product.mp hz
    obtain ⟨qp,near,top⟩ := quality z.2 hq
    exact (split_for_near_prime hp qp near top).2.2
  rw [card_image_of_injOn,card_product]
  intro x hx y hy same
  exact Option.some.inj ((hit hx).symm.trans ((congrArg (EndpointOffsetProduct.probe U) same).trans (hit hy)))

/-- The near-endpoint primality premises are separate from the interval estimate. -/
theorem two_choices (dusart : Dusart) (first : Nat.Prime (U-105)) (second : Nat.Prime (U-179)) :
    let qs : Finset ℕ := {U-105,U-179}
    let inputs := (partners ×ˢ qs).image (fun z => z.1*z.2)
    2^1008 < inputs.card ∧ ∀ n∈inputs, ∃ p q : ℕ, p∈partners ∧ q∈qs ∧ p*q=n ∧
      2^2047≤n ∧ n<2^2048 ∧ EndpointOffsetProduct.probe U n=some (p,q) := by
  classical
  intro qs inputs
  have qual {q} (h : q∈qs) : q.Prime ∧ U-255≤q ∧ q<U := by
    change q∈({U-105,U-179} : Finset ℕ) at h
    simp only [mem_insert,mem_singleton] at h
    rcases h with rfl|rfl
    · exact ⟨first,by decide +kernel,by decide +kernel⟩
    · exact ⟨second,by decide +kernel,by decide +kernel⟩
  constructor
  · change 2^1008<((partners ×ˢ qs).image (fun z => z.1*z.2)).card
    rw [product_count qs (fun _ h => qual h),show qs.card=2 from by decide +kernel]
    have more := many_partners dusart
    omega
  · intro n hn
    obtain ⟨⟨p,q⟩,hz,rfl⟩ := mem_image.mp hn
    obtain ⟨pm,qm⟩ := mem_product.mp hz
    obtain ⟨qp,near,top⟩ := qual qm
    exact ⟨p,q,pm,qm,rfl,split_for_near_prime pm qp near top⟩

end PrimeFactors.TopPartnerInterval
