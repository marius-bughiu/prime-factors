import PrimeFactors.ChebyshevPrimeSample
import PrimeFactors.SmoothOrderTail

/-! A positive smooth divisor of a product splits between its two factors. Counting multiples
of both parts bounds the prevalence of a large smooth divisor of a semiprime's totient. -/
namespace PrimeFactors.SmoothTotientTail

open Finset MixedPrefixSample

set_option exponentiation.threshold 4096

noncomputable def exceptional (B T : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact eligible.filter fun z => ∃ d ∈ Nat.smoothNumbers B, d ∣ (z.1-1)*(z.2-1) ∧ T ≤ d

theorem mem_exceptional {B T : ℕ} {z : ℕ × ℕ} : z ∈ exceptional B T ↔ z ∈ eligible ∧
    ∃ d ∈ Nat.smoothNumbers B, d ∣ (z.1-1)*(z.2-1) ∧ T ≤ d := by
  classical exact mem_filter

private def multiples (U d : ℕ) := ((Ioc 0 U).filter (d ∣ ·)).image (· + 1)

private def rectangle (U T : ℕ) (de : ℕ × ℕ) :=
  if T ≤ de.1*de.2 then multiples U de.1 ×ˢ multiples U de.2 else ∅

private theorem contains {B T U x y d : ℕ}
    (hx : x ∈ Ioc 0 U) (hy : y ∈ Ioc 0 U) (smooth : d ∈ Nat.smoothNumbers B)
    (dv : d ∣ x*y) (large : T≤d) :
    (x+1,y+1) ∈ ((Nat.smoothNumbersUpTo U B) ×ˢ (Nat.smoothNumbersUpTo U B)).biUnion
        (rectangle U T) := by
  obtain ⟨a,b,ax,by',rfl⟩ := exists_dvd_and_dvd_of_dvd_mul dv
  obtain ⟨xp,xu⟩ := mem_Ioc.mp hx
  obtain ⟨yp,yu⟩ := mem_Ioc.mp hy
  apply mem_biUnion.mpr
  refine ⟨(a,b),mem_product.mpr ⟨?_,?_⟩,?_⟩
  · exact Nat.mem_smoothNumbersUpTo.mpr ⟨(Nat.le_of_dvd xp ax).trans xu,
      Nat.mem_smoothNumbers_of_dvd smooth (dvd_mul_right ..)⟩
  · exact Nat.mem_smoothNumbersUpTo.mpr ⟨(Nat.le_of_dvd yp by').trans yu,
      Nat.mem_smoothNumbers_of_dvd smooth (dvd_mul_left ..)⟩
  · rw [rectangle,if_pos large]
    exact mem_product.mpr ⟨mem_image.mpr ⟨x,mem_filter.mpr ⟨hx,ax⟩,rfl⟩,
      mem_image.mpr ⟨y,mem_filter.mpr ⟨hy,by'⟩,rfl⟩⟩

private theorem count_rectangle {U T a b : ℕ} {s : ℝ} (s1 : s≤1)
    (ap : 0<a) (bp : 0<b) :
    (T:ℝ)^(1-s) * (rectangle U T (a,b)).card ≤
      ((U:ℝ)*(a:ℝ)^(-s))*((U:ℝ)*(b:ℝ)^(-s)) := by
  have ar : (0:ℝ)<a := by exact_mod_cast ap
  have br : (0:ℝ)<b := by exact_mod_cast bp
  have denom : (0:ℝ)<(a:ℝ)*b := mul_pos ar br
  by_cases ht : T≤a*b
  · have one (d : ℕ) : ((multiples U d).card:ℝ) ≤ (U:ℝ)/d := by
      apply le_trans _ (Nat.cast_div_le (α:=ℝ))
      norm_cast
      exact card_image_le.trans_eq (Nat.Ioc_filter_dvd_card_eq_div ..)
    rw [rectangle,if_pos ht,card_product,Nat.cast_mul]
    have powle := Real.rpow_le_rpow (Nat.cast_nonneg T)
      (show (T:ℝ)≤(a:ℝ)*b by exact_mod_cast ht) (sub_nonneg.mpr s1)
    calc
      _ ≤ ((a:ℝ)*b)^(1-s)*(((U:ℝ)/a)*(U/b)) := by
        apply mul_le_mul powle (mul_le_mul (one a) (one b) (Nat.cast_nonneg _) (by positivity))
          (by positivity) (Real.rpow_nonneg denom.le _)
      _ = _ := by
        rw [Real.rpow_sub denom,Real.rpow_one,Real.mul_rpow ar.le br.le,
          Real.rpow_neg ar.le,Real.rpow_neg br.le]
        field_simp
        ring
  · rw [rectangle,if_neg ht,card_empty,Nat.cast_zero,mul_zero]
    positivity

/-- Bound a finite set of shifted positive coordinate pairs, without any primality assumption.
A different divisor at or above T may witness each pair. -/
theorem count_box (U B T : ℕ) (S : Finset (ℕ × ℕ)) {s : ℝ} (hs : 0<s) (s1 : s≤1)
    (covered : ∀ z∈S, ∃ x ∈ Ioc 0 U, ∃ y ∈ Ioc 0 U, z=(x+1,y+1) ∧
      ∃ d ∈ Nat.smoothNumbers B, d∣x*y ∧ T≤d) :
    (T:ℝ)^(1-s) * S.card ≤
      ((U:ℝ) * ∏ p ∈ B.primesBelow, (1-(p:ℝ)^(-s))⁻¹)^2 := by
  classical
  let D := Nat.smoothNumbersUpTo U B
  let w (d : ℕ) := (U:ℝ)*(d:ℝ)^(-s)
  have nonneg (d : ℕ) : 0≤w d := by dsimp [w]; positivity
  have positive {d : ℕ} (hd : d∈D) : 0<d :=
    Nat.pos_of_ne_zero (Nat.mem_smoothNumbersUpTo.mp hd).2.1
  have cover : S ⊆ (D ×ˢ D).biUnion (rectangle U T) := by
    intro z hz
    obtain ⟨x,xh,y,yh,rfl,d,hd,dv,large⟩ := covered z hz
    exact contains xh yh hd dv large
  have total : (S.card:ℝ) ≤ ∑ v ∈ D ×ˢ D, ((rectangle U T v).card:ℝ) := by
    exact_mod_cast ((card_le_card cover).trans card_biUnion_le)
  calc
    _ ≤ (T:ℝ)^(1-s) * ∑ v ∈ D ×ˢ D, ((rectangle U T v).card:ℝ) :=
      mul_le_mul_of_nonneg_left total (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ ∑ v ∈ D ×ˢ D, w v.1 * w v.2 := by
      rw [mul_sum]
      apply sum_le_sum
      rintro ⟨a,b⟩ hv
      exact count_rectangle s1 (positive (mem_product.mp hv).1) (positive (mem_product.mp hv).2)
    _ = (∑ d ∈ D, w d)^2 := by rw [sum_product,pow_two,sum_mul_sum]
    _ ≤ _ := by
      apply pow_le_pow_left₀ (sum_nonneg fun d _ => nonneg d) _ 2
      dsimp only [w]
      rw [←mul_sum]
      exact mul_le_mul_of_nonneg_left (SmoothOrderTail.finite_mass U B hs) (Nat.cast_nonneg _)

attribute [local irreducible] eligible sample ordered primes exceptional

private theorem shifted {p : ℕ} (hp : p∈primes) :
    p-1 ∈ Ioc 0 (2^1024) ∧ p=(p-1)+1 := by
  rw [primes,mem_filter] at hp
  have bounds := mem_Ico.mp hp.1
  change 2^1023≤p ∧ p<2*2^1023 at bounds
  rw [mem_Ioc]
  omega

/-- Upper bound on the eligible 2048-bit sample using the full smooth Euler product. -/
theorem population {s : ℝ} (hs : 0<s) (s1 : s≤1) (T B : ℕ) :
    (T:ℝ)^(1-s) * (exceptional B T).card ≤
      ((2:ℝ)^1024 * ∏ p ∈ B.primesBelow, (1-(p:ℝ)^(-s))⁻¹)^2 := by
  have result := count_box (2^1024) B T (exceptional B T) hs s1 (by
    intro z hz
    obtain ⟨he,d,hd,dv,large⟩ := mem_exceptional.mp hz
    rw [eligible,sample,mem_filter] at he
    obtain ⟨hp,hq,_⟩ := mem_ordered.mp he.1
    obtain ⟨hl,ph⟩ := shifted hp
    obtain ⟨hr,qh⟩ := shifted hq
    exact ⟨z.1-1,hl,z.2-1,hr,Prod.ext ph qh,d,hd,dv,large⟩)
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using result

/-- Any smooth exponent with a large gcd with the totient supplies a counted divisor. -/
theorem of_gcd {z : ℕ × ℕ} {E B T : ℕ} (he : z ∈ eligible)
    (smooth : E ∈ Nat.smoothNumbers B) (large : T ≤ E.gcd ((z.1-1)*(z.2-1))) :
    z ∈ exceptional B T :=
  mem_exceptional.mpr ⟨he,_,Nat.mem_smoothNumbers_of_dvd smooth (Nat.gcd_dvd_left ..),
    Nat.gcd_dvd_right ..,large⟩

/-- With the finite Euler cap supplied separately, fewer than one in 2^553 eligible products
has any 1500-smooth divisor at least 2^1024 in its totient. -/
theorem rare553 (cap : (∏ p ∈ (1501:ℕ).primesBelow, (1-(p:ℝ)^(-(1/4:ℝ)))⁻¹) ≤ (2:ℝ)^94) :
    2^553*(exceptional 1501 (2^1024)).card < eligible.card := by
  let S := exceptional 1501 (2^1024)
  have bounded := population (s:=(1/4:ℝ)) (by norm_num) (by norm_num) (2^1024) 1501
  have weight : (2:ℝ)^768 ≤ ((2^1024:ℕ):ℝ)^(1-(1/4:ℝ)) := by
    rw [Nat.cast_pow,Nat.cast_ofNat,←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2),
      ←Real.rpow_natCast 2 (768:ℕ)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have mass := SmoothOrderTail.finite_mass 1 1501 (s:=1/4) (by norm_num)
  have nn : 0 ≤ ∏ p ∈ (1501:ℕ).primesBelow, (1-(p:ℝ)^(-(1/4:ℝ)))⁻¹ :=
    (sum_nonneg fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) _).trans mass
  have bound : (2:ℝ)^768 * S.card ≤ ((2:ℝ)^1024 * (2:ℝ)^94)^2 :=
    ((mul_le_mul_of_nonneg_right weight (Nat.cast_nonneg _)).trans bounded).trans
      (pow_le_pow_left₀ (mul_nonneg (by positivity) nn)
        (mul_le_mul_of_nonneg_left cap (by positivity)) 2)
  have realSize : (S.card:ℝ) ≤ (2:ℝ)^1468 := by
    apply le_of_mul_le_mul_left (a:=(2:ℝ)^768) _ (by positivity)
    exact bound.trans_eq (by norm_num)
  have size : S.card ≤ 2^1468 := by exact_mod_cast realSize
  apply Nat.lt_of_mul_lt_mul_left (a:=21000000)
  calc
    _ ≤ 21000000*(2^553*2^1468) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ size)
    _ < 2^2046 := by decide +kernel
    _ < _ := ChebyshevPrimeSample.eligible_count

end PrimeFactors.SmoothTotientTail
