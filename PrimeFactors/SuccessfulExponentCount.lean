import PrimeFactors.ConvergentGcdThreshold
import PrimeFactors.UniformDivisorCount

/-! Count successful positive exponents on one fixed input. The divisor set
of F is used for the count. Enumerating that set from N is a separate problem. -/
namespace PrimeFactors.SuccessfulExponentCount

open Finset

/-- The reduced numerator satisfies a² F (N−F)<N² whenever 1≤E≤N
and the target ratio occurs among the ordinary convergents. -/
theorem numerator_bound {N E F : ℕ} (ep : 0<E) (en : E≤N) (fp : 0<F) (fn : F≤N)
    (present : ∃ i, (E:ℚ)/F=((E:ℝ)/N).convergent i) :
    (E/E.gcd F)^2*(F*(N-F))<N^2 := by
  let g := E.gcd F
  let a := E/g
  have ga : a*g=E := Nat.div_mul_cancel (Nat.gcd_dvd_left E F)
  have ap : 0<a := Nat.pos_of_ne_zero (fun h => by
    have pos : 0<a*g := by rwa [ga]
    rw [h,zero_mul] at pos
    exact lt_irrefl _ pos)
  have h := ConvergentGcdThreshold.necessary ep fp fn present
  change E*F*(N-F)<N*g^2 at h
  apply Nat.lt_of_mul_lt_mul_right (a:=E)
  change a^2*(F*(N-F))*E<N^2*E
  calc
    _ = (E*F*(N-F))*a^2 := by ring
    _ < (N*g^2)*a^2 := Nat.mul_lt_mul_of_pos_right h (Nat.pow_pos ap)
    _ = (N*E)*E := by rw [←ga]; ring
    _ ≤ N^2*E := Nat.mul_le_mul_right E (by simpa [pow_two] using Nat.mul_le_mul_left N en)

/-- Every successful E can be written a·g with g a divisor of F and a<A
as soon as the size-only bound N²≤A²F(N−F) holds. -/
theorem cover {N E F A : ℕ} (ep : 0<E) (en : E≤N) (fp : 0<F) (fn : F≤N)
    (cap : N^2≤A^2*(F*(N-F)))
    (present : ∃ i, (E:ℚ)/F=((E:ℝ)/N).convergent i) :
    ∃ a<A, ∃ g∈F.divisors, a*g=E := by
  have h := (numerator_bound ep en fp fn present).trans_le cap
  refine ⟨E/E.gcd F,?_,E.gcd F,Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right ..,fp.ne'⟩,
    Nat.div_mul_cancel (Nat.gcd_dvd_left ..)⟩
  exact (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp (Nat.lt_of_mul_lt_mul_right h)

/-- The positive exponents up to and including N that actually put E/F
in the ordinary continued fraction of E/N. -/
noncomputable def hits (N F : ℕ) : Finset ℕ := by
  classical
  exact (Icc 1 N).filter fun E => ∃ i, (E:ℚ)/F=((E:ℝ)/N).convergent i

theorem count {N F A : ℕ} (fp : 0<F) (fn : F≤N) (cap : N^2≤A^2*(F*(N-F))) :
    (hits N F).card≤F.divisors.card*A := by
  classical
  let pairs := (range A) ×ˢ F.divisors
  have subset : hits N F ⊆ pairs.image (fun x => x.1*x.2) := by
    intro E he
    obtain ⟨bounds,hit⟩ := mem_filter.mp he
    obtain ⟨ep,en⟩ := mem_Icc.mp bounds
    obtain ⟨a,ha,g,hg,eq⟩ := cover ep en fp fn cap hit
    exact mem_image.mpr ⟨(a,g),mem_product.mpr ⟨mem_range.mpr ha,hg⟩,eq⟩
  calc
    _ ≤ _ := card_le_card subset
    _ ≤ pairs.card := card_image_le
    _ = _ := by simp [pairs,Nat.mul_comm]

/-- For 4≤p<q≤U, N²≤U F (N−F). This estimate needs no average over
products and no primality assumption. -/
theorem size_cap {p q U : ℕ} (hp : 4≤p) (pq : p<q) (bound : q≤U) :
    (p*q)^2 ≤ U*(((p-1)*(q-1))*(p*q-(p-1)*(q-1))) := by
  have hq : 4≤q := by omega
  obtain ⟨u,hu⟩ := Nat.exists_eq_add_of_le hp
  obtain ⟨v,hv⟩ := Nat.exists_eq_add_of_le hq
  have psub : p-1=3+u := by omega
  have qsub : q-1=3+v := by omega
  have big : p*q ≤ 2*((p-1)*(q-1)) := by rw [psub,qsub,hu,hv]; nlinarith
  have ds : p*q-(p-1)*(q-1)=p+q-1 := by
    have add : p*q=(p-1)*(q-1)+(p+q-1) := by
      have d : p+q-1=7+u+v := by omega
      rw [psub,qsub,d,hu,hv]
      ring
    omega
  have lower : 2*(p*q) ≤ U*(p*q-(p-1)*(q-1)) := calc
    2*(p*q)=q*(2*p) := by ring
    _ ≤ U*(p*q-(p-1)*(q-1)) := Nat.mul_le_mul bound (by rw [ds]; omega)
  calc
    _ = (p*q)*(p*q) := by ring
    _ ≤ (2*((p-1)*(q-1)))*(p*q) := Nat.mul_le_mul_right _ big
    _ = ((p-1)*(q-1))*(2*(p*q)) := by ring
    _ ≤ ((p-1)*(q-1))*(U*(p*q-(p-1)*(q-1))) := Nat.mul_le_mul_left _ lower
    _ = _ := by ring

/-- On a fixed product of two factors below 2^1024, the reduced numerator
of an actually recovered positive ratio is below 2^512. -/
theorem numerator_2048 {p q E : ℕ} (hp : 4≤p) (pq : p<q) (wq : q<2^1024)
    (ep : 0<E) (en : E≤p*q)
    (present : ∃ i, (E:ℚ)/((p-1)*(q-1):ℕ)=((E:ℝ)/(p*q:ℕ)).convergent i) :
    E/E.gcd ((p-1)*(q-1))<2^512 := by
  have fp : 0<(p-1)*(q-1) := Nat.mul_pos (by omega) (by omega)
  have fn : (p-1)*(q-1)≤p*q := Nat.mul_le_mul (Nat.sub_le ..) (Nat.sub_le ..)
  have cap := size_cap hp pq wq.le
  rw [show (2:ℕ)^1024=(2^512)^2 by rw [←pow_mul]] at cap
  have bound := (numerator_bound ep en fp fn present).trans_le cap
  exact (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp (Nat.lt_of_mul_lt_mul_right bound)

/-- Fewer than 2^752 positive exponent choices work on each such fixed
product. The range for a is [0,2^512), and F has fewer than 2^240 divisors. -/
theorem count_2048 {p q : ℕ} (hp : 4≤p) (pq : p<q) (wq : q<2^1024) :
    (hits (p*q) ((p-1)*(q-1))).card<2^752 := by
  have fp : 0<(p-1)*(q-1) := Nat.mul_pos (by omega) (by omega)
  have fn : (p-1)*(q-1)≤p*q := Nat.mul_le_mul (Nat.sub_le ..) (Nat.sub_le ..)
  have pw : p*q<2^2049 := calc
    _ ≤ q*q := Nat.mul_le_mul_right q pq.le
    _ < (2^1024)^2 := by simpa only [pow_two] using Nat.pow_lt_pow_left wq (by decide : 2≠0)
    _ ≤ _ := by decide +kernel
  have cap := size_cap hp pq wq.le
  rw [show (2:ℕ)^1024=(2^512)^2 by rw [←pow_mul]] at cap
  have tau := UniformDivisorCount.below_2049 fp (fn.trans_lt pw)
  calc
    _ ≤ _ := count fp fn cap
    _ < 2^240*2^512 := Nat.mul_lt_mul_of_pos_right tau (by positivity)
    _ = _ := by rw [←pow_add]

/-- Uniform sampling from [1,N] on each individual 2048-bit product has
success probability strictly below 2^-1295, expressed with integer counts. -/
theorem rate_2048 {p q : ℕ} (hp : 4≤p) (pq : p<q) (wq : q<2^1024) (width : 2^2047≤p*q) :
    2^1295*(hits (p*q) ((p-1)*(q-1))).card<p*q := calc
  _ < 2^1295*2^752 := Nat.mul_lt_mul_of_pos_left (count_2048 hp pq wq) (by positivity)
  _ = 2^2047 := by rw [←pow_add]
  _ ≤ _ := width

end PrimeFactors.SuccessfulExponentCount
