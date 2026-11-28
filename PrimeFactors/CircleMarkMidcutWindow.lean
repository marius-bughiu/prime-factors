import PrimeFactors.CircleMarkMidcutPrecision
import PrimeFactors.CircleMarkMidcutSampling

/-! A supplied approximation to the all-residue signed midpoint mean yields an
explicit finite interval of odd candidates for the smaller prime. -/
namespace PrimeFactors.CircleMarkMidcutWindow

open Finset CircleMarkMidcutReadout CircleMarkMidcutPrecision CircleMarkMidcutSampling
open CircleMarkStoppingPrecision

/-- Convert a rational approximation to the signed mean into a factor estimate. -/
noncomputable def center (n : ℕ) (y : ℚ) : ℚ := 1+(n:ℚ)/cutoff n*y

/-- All odd integers at distance strictly below the specified radius. -/
noncomputable def candidates (x : ℚ) (r : ℕ) : Finset ℤ :=
  (Ioo ⌊(x-r-1)/2⌋ ⌈(x+r-1)/2⌉).image (fun k : ℤ => 2*k+1)

theorem mem_candidates {z : ℤ} {x : ℚ} {r : ℕ} :
    z∈candidates x r ↔ Odd z ∧ |x-z|<r := by
  simp only [candidates,mem_image,mem_Ioo,Int.floor_lt,Int.lt_ceil]
  constructor
  · rintro ⟨k,⟨lo,hi⟩,rfl⟩
    refine ⟨⟨k,rfl⟩,?_⟩
    rw [abs_lt]; push_cast; constructor <;> linarith
  · rintro ⟨⟨k,rfl⟩,h⟩
    rw [abs_lt] at h
    push_cast at h
    exact ⟨k,⟨by linarith,by linarith⟩,rfl⟩

/-- The strict radius r can accommodate at most r points of the odd lattice. -/
theorem candidate_count (x : ℚ) (r : ℕ) : (candidates x r).card≤r := by
  let a := (x-r-1)/2
  have up : (x+r-1)/2=a+(r:ℤ) := by dsimp [a]; push_cast; ring
  have gap : ⌈a⌉≤⌊a⌋+1 := Int.ceil_le.mpr (by
    push_cast
    exact (Int.lt_floor_add_one a).le)
  apply card_image_le.trans
  rw [Int.card_Ioo,up,Int.ceil_add_intCast]
  change (⌈a⌉+r-⌊a⌋-1).toNat≤r
  omega

set_option exponentiation.threshold 8192

/-- For two full-width primes, an error of at most 2⁻⁶⁴ in the supplied
mean gives a strict 2⁹⁶² radius for the smaller prime. -/
theorem reading_error {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (lo : 2^1023≤p) (order : p<q) (hi : q<2^1024) {y : ℚ}
    (reading : |y-(imbalance (p*q):ℚ)/(p*q:ℕ)|≤1/(2:ℚ)^64) :
    |center (p*q) y-p| < (2:ℚ)^962 := by
  let n : ℚ := (p*q:ℕ)
  let k : ℚ := cutoff (p*q)
  have pgt := (by decide +kernel : 2<2^1023).trans_le lo
  have np : 0<n := by dsimp [n]; exact_mod_cast Nat.mul_pos (by omega : 0<p) (by omega : 0<q)
  have kp : 0<k := by dsimp [k]; exact_mod_cast cutoff_pos order pgt.ne'
  have scale := full_scale lo order hi
  change n*(1/2^1026)<k at scale
  rw [mul_one_div, div_lt_iff₀ (by positivity : (0:ℚ)<2^1026)] at scale
  have sk : n/k<(2:ℚ)^1026 := (div_lt_iff₀ kp).mpr (by simpa only [mul_comm] using scale)
  have mass : (imbalance (p*q):ℚ)=k*((p:ℚ)-1) := by
    dsimp only [k]; exact_mod_cast imbalance_eq order pgt.ne' (pgt.trans order).ne'
  have eqn : center (p*q) y-p=n/k*(y-(imbalance (p*q):ℚ)/n) := by
    change 1+n/k*y-p=_
    rw [mass]
    field_simp
    ring
  rw [eqn,abs_mul,abs_of_pos (div_pos np kp)]
  calc _ ≤ n/k*(1/2^64) := mul_le_mul_of_nonneg_left reading (div_pos np kp).le
       _ < (2:ℚ)^1026*(1/2^64) := mul_lt_mul_of_pos_right sk (by positivity)
       _ = _ := by norm_num

/-- The interval depends only on the product and the supplied mean. -/
theorem full_window {p q : ℕ} [hp : Fact p.Prime] [Fact q.Prime]
    (lo : 2^1023≤p) (order : p<q) (hi : q<2^1024) {y : ℚ}
    (reading : |y-(imbalance (p*q):ℚ)/(p*q:ℕ)|≤1/(2:ℚ)^64) :
    (p:ℤ)∈candidates (center (p*q) y) (2^962) ∧
      (candidates (center (p*q) y) (2^962)).card≤2^962 := by
  have pgt := (by decide +kernel : 2<2^1023).trans_le lo
  refine ⟨mem_candidates.mpr ⟨by exact_mod_cast hp.out.odd_of_ne_two pgt.ne',?_⟩,candidate_count ..⟩
  exact_mod_cast reading_error lo order hi reading

/-- For a 2048-bit product, the ordinary empirical midpoint estimate needs
over 2¹²³ independent draws with replacement to reach a 2⁹⁶² RMS error. -/
theorem draws_for_window {p q draws : ℕ} [Fact p.Prime] [Fact q.Prime]
    (lo : 2^2047≤p*q) (order : p<q) (op : p≠2) (oq : q≠2) (dp : 0<draws)
    (rms : Real.sqrt ((meanSquare (estimate (p*q)) p draws:ℚ):ℝ)<2^962) : 2^123<draws := by
  rw [sample_error order op oq dp] at rms
  have b := (Real.sqrt_lt' (by positivity : (0:ℝ)<2^962)).mp rms
  have err : variance (p*q) p/(draws:ℚ)<((2:ℚ)^962)^2 := by exact_mod_cast b
  have upper := (div_lt_iff₀ (by exact_mod_cast dp : 0<(draws:ℚ))).mp err
  have cap : (2:ℚ)^2047≤(p*q:ℕ) := by exact_mod_cast lo
  have bound : ((2:ℚ)^962)^2*2^123 < ((2:ℚ)^962)^2*draws := calc
    _ = 2^2047 := by norm_num
    _ ≤ _ := cap
    _ < _ := (variance_gt_product order op oq).trans upper
  exact_mod_cast (lt_of_mul_lt_mul_left bound (by positivity))

end PrimeFactors.CircleMarkMidcutWindow
