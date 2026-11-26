import Mathlib.Tactic

/-! Perturbation arithmetic for the population of balanced prime pairs.
The prime-count discrepancy, mass of each region and smooth density estimates
are hypotheses. This module does not prove an explicit prime number theorem. -/
namespace PrimeFactors.QuantilePopulationBounds

/-- Moving each of the good/bad counts by at most E moves its fraction by
at most E/(G+J). The extremizers move the two counts in opposite directions.
For the degenerate case of an empty population, division is Lean's total division. -/
theorem fraction_error {G J g j E : ℝ} (e : 0 ≤ E) (good : E ≤ G) (bad : E ≤ J)
    (g0 : 0 ≤ g) (j0 : 0 ≤ j) (eg : |g-G| ≤ E) (ej : |j-J| ≤ E) :
    |g/(g+j)-G/(G+J)| ≤ E/(G+J) := by
  obtain ⟨glo,ghi⟩ := abs_le.mp eg
  obtain ⟨jlo,jhi⟩ := abs_le.mp ej
  by_cases empty : G+J=0
  · have x : g=0 := by linarith
    simp [empty, x]
  have D : 0<G+J := lt_of_le_of_ne (by linarith) (Ne.symm empty)
  by_cases missing : g+j=0
  · have x : g=0 := by linarith
    have eq : G=E := by linarith
    simp [x, eq, abs_of_nonneg (div_nonneg e (by linarith : 0≤E+J))]
  have d : 0<g+j := lt_of_le_of_ne (add_nonneg g0 j0) (Ne.symm missing)
  have a : (G-E)*j ≤ g*(J+E) := mul_le_mul (by linarith) (by linarith) j0 g0
  have b : g*(J-E) ≤ (G+E)*j := mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have lo : (G-E)/(G+J) ≤ g/(g+j) := (div_le_div_iff₀ D d).mpr (by nlinarith only [a])
  have hi : g/(g+j) ≤ (G+E)/(G+J) := (div_le_div_iff₀ d D).mpr (by nlinarith only [b])
  rw [sub_div] at lo
  rw [add_div] at hi
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Numeric transfer of the interval discrepancy and mass bounds used with
Dusart, where X is the lower endpoint and E is the error for either region. -/
theorem dusart_error {X ε V D E : ℝ} (size : 0<X) (discrep : 0≤ε)
    (eps : ε ≤ X/680000000) (mass0 : 0≤V) (mass : V≤X/709)
    (total : 306/1000 * X^2 / 710^2 < D) (region : E ≤ ε*(2*V+ε)) :
    E/D < 6834/10^9 := by
  have bound : ε*(2*V+ε) ≤ (X/680000000)*(2*(X/709)+X/680000000) :=
    mul_le_mul eps (by linarith) (by linarith) (by positivity)
  have d : 0<D := lt_of_le_of_lt (by positivity) total
  apply (div_lt_iff₀ d).mpr
  calc E ≤ _ := region.trans bound
       _ < (6834/10^9)*(306/1000 * X^2 / 710^2) := by nlinarith only [sq_pos_of_pos size]
       _ < (6834/10^9)*D := mul_lt_mul_of_pos_left total (by norm_num)

set_option exponentiation.threshold 4096 in
/-- Schoenfeld's stated count error and the single slab's lower mass suffice
at B=2^1024, using B^(3/2)=2^1536 and B²=2^2048. -/
theorem rh_error {E D : ℝ} (region : E ≤ 130*2^1536)
    (slab : (2:ℝ)^2048/(64*710^2) ≤ D) : E/D < 4/10^145 := by
  have d : 0<D := lt_of_lt_of_le (by positivity) slab
  apply (div_lt_iff₀ d).mpr
  calc E ≤ _ := region
       _ < (4/10^145)*(2^2048/(64*710^2)) := by norm_num
       _ ≤ (4/10^145)*D := mul_le_mul_of_nonneg_left slab (by positivity)

/-- The upper bound on a fiber's tilt for z=λ² and λ≤1/2047. -/
theorem fiber_tilt {z : ℝ} (small : z≤1/2047^2) :
    z/(8*(1-z)^2) < 2984/10^11 := by
  have near : 0 < 1-z := by linarith
  have sq : (1-(1/2047^2:ℝ))^2 ≤ (1-z)^2 := by gcongr
  apply (div_lt_iff₀ (by positivity)).mpr
  calc z ≤ _ := small
       _ < (2984/10^11)*(8*(1-1/2047^2)^2) := by norm_num
       _ ≤ (2984/10^11)*(8*(1-z)^2) := by gcongr

/-- A slab of relative mass at least 1/9, λ≥1/4096 and λ≤1/2047
makes the averaged smooth tilt strictly larger than the displayed constant. -/
theorem slab_tilt {z w : ℝ} (lo : 1/4096^2 ≤ z) (hi : z≤1/2047^2) (weight : 1/9≤w) :
    827/10^12 < w*((1-z)*z/8) := by
  have near : 0 < 1-z := by linarith
  have z0 : 0≤z := le_trans (by norm_num) lo
  have h : (1-(1/2047^2:ℝ))*(1/4096^2) ≤ (1-z)*z :=
    mul_le_mul (by linarith) lo (by norm_num) near.le
  calc 827/10^12 < (1/9)*((1-1/2047^2)*(1/4096^2)/8) := by norm_num
       _ ≤ w*((1-z)*z/8) := mul_le_mul weight (by linarith) (by norm_num) (by linarith)

private theorem room {G J E : ℝ} (pos : 0<G+J) (error : E/(G+J)<1/4)
    (lo : 1/4≤G/(G+J)) (hi : G/(G+J)≤3/4) : E≤G ∧ E≤J := by
  have err := (div_lt_iff₀ pos).mp error
  have gLo := (le_div_iff₀ pos).mp lo
  have gHi := (div_le_iff₀ pos).mp hi
  constructor <;> linarith

/-- Here the analytic upper tilt is for the full smooth population. Given
the paper's Dusart hypotheses, the covered fraction lies in (0.499993,0.500007). -/
theorem dusart_coverage {G J g j E X ε V : ℝ} (e : 0≤E)
    (g0 : 0≤g) (j0 : 0≤j) (eg : |g-G|≤E) (ej : |j-J|≤E)
    (size : 0<X) (eps0 : 0≤ε) (eps : ε≤X/680000000) (mass0 : 0≤V) (mass : V≤X/709)
    (total : 306/1000 * X^2 / 710^2 < G+J) (region : E≤ε*(2*V+ε))
    (tilt0 : 0≤1/2-G/(G+J)) (tilt : 1/2-G/(G+J) ≤ 2984/10^11) :
    499993/10^6 < g/(g+j) ∧ g/(g+j) < 500007/10^6 := by
  have ratio := dusart_error size eps0 eps mass0 mass total region
  obtain ⟨good,bad⟩ := room (lt_of_le_of_lt (by positivity) total) (lt_trans ratio (by norm_num))
    (by linarith only [tilt]) (by linarith only [tilt0])
  have span := abs_le.mp (fraction_error e good bad g0 j0 eg ej)
  constructor <;> linarith [span.1,span.2]

/-- The only RH-dependent input here is the supplied count estimate. The
smooth-tilt bounds, region counts and slab mass also enter as hypotheses. -/
theorem rh_coverage {G J g j E : ℝ} (e : 0≤E)
    (g0 : 0≤g) (j0 : 0≤j) (eg : |g-G|≤E) (ej : |j-J|≤E)
    (region : E≤130*2^1536) (slab : (2:ℝ)^2048/(64*710^2)≤G+J)
    (tiltLo : 827/10^12 ≤ 1/2-G/(G+J)) (tiltHi : 1/2-G/(G+J) ≤ 2984/10^11) :
    499999970/10^9 < g/(g+j) ∧ g/(g+j) < 4999999995/10^10 := by
  have ratio := rh_error region slab
  obtain ⟨good,bad⟩ := room (lt_of_lt_of_le (by positivity) slab) (lt_trans ratio (by norm_num))
    (by linarith only [tiltHi]) (by linarith only [tiltLo])
  have span := abs_le.mp (fraction_error e good bad g0 j0 eg ej)
  constructor <;> linarith only [span.1,span.2,ratio,tiltLo,tiltHi]

/-- Write S=√B. The bin's one-dimensional support has smooth mass at most
`d*S²/709`. The two discrepancy bounds then imply the stated region error. -/
theorem prefix_region {d S ε V E : ℝ} (size : 0<S) (v0 : 0≤V) (e0 : 0≤ε)
    (schoenfeld : ε≤61*S) (localErr : ε≤d*S^2/709) (localMass : V≤d*S^2/709)
    (region : E≤ε*(2*V+ε)) : E≤183*d*S^3/709 := by
  calc E ≤ _ := region
       _ ≤ (61*S)*(3*(d*S^2/709)) := mul_le_mul schoenfeld (by linarith) (by linarith) (by positivity)
       _ = _ := by ring

/-- The region error divided by the geometric lower bound for one bin. -/
theorem prefix_ratio {δ d S E D : ℝ} (width : 0<δ) (d0 : 0<d) (size : 0<S)
    (count : E≤183*d*S^3/709) (mass : δ*d*S^4/(4*710^2)≤D) : E/D<2^19/(δ*S) := by
  have pos : 0<D := lt_of_lt_of_le (by positivity) mass
  apply (div_lt_div_iff₀ pos (mul_pos width size)).mpr
  calc E*(δ*S) ≤ (183*d*S^3/709)*(δ*S) := mul_le_mul_of_nonneg_right count (by positivity)
       _ < 2^19*(δ*d*S^4/(4*710^2)) := by
         have h : 0<δ*d*S^4 := by positivity
         nlinarith only [h]
       _ ≤ 2^19*D := mul_le_mul_of_nonneg_left mass (by positivity)

set_option exponentiation.threshold 4096 in
/-- At normalized width `2⁻⁴⁷⁵`, the error bound is below `2⁻¹⁸` for
every individual bin, including the final bin with `d=δ`. -/
theorem prefix_error_475 {d E D : ℝ} (d0 : 0<d) (count : E≤183*d*2^1536/709)
    (mass : (1/2^475)*d*2^2048/(4*710^2)≤D) : E/D<1/2^18 := by
  have h := prefix_ratio (E:=E) (D:=D) (δ:=1/2^475) (S:=2^512) (by positivity) d0 (by positivity)
    (by simpa only [←pow_mul] using count) (by simpa only [←pow_mul] using mass)
  exact h.trans_eq (by norm_num)

/-- Convert the two raw count errors for a particular prefix into the error
on its probability of containing the true sum. -/
theorem prefix_fraction_475 {G J g j E d : ℝ} (e : 0≤E) (g0 : 0≤g) (j0 : 0≤j)
    (eg : |g-G|≤E) (ej : |j-J|≤E) (tilt : |1/2-G/(G+J)| ≤ 2984/10^11)
    (d0 : 0<d) (count : E≤183*d*2^1536/709)
    (mass : (1/2^475)*d*2^2048/(4*710^2)≤G+J) : |g/(g+j)-G/(G+J)|<1/2^18 := by
  have ratio := prefix_error_475 d0 count mass
  obtain ⟨lo,hi⟩ := abs_le.mp tilt
  obtain ⟨good,bad⟩ := room (lt_of_lt_of_le (by positivity) mass) (lt_trans ratio (by norm_num))
    (by linarith only [hi]) (by linarith only [lo])
  exact (fraction_error e good bad g0 j0 eg ej).trans_lt ratio

/-- `w` is the probability of a bin, `f` is its actual inner fraction, `z`
its smooth inner fraction, and `a` is the probability of choosing the inner
branch given just that bin. The bound holds for every such decision rule. -/
theorem prefix_accuracy_475 {ι : Type*} (bins : Finset ι) (w f z a : ι → ℝ)
    (nonneg : ∀ i∈bins, 0≤w i) (total : ∑ i∈bins, w i=1)
    (err : ∀ i∈bins, |f i-z i|≤1/2^18) (tilt : ∀ i∈bins, |1/2-z i|≤2984/10^11)
    (choice : ∀ i∈bins, 0≤a i ∧ a i≤1) :
    ∑ i∈bins, w i*(a i*f i+(1-a i)*(1-f i)) < 50000385/10^8 := by
  let C : ℝ := 1/2+1/2^18+2984/10^11
  have pointwise (i) (h : i∈bins) : a i*f i+(1-a i)*(1-f i) ≤ C := by
    have ⟨el,eh⟩ := abs_le.mp (err i h)
    have ⟨tl,th⟩ := abs_le.mp (tilt i h)
    have ⟨al,ah⟩ := choice i h
    have one : f i≤C := by dsimp [C]; linarith
    have two : 1-f i≤C := by dsimp [C]; linarith
    calc _ ≤ a i*C+(1-a i)*C := add_le_add (mul_le_mul_of_nonneg_left one al)
           (mul_le_mul_of_nonneg_left two (by linarith))
         _ = C := by ring
  calc _ ≤ ∑ i∈bins, w i*C := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
           (pointwise i hi) (nonneg i hi))
       _ = C := by rw [←Finset.sum_mul,total,one_mul]
       _ < _ := by norm_num [C]

end PrimeFactors.QuantilePopulationBounds
