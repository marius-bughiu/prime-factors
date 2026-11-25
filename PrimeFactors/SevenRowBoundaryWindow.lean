import PrimeFactors.BoundaryWindowSelection
import PrimeFactors.SiftedDivisorWindow

namespace PrimeFactors.SevenRowBoundaryWindow

open BoundaryWindowSelection AnalyticDivisorWindow

/-- Radius measured in parity indices, corresponding to a physical span of four radii. -/
def radius : ℕ := 5*2^437

set_option exponentiation.threshold 4096 in
/-- The physical diameter has room to round the factor's lower bound down by one. -/
theorem diameter : (2:ℝ)^1024*(Real.pi/(3*2^583))+1 ≤ 4*(radius:ℝ) := by
  norm_num [radius]
  linarith [Real.pi_lt_d2]

/-- An integer lower endpoint calculated from the product and the two observation batches. -/
noncomputable def lowerEndpoint (n : ℕ) (read : ℕ → ℝ) : ℕ :=
  ⌊lowerValue n (left 583 (wave n read))⌋₊

private theorem costs (K : ℕ) (y : ℕ → ℝ) :
    (queries K y).card ≤ 2*(K+1) ∧ (∀ t∈queries K y, 0<t ∧ t≤2^(K+1)) :=
  ⟨query_count K y,fun t ht => query_heights (K:=K) (y:=y) (t:=t) ht⟩

set_option exponentiation.threshold 4096 in
/-- At most 1,168 bounded-error observations determine one seven-row window containing
the larger prime of every qualifying factorization. The endpoint is rounded down. -/
theorem selection {n : ℕ} [NeZero n] (large : 2^2047≤n) (odd : Odd n) (cop : n.Coprime 45360)
    (read : ℕ → ℝ) (accurate : ∀ t∈queries 583 (wave n read), |read t-boundaryProbe n t|≤1/8) :
    let T := queries 583 (wave n read)
    let C := center (lowerEndpoint n read) radius
    T.card≤1168 ∧ (∀ t∈T, 0<t ∧ t≤2^584) ∧
    ∃ F : Polynomial ℤ, F≠0 ∧ F.roots.toFinset.card≤6 ∧
      ∀ p q : ℕ, p*q=n → p.Prime → q.Prime → p<q → q≤2*p → q<2^1024 →
      ∃ x : ℤ, (q:ℤ)=(C:ℤ)+2*x ∧ |x|≤(radius:ℤ) ∧ F.eval x=0 := by
  have schedule := costs 583 (wave n read)
  norm_num only [Nat.reduceAdd,Nat.reduceMul] at schedule
  refine ⟨schedule.1,schedule.2,?_⟩
  let C := center (lowerEndpoint n read) radius
  obtain ⟨F,nz,count,atWindow⟩ := SiftedDivisorWindow.coupled_factorial_window large cop odd (C:ℤ)
    (by exact_mod_cast center_odd (lowerEndpoint n read) radius)
  refine ⟨F,nz,count,?_⟩
  intro p q pair hp hq ord bal cap
  subst n
  have fits := fits_readings hp hq ord bal read accurate
  obtain ⟨lo,hi⟩ := enclosure fits
  have shift : Real.log q-Real.log (p*q:ℕ)/2=(Real.log q-Real.log p)/2 := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
    ring
  rw [←shift] at lo hi
  obtain ⟨lb,dist⟩ := lowerValue_bounds (by exact_mod_cast hq.pos)
    (by exact_mod_cast cap.le : (q:ℝ)≤(2:ℝ)^1024) lo hi
  let X := lowerValue (p*q) (left 583 (wave (p*q) read))
  have down : (lowerEndpoint (p*q) read:ℝ)≤X := Nat.floor_le (Real.exp_pos _).le
  have next : X<(lowerEndpoint (p*q) read:ℝ)+1 := Nat.lt_floor_add_one _
  have room : (q:ℝ)-(lowerEndpoint (p*q) read:ℝ) ≤ 4*(radius:ℝ) := by
    change (q:ℝ)-X≤_ at dist
    linarith only [dist,next,diameter]
  obtain ⟨x,pos,near⟩ := center_contains (Nat.odd_mul.mp odd).2 (Nat.cast_nonneg _) (down.trans lb) room
  have low : CoupledDivisorWindow.lower (p*q) ≤ q :=
    CoupledDivisorWindow.lower_le_factor (by rw [Nat.mul_comm] : p*q=q*p) (ord.trans cap).le
  refine ⟨x,pos,near,atWindow x q ?_ pos (by exact_mod_cast low) ?_⟩
  · exact_mod_cast (dvd_mul_left q p)
  · simpa only [radius,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using near

end PrimeFactors.SevenRowBoundaryWindow
