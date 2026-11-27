import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic

/-! A product-only necessary test for a totient ratio to be a convergent.
It applies regardless of the support of a power map. -/
namespace PrimeFactors.PowerRatioRemainder

/-- Every approximant is its integer part plus a nonnegative correction. -/
theorem above_floor (x : ℝ) (i : ℕ) : (⌊x⌋ : ℚ) ≤ x.convergent i := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
    rw [Real.convergent_succ]
    apply le_add_of_nonneg_right
    apply inv_nonneg.mpr
    apply le_trans _ (ih (Int.fract x)⁻¹)
    exact_mod_cast Int.floor_nonneg.mpr (inv_nonneg.mpr (Int.fract_nonneg x))

/-- For E/N between zero and one, the first positive convergent bounds
every convergent above, including the entire terminating rational tail. -/
theorem ceiling {E N : ℕ} (ep : 0<E) (en : E≤N) (i : ℕ) :
    ((E:ℝ)/N).convergent i ≤ ((N/E : ℕ):ℚ)⁻¹ := by
  have np : 0<N := ep.trans_le en
  have dp : 0<N/E := Nat.div_pos en ep
  have rn : 0<(N:ℝ) := by exact_mod_cast np
  have re : 0<(E:ℝ) := by exact_mod_cast ep
  by_cases same : E=N
  · subst E
    rw [div_self rn.ne',Nat.div_self np]
    simpa using (le_of_eq (Real.convergent_of_int (ξ := 1) i))
  have below : (E:ℝ)/N<1 := (div_lt_one rn).mpr (by exact_mod_cast lt_of_le_of_ne en same)
  have nonnegative : 0≤(E:ℝ)/N := (div_pos re rn).le
  have f : ⌊(E:ℝ)/N⌋=0 := Int.floor_eq_zero_iff.mpr ⟨nonnegative,below⟩
  have fract : Int.fract ((E:ℝ)/N)=(E:ℝ)/N := by simp [Int.fract,f]
  cases i with
  | zero => simp [f]
  | succ i =>
    rw [Real.convergent_succ,f,Int.cast_zero,zero_add,fract,inv_div]
    have lower : ((N/E:ℕ):ℤ) ≤ ⌊(N:ℝ)/E⌋ := by
      apply Int.le_floor.mpr
      apply (le_div_iff₀ re).mpr
      exact_mod_cast Nat.div_mul_le_self N E
    have bound : ((N/E:ℕ):ℚ) ≤ ((N:ℝ)/E).convergent i :=
      (by simpa only [Int.cast_natCast] using
        (Int.cast_le (R:=ℚ)).mpr lower : ((N/E:ℕ):ℚ) ≤ (⌊(N:ℝ)/E⌋:ℚ)).trans (above_floor _ i)
    have pos : 0<((N/E:ℕ):ℚ) := by exact_mod_cast dp
    exact (inv_le_inv₀ (pos.trans_le bound) pos).mpr bound

/-- Any positive recovered denominator F is at least the last multiple of E
below N. Its difference from N cannot exceed the public remainder. -/
theorem remainder {E N F : ℕ} (ep : 0<E) (en : E≤N) (fp : 0<F)
    (hit : ∃ i, (E:ℚ)/F=((E:ℝ)/N).convergent i) :
    E*(N/E)≤F ∧ N-F≤N%E := by
  obtain ⟨i,hi⟩ := hit
  have cap := ceiling ep en i
  rw [←hi, ←one_div] at cap
  have dp : 0<((N/E:ℕ):ℚ) := by exact_mod_cast Nat.div_pos en ep
  have cross := (div_le_div_iff₀ (by exact_mod_cast fp) dp).mp cap
  have bound : E*(N/E)≤F := by exact_mod_cast (by simpa using cross : (E:ℚ)*(N/E:ℕ)≤F)
  exact ⟨bound,by have := Nat.mod_add_div N E; omega⟩

/-- For N=pq the hidden sum is bounded by a residue computed from the product.
This gives a product-only test using one division and one integer square. -/
theorem factor_gate {E p q : ℕ} (hp : 1<p) (hq : 1<q) (ep : 0<E) (en : E≤p*q)
    (hit : ∃ i, (E:ℚ)/((p-1)*(q-1):ℕ)=((E:ℝ)/(p*q:ℕ)).convergent i) :
    p+q≤(p*q)%E+1 ∧ 4*(p*q)≤((p*q)%E+1)^2 := by
  have fp : 0<(p-1)*(q-1) := Nat.mul_pos (by omega) (by omega)
  have bound := (remainder ep en fp hit).2
  have equation : p*q-(p-1)*(q-1)=p+q-1 := by
    obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p≠0)
    obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q≠0)
    simp only [Nat.add_one_sub_one]
    have curve : (a+1)*(b+1)=a*b+(a+b+1) := by ring
    rw [curve]; omega
  rw [equation] at bound
  have sum : p+q≤(p*q)%E+1 := by omega
  refine ⟨sum, ?_⟩
  have ag : 4*(p*q)≤(p+q)^2 := by
    exact_mod_cast (show (4:ℤ)*(p*q)≤(p+q)^2 by nlinarith only [sq_nonneg ((p:ℤ)-q)])
  exact ag.trans (Nat.pow_le_pow_left sum 2)

/-- Throughout the 2048-bit product interval, a remainder below 2^1024
immediately rules out this entire exponent, even when E itself is enormous. -/
theorem full_size_excluded {E p q : ℕ} (hp : 1<p) (hq : 1<q)
    (ep : 0<E) (en : E≤p*q) (large : 2^2047≤p*q) (short : (p*q)%E<2^1024) :
    ¬ ∃ i, (E:ℚ)/((p-1)*(q-1):ℕ)=((E:ℝ)/(p*q:ℕ)).convergent i := by
  intro hit
  have necessary := (factor_gate hp hq ep en hit).2
  have small := Nat.pow_le_pow_left (Nat.succ_le_of_lt short) 2
  have lower := Nat.mul_le_mul_left 4 large
  exact (by decide +kernel : ¬ (4*2^2047:ℕ)≤(2^1024)^2) (lower.trans (necessary.trans small))

/-- An exponent at a quotient of N or its predecessor is too close to a
division endpoint. This excludes every divisor-index t, with no width assumption. -/
theorem quotient_band_excluded {E p q t s : ℕ} (hp : 1<p) (hq : 1<q)
    (ep : 0<E) (tp : 0<t) (split : p*q=t*E+s) (short : s≤t) :
    ¬ ∃ i, (E:ℚ)/((p-1)*(q-1):ℕ)=((E:ℝ)/(p*q:ℕ)).convergent i := by
  intro hit
  have te : t*E≤p*q := by omega
  have en : E≤p*q := (Nat.le_mul_of_pos_left E tp).trans te
  have need := (factor_gate hp hq ep en hit).2
  have reduced : (p*q)%E=s%E := by simp [split, Nat.add_mod]
  have rt : (p*q)%E≤t := reduced ▸ (Nat.mod_le s E).trans short
  have re := Nat.mod_lt (p*q) ep
  have bound := Nat.mul_le_mul (by omega : (p*q)%E+1≤2*t) (by omega : (p*q)%E+1≤E)
  have pos : 0<p*q := Nat.mul_pos (by omega) (by omega)
  nlinarith only [need, bound, te, pos]

/-- The complete public menu floor(N/t) and floor((N−1)/t) is excluded. -/
theorem quotient_excluded {p q t j : ℕ} (hp : 1<p) (hq : 1<q)
    (tp : 0<t) (offset : j≤1) (ep : 0<(p*q-j)/t) :
    ¬ ∃ i, (((p*q-j)/t:ℕ):ℚ)/((p-1)*(q-1):ℕ)=
      ((((p*q-j)/t:ℕ):ℝ)/(p*q:ℕ)).convergent i := by
  apply quotient_band_excluded (t:=t) (s:=(p*q-j)%t+j) hp hq ep tp
  · have := Nat.mod_add_div (p*q-j) t
    have : 0<p*q := Nat.mul_pos (by omega) (by omega)
    omega
  · have := Nat.mod_lt (p*q-j) tp
    omega

end PrimeFactors.PowerRatioRemainder
