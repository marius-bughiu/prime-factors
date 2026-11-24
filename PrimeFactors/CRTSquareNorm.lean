import PrimeFactors.FactorSum
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- A root modulo D² yields a quadratic giving the exact signed quotient for
every representative t=r+D²k. -/
theorem crtSquareNorm_polynomial {R : Type*} [CommRing R] {D r N c : R}
    (root : r^2-N=D^2*c) (k : R) :
    (r+D^2*k)^2-N = D^2*(D^2*k^2+2*r*k+c) := by
  calc
    _ = (r^2-N)+D^2*(D^2*k^2+2*r*k) := by ring
    _ = _ := by rw [root]; ring

/-- Modulo the input product an inverse of D normalizes the row to a square
with right-hand side Q. This also works over rings with zero divisors. -/
theorem crtSquareNorm_normalize {R : Type*} [CommRing R] {D e t Q : R}
    (row : t^2=D^2*Q) (inverse : D*e=1) : (t*e)^2=Q := by
  calc
    _ = t^2*e^2 := by ring
    _ = (D*e)^2*Q := by rw [row]; ring
    _ = Q := by rw [inverse]; simp

/-- An exact signed integer norm descends to the normalized congruence
in the actual residue ring modulo N. -/
theorem crtSquareNorm_mod {N : ℕ} {D t Q : ℤ}
    (row : t^2-(N:ℤ)=D^2*Q) (e : ZMod N) (inverse : (D:ZMod N)*e=1) :
    ((t:ZMod N)*e)^2=(Q:ZMod N) := by
  apply crtSquareNorm_normalize _ inverse
  have h := congrArg (fun z : ℤ => (z : ZMod N)) row
  simpa using h

/-- If x≤y are nonnegative and their squares lie between N-B and N+B,
the squared width times N is at most 2B². Only the outer two gates are needed. -/
theorem crtSquareNorm_width {x y N B : ℝ} (hx : 0 ≤ x) (order : x ≤ y)
    (lower : N ≤ x^2+B) (upper : y^2 ≤ N+B) : (y-x)^2*N ≤ 2*B^2 := by
  let w := y-x
  have hw : 0 ≤ w := sub_nonneg.mpr order
  have hwx : 0 ≤ w*x := mul_nonneg hw hx
  have gap : w^2+2*(w*x) ≤ 2*B := by dsimp [w]; nlinarith
  have hxw : w*x ≤ B := by nlinarith [sq_nonneg w]
  have hB : 0 ≤ B := hwx.trans hxw
  change w^2*N ≤ 2*B^2
  nlinarith [mul_le_mul_of_nonneg_left lower (sq_nonneg w),
    mul_le_mul_of_nonneg_right gap hB, mul_le_mul_of_nonneg_right hxw hwx]

/-- When 2Y²<N, two natural representatives in the same residue class mod A
cannot both give signed square errors bounded by AY. -/
theorem crtSquareNorm_unique {x y A Y N : ℕ} (positive : 0 < A) (small : 2*Y^2<N)
    (order : x ≤ y) (residue : x ≡ y [MOD A])
    (lower : N ≤ x^2+A*Y) (upper : y^2 ≤ N+A*Y) : x=y := by
  by_contra different
  have gap : (A : ℝ) ≤ (y:ℝ)-x := by
    have h := residue.add_le_of_lt (lt_of_le_of_ne order different)
    have cast : (x:ℝ)+A ≤ y := by exact_mod_cast h
    linarith
  have wide := crtSquareNorm_width (x := (x:ℝ)) (y := (y:ℝ)) (N := (N:ℝ))
    (B := (A:ℝ)*Y) (Nat.cast_nonneg _) (by exact_mod_cast order)
    (by exact_mod_cast lower) (by exact_mod_cast upper)
  have g2 := sq_le_sq' (by linarith [Nat.cast_nonneg (α := ℝ) A] : -(y-x:ℝ) ≤ A) gap
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have strict : (2:ℝ)*(Y:ℝ)^2<N := by exact_mod_cast small
  have hA : (0:ℝ)<(A:ℝ) := by exact_mod_cast positive
  nlinarith [mul_le_mul_of_nonneg_right g2 hN,
    mul_lt_mul_of_pos_left strict (sq_pos_of_pos hA)]

/-- Over an increasing list of left sums spanning at most one period, the
rank of a fixed threshold decreases by at most one right list in total. -/
theorem crtSquareNorm_scan_budget (rank : ℤ → ℤ) (increasing : Monotone rank)
    {A R : ℤ} (period : ∀ x, rank (x+A) = rank x + R)
    {first last : ℤ} (ordered : first ≤ last) (span : last ≤ first+A) (target : ℤ) :
    rank (target-last) ≤ rank (target-first) ∧
      rank (target-first) - rank (target-last) ≤ R := by
  refine ⟨increasing (by omega), ?_⟩
  have enough : target-first ≤ target-last+A := by omega
  have reach := increasing enough
  rw [period] at reach
  omega

/-- When consecutive representatives straddle the square root, the smaller
of their two square errors is the minimum over the entire residue class. -/
theorem crtSquareNorm_bracket {r A x N : ℕ} (residue : r ≡ x [MOD A])
    (left : r^2 ≤ N) (right : N ≤ (r+A)^2) :
    min (N-r^2) ((r+A)^2-N) ≤ Nat.dist (x^2) N := by
  by_cases hx : x ≤ r
  · have h := Nat.pow_le_pow_left hx 2
    rw [Nat.dist_eq_sub_of_le (h.trans left)]
    exact (min_le_left _ _).trans (Nat.sub_le_sub_left h N)
  · have h := Nat.pow_le_pow_left (residue.add_le_of_lt (by omega)) 2
    rw [Nat.dist_eq_sub_of_le_right (right.trans h)]
    exact (min_le_right _ _).trans (Nat.sub_le_sub_right h N)

/-- If the least nonnegative representative is already above the square root,
the first term of the progression minimizes the square error. -/
theorem crtSquareNorm_first {r A x N : ℕ} (residue : x%A=r)
    (above : N ≤ r^2) : r^2-N ≤ Nat.dist (x^2) N := by
  have first : r ≤ x := residue ▸ Nat.mod_le x A
  have h := Nat.pow_le_pow_left first 2
  rw [Nat.dist_eq_sub_of_le_right (above.trans h)]
  exact Nat.sub_le_sub_right h N

/-- A single positive square norm can expose only the Fermat midpoint and
the exact half-gap of the two unknown primes. The test on t-Ds excludes 1·N. -/
theorem crtSquareNorm_square_components {p q D t s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ordered : p ≤ q)
    (row : t^2=p*q+(D*s)^2) (proper : 1<t-D*s) :
    t=(p+q)/2 ∧ D*s=(q-p)/2 := by
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le (show D*s ≤ t by omega)
  have product : u*(u+2*(D*s))=p*q := by
    rw [hu] at row
    nlinarith only [row]
  obtain ⟨h₁, h₂⟩ := ordered_semiprime_pair_unique hp hq ordered
    (show u ≤ u+2*(D*s) by omega) (show 1<u by omega) product
  omega

/-- A positive square with quotient at most Y exists and splits the two
primes precisely when D divides their half-gap and that quotient fits Y. -/
theorem crtSquareNorm_bounded_square_iff {p q D Y : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ordered : p < q) (op : Odd p) (oq : Odd q)
    (pos : 0 < D) :
    (∃ t s : ℕ, 0<s ∧ s^2 ≤ Y ∧ t^2=p*q+(D*s)^2 ∧ 1<t-D*s) ↔
      D ∣ (q-p)/2 ∧ (((q-p)/2)/D)^2 ≤ Y := by
  constructor
  · rintro ⟨t,s,_,budget,row,proper⟩
    have h := (crtSquareNorm_square_components hp hq ordered.le row proper).2.symm
    exact ⟨⟨s,h⟩, by rwa [h, Nat.mul_div_cancel_left _ pos]⟩
  · rintro ⟨⟨s,hs⟩,budget⟩
    rw [hs, Nat.mul_div_cancel_left _ pos] at budget
    obtain ⟨a,ha⟩ := op
    obtain ⟨b,hb⟩ := oq
    have qeq : q=p+2*(D*s) := by omega
    have ds : 0<D*s := by omega
    have hspos : 0<s := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at ds
    refine ⟨p+D*s,s,hspos,budget,?_,by simpa using hp.one_lt⟩
    rw [qeq]
    ring

/-- The direct square criterion without a size cutoff. -/
theorem crtSquareNorm_square_iff {p q D : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ordered : p < q) (op : Odd p) (oq : Odd q)
    (pos : 0 < D) :
    (∃ t s : ℕ, 0<s ∧ t^2=p*q+(D*s)^2 ∧ 1<t-D*s) ↔ D ∣ (q-p)/2 := by
  constructor
  · rintro ⟨t,s,_,row,proper⟩
    exact ⟨s,(crtSquareNorm_square_components hp hq ordered.le row proper).2.symm⟩
  · intro h
    obtain ⟨t,s,hs,_,row,proper⟩ :=
      (crtSquareNorm_bounded_square_iff hp hq ordered op oq pos).mpr ⟨h,le_rfl⟩
    exact ⟨t,s,hs,row,proper⟩

/-- A bounded trial-division sieve for the finite CRT population constants.
Every composite below 41² has a proper factor below 41. -/
def crtOddPrimeTrial (n : ℕ) : Bool :=
  decide (2 < n) && (List.range 41).all (fun d => decide (d < 2 ∨ n ≤ d ∨ n % d ≠ 0))

theorem crtOddPrimes_trial (limit : ℕ) (bound : limit ≤ 41^2) :
    (List.range limit).filter (fun p => decide (p.Prime ∧ 2 < p)) =
      (List.range limit).filter crtOddPrimeTrial := by
  apply List.filter_congr
  intro n hn
  apply Bool.eq_iff_iff.mpr
  simp only [crtOddPrimeTrial, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨prime, odd⟩
    refine ⟨odd, fun d _ => ?_⟩
    by_contra! h
    obtain h1 | h2 := (Nat.dvd_prime prime).mp (Nat.dvd_of_mod_eq_zero h.2.2)
    all_goals omega
  · rintro ⟨odd, trial⟩
    refine ⟨?_, odd⟩
    by_contra composite
    have small := Nat.minFac_sq_le_self (n := n) (by omega) composite
    have top := List.mem_range.mp hn
    have cut : n.minFac < 41 := by
      by_contra! large
      have comp := Nat.pow_le_pow_left large 2
      omega
    have tested := trial _ cut
    have := (Nat.minFac_prime (by omega : n ≠ 1)).two_le
    have := (Nat.not_prime_iff_minFac_lt (by omega : 2 ≤ n)).mp composite
    have := Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd n)
    omega

/-- Coefficients through degree 32 of the product of (p+z), for the subset
bound. The coefficient of z^32 divided by the primorial equals Σ 1/D. -/
private def crtSquareGap_coefficients (primes : List ℕ) : List ℕ :=
  primes.foldl (fun c p => List.zipWith (fun x y => p*x+y) c (0::c))
    (1 :: List.replicate 32 0)

/-- For each unfinished degree record the number of unit classes that have
skipped every nonsplit prime and matched p at each selected prime. The last
counter records all classes that already matched 32 selected primes. -/
private def crtSquareGap_selection (primes : List ℕ) : List ℕ × ℕ :=
  primes.foldl (fun (c, done) p =>
    (List.zipWith (fun x y => ((p-1)/2)*x+y) c (0::c),
     (p-1)*done+c[31]!)) (1 :: List.replicate 31 0, 0)

/-- Cleared-denominator bounds for the three elementary counts. In order,
the exponents cover any 32-prime subset, the first 32 split primes stopping
by 739, and the same first-split rule with no stopping-prime cutoff. -/
theorem crtSquareGap_population_constants :
    let primes := (List.range 740).filter (fun p => decide (p.Prime ∧ 2<p))
    let M := primes.prod
    let X := 2^1023
    let c := (crtSquareGap_coefficients primes)[32]!
    let selected := crtSquareGap_selection primes
    let K := Nat.choose primes.length 32
    let num := 1511*710*10000
    let den := 1000*22^2
    primes.length=130 ∧
      2^112*num*(X*c+2*M*K) < 2*M*X*den ∧
      2^147*num*(X+M)*selected.2 < M*X*den ∧
      2^113*num*(X+M)*(selected.2+selected.1.sum) < M*X*den := by
  rw [crtOddPrimes_trial 740 (by decide)]
  dsimp only
  have size : ((List.range 740).filter crtOddPrimeTrial).length = 130 := by
    set_option maxRecDepth 65536 in decide +kernel
  rw [size, Nat.choose_eq_factorial_div_factorial (by decide : 32 ≤ 130)]
  set_option maxRecDepth 65536 in
  set_option maxHeartbeats 2000000 in
  decide +kernel

end PrimeFactors
