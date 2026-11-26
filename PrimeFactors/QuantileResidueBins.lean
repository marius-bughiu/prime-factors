import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Finite counting and error propagation for a predictor that sees a leading
and a trailing word of the product. The analytic prime-count discrepancy and
the two-dimensional continuous area estimates are hypotheses of the bridge. -/
namespace PrimeFactors.QuantileResidueBins
open Finset

/-- Each first unit residue determines exactly one second residue in a
specified unit product class. This applies to non-squarefree moduli. -/
theorem fiber_sum {G A : Type*} [Group G] [Fintype G] [DecidableEq G]
    [AddCommMonoid A] (r : G) (weight : G → G → A) :
    (∑ a : G, ∑ b : G, if a*b=r then weight a b else 0) =
      ∑ a : G, weight a (a⁻¹*r) := by
  apply sum_congr rfl
  intro a _
  rw [sum_eq_single (a⁻¹*r)]
  · simp
  · intro b _ ne
    rw [if_neg (fun e => ne (by rw [←e]; simp))]
  · simp

/-- The highest bit of a full-width product and the lowest bit of an odd
product are known. The exponent bins allow a zero length on either side. -/
theorem word_scale {head tail : ℕ} (budget : head+tail≤464) :
    (2:ℝ)^48*(2:ℝ)^(tail-1) ≤ (1/(2:ℝ)^(max 1 head))*(2:ℝ)^512 := by
  have exps : 48+(tail-1)+max 1 head≤512 := by omega
  rw [one_div_mul_eq_div,le_div_iff₀ (by positivity),←pow_add,←pow_add]
  exact pow_le_pow_right₀ (by norm_num) exps

/-- At scale B=r², let e be the prime count error on one slice and E the
resulting error on one region of a single prefix/suffix cell. D is the
smooth total mass of that cell after imposing both words. -/
theorem relative_error {r f δ d e E D : ℝ} (rp : 0<r) (fp : 0<f) (δp : 0<δ)
    (width : δ≤d) (menu : (2:ℝ)^48*f≤δ*r) (e0 : 0≤e) (cap : e≤2^15*r)
    (slices : E≤e*(2*d*r^2/709+f*e))
    (mass : r^4*δ*d≤4*710^2*f*D) : (2:ℝ)^20*E<D := by
  have dp : 0<d := δp.trans_le width
  have ferry : 2*709*f*e ≤ d*r^2 := calc
    2*709*f*e ≤ 2*709*f*(2^15*r) :=
      mul_le_mul_of_nonneg_left cap (by positivity)
    _ ≤ (2^48*f)*r := by nlinarith only [mul_pos fp rp]
    _ ≤ (δ*r)*r := mul_le_mul_of_nonneg_right menu rp.le
    _ ≤ d*r^2 := by rw [mul_assoc,←sq]; exact mul_le_mul_of_nonneg_right width (sq_nonneg _)
  have sliceBound : E ≤ (2^15*r)*(5*d*r^2/1418) := calc
    E ≤ e*(2*d*r^2/709+f*e) := slices
    _ ≤ e*(5*d*r^2/1418) := mul_le_mul_of_nonneg_left (by linarith only [ferry]) e0
    _ ≤ (2^15*r)*(5*d*r^2/1418) := mul_le_mul_of_nonneg_right cap (by positivity)
  apply (lt_of_mul_lt_mul_left (a:=4*710^2*f) ?_ (by positivity))
  calc 4*710^2*f*(2^20*E) ≤
      (4*710^2*2^20*2^15*5/1418)*(f*r^3*d) := by
        calc _ ≤ 4*710^2*f*(2^20*((2^15*r)*(5*d*r^2/1418))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left sliceBound (by positivity))
                (by positivity)
             _ = _ := by ring
    _ < 2^48*(f*r^3*d) := mul_lt_mul_of_pos_right (by norm_num) (by positivity)
    _ = (2^48*f)*(r^3*d) := by ring
    _ ≤ (δ*r)*(r^3*d) := mul_le_mul_of_nonneg_right menu (by positivity)
    _ = r^4*δ*d := by ring
    _ ≤ 4*710^2*f*D := mass

/-- Independent additive count errors on an event and its complement move
their normalized share by at most the error divided by the smooth total. -/
theorem count_share {g b : ℕ} {G B E s t : ℝ}
    (lower : 0≤s+t) (upper : s+t≤1)
    (good : (g:ℝ)≤G+E) (bad : B-E≤(b:ℝ))
    (smooth : G≤s*(G+B)) (err : E<t*(G+B)) :
    (g:ℝ)<(s+t)*(g+b) := by
  have h1 := mul_le_mul_of_nonneg_left good (sub_nonneg.mpr upper)
  have h2 := mul_le_mul_of_nonneg_left bad lower
  nlinarith only [h1,h2,smooth,err]

/-- Either choice in a cell is below the stated ceiling when the larger
smooth share has the fixed bias cap and both counts satisfy the slice bounds. -/
theorem accuracy {g b : ℕ} {G B E : ℝ}
    (good : |(g:ℝ)-G|≤E) (bad : |(b:ℝ)-B|≤E)
    (gfrac : G≤(1/2+(3:ℝ)/10^8)*(G+B))
    (bfrac : B≤(1/2+(3:ℝ)/10^8)*(G+B))
    (err : (2:ℝ)^20*E<G+B) (pick : Bool) :
    ((if pick then g else b : ℕ):ℝ)<(50000099:ℝ)/100000000*(g+b) := by
  have eps : E<(1/(2:ℝ)^20)*(G+B) := by linarith
  have h (n m : ℕ) (X Y : ℝ) (h0 : (n:ℝ)≤X+E) (h1 : Y-E≤(m:ℝ))
      (hs : X≤(1/2+(3:ℝ)/10^8)*(X+Y)) (he : E<(1/(2:ℝ)^20)*(X+Y)) :
      (n:ℝ)<(50000099:ℝ)/100000000*(n+m) := by
    apply lt_of_lt_of_le (count_share (s:=1/2+(3:ℝ)/10^8) (t:=1/(2:ℝ)^20)
      (by norm_num) (by norm_num) h0 h1 hs he)
    exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  cases pick
  · change (b:ℝ)<(50000099:ℝ)/100000000*(g+b)
    have e := h b g B G (by linarith [(abs_le.mp bad).2]) (by linarith [(abs_le.mp good).1])
      (by linarith only [bfrac]) (by linarith only [eps])
    simpa only [add_comm (g:ℝ) (b:ℝ)] using e
  · exact h g b G B (by linarith [(abs_le.mp good).2]) (by linarith [(abs_le.mp bad).1])
      gfrac eps

/-- A gap band and the whole cell can each be compared to their smooth
mass even when the complement of the band has disconnected slices. -/
theorem band_accuracy {hits total : ℕ} {D E : ℝ} (mass : 0<D)
    (band : (hits:ℝ)≤D/(256*(1-1/(2047:ℝ)^2))+E)
    (whole : D-E≤(total:ℝ)) (discrepancy : (2:ℝ)^20*E<D) :
    (hits:ℝ)<(3908:ℝ)/1000000*total := by
  have ceiling : 1/(256*(1-1/(2047:ℝ)^2))+1/(2:ℝ)^20 <
      (3908:ℝ)/1000000*(1-1/(2:ℝ)^20) := by norm_num
  have eps : E<(1/(2:ℝ)^20)*D := by linarith
  calc (hits:ℝ) ≤ D/(256*(1-1/(2047:ℝ)^2))+E := band
    _ < (1/(256*(1-1/(2047:ℝ)^2))+1/(2:ℝ)^20)*D := by
      rw [add_mul,one_div_mul_eq_div]; exact add_lt_add_left eps _
    _ < 3908/1000000*(1-1/(2:ℝ)^20)*D := mul_lt_mul_of_pos_right ceiling mass
    _ ≤ 3908/1000000*(total:ℝ) := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      linarith only [whole,eps]

/-- A finite partition allows a different prediction on each observed cell.
It suffices to bound the number of correct labels in every individual cell. -/
theorem combine {ι : Type*} (cells : Finset ι) (ne : cells.Nonempty)
    (wins total : ι → ℕ) {rate : ℝ}
    (bounds : ∀ i∈cells, (wins i:ℝ)<rate*(total i:ℝ)) :
    (∑ i∈cells, (wins i:ℝ))<rate*(∑ i∈cells, (total i:ℝ)) := by
  rw [Finset.mul_sum]
  exact Finset.sum_lt_sum_of_nonempty ne bounds

/-- The unit-class count for the repository's mod-4 and odd-prime menus. -/
theorem menu_totient (P : Finset ℕ) (primes : ∀ p ∈ P, p.Prime ∧ 2 < p) :
    Nat.totient (4 * ∏ p ∈ P, p) = 2 * ∏ p ∈ P, (p-1) := by
  induction P using Finset.induction_on with
  | empty => decide +kernel
  | @insert p P fresh ih =>
    have hp := primes p (Finset.mem_insert_self ..)
    have old (q : ℕ) (hq : q ∈ P) := primes q (Finset.mem_insert_of_mem hq)
    have c2 := (Nat.coprime_primes hp.1 Nat.prime_two).mpr hp.2.ne'
    have c4 : p.Coprime 4 := c2.pow_right 2
    have cs : p.Coprime (∏ q ∈ P, q) := Nat.coprime_prod_right_iff.mpr
      (fun q hq => (Nat.coprime_primes hp.1 (old q hq).1).mpr (fun eq => fresh (eq ▸ hq)))
    rw [Finset.prod_insert fresh, Finset.prod_insert fresh,
        mul_left_comm 4 p, Nat.totient_mul (c4.mul_right cs), Nat.totient_prime hp.1, ih old]
    ring

/-- Number of possible unit residues modulo 4 and all odd primes through the cutoff. -/
noncomputable def sieveUnitCount (cutoff : ℕ) : ℕ :=
  2 * ∏ p ∈ (Finset.range (cutoff+1)).filter (fun p => p.Prime ∧ 2 < p), (p-1)

theorem sieve_observation_budgets :
    2^128 * sieveUnitCount 251 ≤ 2^464 ∧
    2 * sieveUnitCount 347 ≤ 2^464 ∧
    2^464 < 2^128 * sieveUnitCount 257 ∧ 2^464 < 2 * sieveUnitCount 349 := by
  decide +kernel

/-- Jacobi observations on any product of the covered generators factor through
one residue of the odd denominator. The list may repeat generators arbitrarily. -/
theorem jacobi_product_observation {n n' Q : ℕ} (odd : Odd n) (odd' : Odd n')
    (same : n ≡ n' [MOD Q]) (generators : List ℤ)
    (covered : ∀ z ∈ generators, 4*z.natAbs ∣ Q) :
    jacobiSym generators.prod n = jacobiSym generators.prod n' := by
  induction generators with
  | nil => simp [jacobiSym.one_left]
  | cons z rest ih =>
    have eq := Nat.ModEq.of_dvd (covered z (List.mem_cons_self ..)) same
    have char : jacobiSym z n = jacobiSym z n' := calc
      jacobiSym z n = jacobiSym z (n % (4*z.natAbs)) := jacobiSym.mod_right z odd
      _ = jacobiSym z (n' % (4*z.natAbs)) := congrArg (jacobiSym z) eq
      _ = jacobiSym z n' := (jacobiSym.mod_right z odd').symm
    simp only [List.prod_cons, jacobiSym.mul_left, char,
      ih (fun w hw => covered w (List.mem_cons_of_mem _ hw))]

/-- A modulus for the sign, the factor 2 and all odd primes in a menu. -/
theorem jacobi_generators {P : Finset ℕ} {z : ℤ}
    (known : z = -1 ∨ z = 2 ∨ ∃ p ∈ P, z = (p : ℤ)) :
    4*z.natAbs ∣ 8 * ∏ p ∈ P, p := by
  rcases known with rfl | rfl | ⟨p,hp,rfl⟩
  · exact dvd_mul_of_dvd_left (by decide) _
  · exact dvd_mul_of_dvd_left (by decide) _
  · exact Nat.mul_dvd_mul (by decide : 4 ∣ 8) (Finset.dvd_prod_of_mem _ hp)

theorem jacobi_menu_count (P : Finset ℕ) (primes : ∀ p ∈ P, p.Prime ∧ 2 < p) :
    Nat.totient (8 * ∏ p ∈ P, p) = 4 * ∏ p ∈ P, (p-1) := by
  have cop : Nat.Coprime 2 (∏ p ∈ P, p) := Nat.coprime_prod_right_iff.mpr
    (fun p hp => (Nat.coprime_primes Nat.prime_two (primes p hp).1).mpr (primes p hp).2.ne)
  have base := menu_totient P primes
  rw [Nat.totient_mul (cop.pow_left 2), show Nat.totient 4 = 2 by decide] at base
  rw [Nat.totient_mul (cop.pow_left 3), show Nat.totient 8 = 4 by decide]
  omega

theorem jacobi_observation_budgets :
    2^129 * sieveUnitCount 251 ≤ 2^464 ∧ 4 * sieveUnitCount 347 ≤ 2^464 := by
  decide +kernel

end PrimeFactors.QuantileResidueBins
