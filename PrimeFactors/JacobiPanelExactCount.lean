import PrimeFactors.JacobiPeriodPanel
import PrimeFactors.JointPeriod
import Mathlib.Combinatorics.Enumerative.InclusionExclusion

/-! Exact size of the set of ordered unit pairs that simultaneously test all
multipliers of the public power probe correctly. -/
namespace PrimeFactors.JacobiPanelExactCount

open Finset JacobiPeriodCount JacobiPeriodPanel

private noncomputable def both (N t : ℕ) [NeZero N] : Finset ((ZMod N)ˣ × (ZMod N)ˣ) :=
  let U := univ.filter fun x : (ZMod N)ˣ => x^((N-1)*t)=1
  U ×ˢ U

private theorem mem_both {N : ℕ} [NeZero N] (z : (ZMod N)ˣ × (ZMod N)ˣ) (t : ℕ) :
    z ∈ both N t ↔ Passes z (N-1) t := by simp [both,Passes]

private theorem exchange {R m d : ℕ} (md : m ∣ R) (dd : d ∣ R) :
    m ∣ R/d ↔ d ∣ R/m := by
  rw [Nat.dvd_div_iff_mul_dvd dd,Nat.dvd_div_iff_mul_dvd md,mul_comm]

/-- Intersecting the critical tests removes the product of their distinct primes. -/
private theorem intersection {p q : ℕ} [NeZero (p*q)] (pp : p.Prime) (qp : q.Prime)
    (ne : p≠q) (S : Finset ℕ) (sub : S ⊆ (residualProduct p q).primeFactors) :
    let R := residualProduct p q
    S.inf (fun l => both (p*q) (R/l)) = both (p*q) (R/(∏ l ∈ S, l)) := by
  classical
  let R := residualProduct p q
  let d := ∏ l ∈ S, l
  have dd : d ∣ R := (prod_dvd_prod_of_subset S R.primeFactors id sub).trans (Nat.prod_primeFactors_dvd R)
  ext z
  let N := p*q
  let m := (orderOf (z.1^(N-1))).lcm (orderOf (z.2^(N-1)))
  have test (t : ℕ) : z ∈ both N t ↔ m ∣ t := by
    rw [mem_both]
    simp only [Passes,m,Nat.lcm_dvd_iff,orderOf_dvd_iff_pow_eq_one,←pow_mul]
  have md : m ∣ R := (test R).mp ((mem_both z R).mpr ⟨full_pass pp qp ne _,full_pass pp qp ne _⟩)
  change z ∈ S.inf (fun l => both N (R/l)) ↔ z ∈ both N (R/d)
  rw [mem_inf,test,exchange md dd]
  constructor
  · intro all
    apply prod_primes_dvd
    · exact fun l hl => (Nat.prime_of_mem_primeFactors (sub hl)).prime
    · intro l hl
      exact (exchange md (Nat.dvd_of_mem_primeFactors (sub hl))).mp ((test _).mp (all l hl))
  · intro hit l hl
    apply (test _).mpr
    apply (exchange md (Nat.dvd_of_mem_primeFactors (sub hl))).mpr
    exact (dvd_prod_of_mem id hl).trans hit

private theorem intersection_count {p q : ℕ} [NeZero (p*q)] (pp : p.Prime) (qp : q.Prime)
    (ne : p≠q) (S : Finset ℕ) (sub : S ⊆ (residualProduct p q).primeFactors) :
    let R := residualProduct p q
    ((S.inf (fun l => both (p*q) (R/l))).card : ℚ) =
      ((p*q).totient : ℚ)^2 * ∏ l ∈ S, 1/(l:ℚ)^2 := by
  classical
  let R := residualProduct p q
  let d := ∏ l ∈ S, l
  have dd : d ∣ R := (prod_dvd_prod_of_subset S R.primeFactors id sub).trans (Nat.prod_primeFactors_dvd R)
  have pg := Nat.sub_pos_of_lt pp.one_lt
  have qg := Nat.sub_pos_of_lt qp.one_lt
  have gp := Nat.gcd_pos_of_pos_left (q-1) pg
  have rp : 0 < R := Nat.mul_pos (Nat.div_pos (Nat.gcd_le_left _ pg) gp)
    (Nat.div_pos (Nat.gcd_le_right _ qg) gp)
  have dp := Nat.pos_of_dvd_of_pos dd rp
  have ep := Nat.div_pos (Nat.le_of_dvd rp dd) dp
  have frac := exact_fraction pp qp ne (R/d)
  change passing (p*q) (R/d)*R=(p*q).totient * R.gcd (R/d) at frac
  rw [Nat.gcd_eq_right (Nat.div_dvd_of_dvd dd)] at frac
  have h : passing (p*q) (R/d)*d=(p*q).totient := by
    apply Nat.eq_of_mul_eq_mul_right ep
    rw [mul_assoc,Nat.mul_div_cancel' dd,frac]
  have eqQ : (passing (p*q) (R/d):ℚ)*d=(p*q).totient := by exact_mod_cast h
  have nz : (d:ℚ)≠0 := by exact_mod_cast dp.ne'
  dsimp only
  rw [intersection pp qp ne S sub]
  have pc : (both (p*q) (R/d)).card = passing (p*q) (R/d)^2 := by
    rw [both,card_product,pow_two]; rfl
  change ((both (p*q) (R/d)).card : ℚ) = _
  rw [pc,Nat.cast_pow,prod_div_distrib,prod_const_one,prod_pow]
  have dc : (∏ l ∈ S, (l:ℚ)) = (d:ℚ) := by simp [d]
  rw [dc,←eqQ]
  field_simp
  ring

/-- The exact fraction of independent ordered pairs that correctly answer every
guess equals the generating-pair Euler product at R. -/
theorem faithful_count {p q : ℕ} [NeZero (p*q)] (pp : p.Prime) (qp : q.Prime) (ne : p≠q) :
    let R := residualProduct p q
    (((badPanels (p*q) R)ᶜ.card : ℕ) : ℚ) =
      ((p*q).totient : ℚ)^2 * ∏ l ∈ R.primeFactors, (1-1/(l:ℚ)^2) := by
  classical
  let R := residualProduct p q
  let P := R.primeFactors
  let E := fun l => both (p*q) (R/l)
  have complement : (badPanels (p*q) R)ᶜ = P.inf (fun l => (E l)ᶜ) := by
    rw [← Finset.compl_sup,Finset.sup_eq_biUnion]
    rfl
  have inc := congrArg (fun z : ℤ => (z:ℚ)) (inclusion_exclusion_card_inf_compl P E)
  push_cast at inc
  change (((badPanels (p*q) R)ᶜ.card : ℕ) : ℚ) = _
  rw [complement,inc,prod_sub (fun _ : ℕ => (1:ℚ)) (fun l : ℕ => 1/(l:ℚ)^2) P,mul_sum]
  apply sum_congr rfl
  intro S hS
  have cnt := intersection_count pp qp ne S (mem_powerset.mp hS)
  change ((S.inf E).card : ℚ) = _ at cnt
  rw [cnt,prod_const_one]
  ring

/-- Probability version for two independent uniformly chosen unit bases. -/
theorem faithful_fraction {p q : ℕ} [NeZero (p*q)] (pp : p.Prime) (qp : q.Prime) (ne : p≠q) :
    let R := residualProduct p q
    (((badPanels (p*q) R)ᶜ.card : ℕ) : ℚ) / ((p*q).totient : ℚ)^2 =
      ∏ l ∈ R.primeFactors, (1-1/(l:ℚ)^2) := by
  dsimp only
  have positive : 0 < ((p*q).totient : ℚ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos (p*q))
  apply (div_eq_iff (pow_ne_zero 2 positive.ne')).mpr
  exact (faithful_count pp qp ne).trans (mul_comm ..)

/-- The product lower bound applies to the actual fraction, for every R. -/
theorem faithful_lower {p q : ℕ} [NeZero (p*q)] (pp : p.Prime) (qp : q.Prime) (ne : p≠q) :
    let R := residualProduct p q
    ((R:ℚ)+2)/(2*(R+1)) ≤ (((badPanels (p*q) R)ᶜ.card : ℕ) : ℚ) / ((p*q).totient : ℚ)^2 := by
  dsimp only
  rw [faithful_fraction pp qp ne]
  apply jointPeriod_eulerProduct_bound
  intro l hl
  obtain ⟨pr,ld,nz⟩ := Nat.mem_primeFactors.mp hl
  exact ⟨pr.two_le,(Nat.le_of_dvd (Nat.pos_of_ne_zero nz) ld).trans (Nat.le_succ _)⟩

/-- At 221 exactly two thirds of ordered pairs are faithful. -/
theorem control_221 : (((badPanels 221 12)ᶜ.card : ℕ) : ℚ)/192^2=2/3 := by
  have h := faithful_fraction (p:=13) (q:=17) (by decide) (by decide) (by decide)
  change (((badPanels 221 12)ᶜ.card : ℕ) : ℚ)/((221:ℕ).totient:ℚ)^2=
    ∏ l ∈ (12:ℕ).primeFactors, (1-1/(l:ℚ)^2) at h
  have factors : (12:ℕ).primeFactors = {2,3} := by
    ext l
    rw [Nat.mem_primeFactors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨pr,div,_⟩
      have bound := Nat.le_of_dvd (by decide : 0 < 12) div
      interval_cases l <;> norm_num at pr div ⊢
    · rintro (rfl|rfl) <;> norm_num
  rw [show (221:ℕ).totient=192 by decide +kernel,
    show (∏ l ∈ (12:ℕ).primeFactors, (1-1/(l:ℚ)^2))=2/3 by norm_num [factors]] at h
  exact h

end PrimeFactors.JacobiPanelExactCount
