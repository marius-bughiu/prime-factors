import PrimeFactors.FractionalNonunitPrefix
import PrimeFactors.Fermat
import PrimeFactors.Isolation

/-! Prefix nonunit counts at and above the ceiling square root. For balanced
prime factors these counts are zero or one. Their transition locates the
larger prime, and balance supplies a public upper endpoint for testing it. -/
namespace PrimeFactors.FractionalFreeReadings

open Finset FractionalNonunitPrefix

/-- The ceiling square root separates the two factors. Balance also puts
the larger prime below twice this public denominator. -/
theorem root_bounds {p q : ℕ} (pos : 0<p) (order : p<q) (balance : q<2*p) :
    p<ceilSqrt (p*q) ∧ ceilSqrt (p*q)≤q ∧ q<2*ceilSqrt (p*q) := by
  have small : p<ceilSqrt (p*q) := by
    apply lt_of_not_ge
    intro h
    have prod := ceilSqrt_le_iff.mp h
    have gap := Nat.mul_lt_mul_of_pos_left order pos
    nlinarith only [prod,gap]
  have large : ceilSqrt (p*q)≤q := ceilSqrt_le_iff.mpr
    (by simpa only [pow_two] using Nat.mul_le_mul_right q order.le)
  exact ⟨small,large,by omega⟩

/-- A denominator above the larger prime is precisely a zero reading. -/
theorem zero_iff {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (order : p<q) (hm : 2≤m) :
    prefixCount (p*q) m=0 ↔ q<m := by
  rw [quotient_sum hp hq order.ne hm, Nat.add_eq_zero_iff, Nat.div_eq_zero_iff,
    Nat.div_eq_zero_iff]
  omega

/-- From the public root onward, the count is a comparison with the larger prime. -/
theorem above_root {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (order : p<q)
    (balance : q<2*p) (above : ceilSqrt (p*q)≤m) :
    prefixCount (p*q) m = if m≤q then 1 else 0 := by
  obtain ⟨left,_,right⟩ := root_bounds hp.pos order balance
  have pl : p<m := by omega
  have proper : 1<m := hp.one_lt.trans pl
  rw [quotient_sum hp hq order.ne proper, Nat.div_eq_of_lt pl, zero_add]
  split_ifs with cover
  · exact Nat.div_eq_of_lt_le (by simpa using cover) (by omega)
  · exact Nat.div_eq_of_lt (by omega)

/-- This count is available from the product and the balance assumption alone. -/
theorem root_reading {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (order : p<q)
    (balance : q<2*p) : prefixCount (p*q) (ceilSqrt (p*q))=1 := by
  rw [above_root hp hq order balance le_rfl, if_pos (root_bounds hp.pos order balance).2.1]

private theorem upper {p q : ℕ} (order : p<q) (balance : q<2*p) :
    q<ceilSqrt (2*(p*q)) := by
  apply lt_of_not_ge
  intro h
  have b := ceilSqrt_le_iff.mp h
  have gap := Nat.mul_lt_mul_of_pos_right balance (by omega : 0<q)
  nlinarith only [b,gap]

/-- The squared public cutoff 2N ≤ m² guarantees the zero branch. -/
theorem public_zero {p q m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (order : p<q) (balance : q<2*p) (cut : 2*(p*q)≤m^2) : prefixCount (p*q) m=0 := by
  have bound := (upper order balance).trans_le (ceilSqrt_le_iff.mpr cut)
  exact (zero_iff hp hq order (by have := hq.two_le; omega)).mpr bound

/-- Candidate divisors from the public root up to the earlier of the proposed
denominator and the public upper endpoint for the larger prime. -/
noncomputable def candidates (n m : ℕ) := Ico (ceilSqrt n) (min m (ceilSqrt (2*n)))

theorem test_count (n m : ℕ) :
    (candidates n m).card = min m (ceilSqrt (2*n))-ceilSqrt n := Nat.card_Ico ..

/-- Testing divisibility on this interval exactly decides between the two
possible readings for a denominator at or above the public root. -/
theorem scan_iff {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (order : p<q)
    (balance : q<2*p) (above : ceilSqrt (p*q)≤m) :
    prefixCount (p*q) m=1 ↔ ∀ x∈candidates (p*q) m, ¬x∣p*q := by
  have bounds := root_bounds hp.pos order balance
  have qmax := upper order balance
  rw [above_root hp hq order balance above]
  constructor
  · intro h x hx dv
    have mq : m≤q := by simpa using h
    obtain ⟨bottom,top⟩ := mem_Ico.mp hx
    have px := bounds.1.trans_le bottom
    have xq := (top.trans_le (min_le_left ..)).trans_le mq
    have prod : q≤p*q := Nat.le_mul_of_pos_left _ hp.pos
    have pp := hp.one_lt
    obtain ⟨a,b,ap,bq,ab⟩ := Nat.dvd_mul.mp dv
    rcases (Nat.dvd_prime hp).mp ap with rfl|rfl <;>
      rcases (Nat.dvd_prime hq).mp bq with rfl|rfl <;>
        (try simp only [one_mul,mul_one] at ab) <;> omega
  · intro clean
    exact if_pos (le_of_not_gt fun mq =>
      clean q (mem_Ico.mpr ⟨bounds.2.1,lt_min mq qmax⟩) (dvd_mul_left q p))

private theorem root_2183 : ceilSqrt 2183=47 := by
  apply le_antisymm (ceilSqrt_le_iff.mpr (by decide))
  by_contra! h
  have small := ceilSqrt_le_iff.mp (show ceilSqrt 2183≤46 by omega)
  omega

private theorem interval_2183 : candidates 2183 48={47} := by
  change Ico (ceilSqrt 2183) (min 48 (ceilSqrt 4366))={47}
  have reach : 48≤ceilSqrt 4366 := by
    by_contra! h
    have small := ceilSqrt_le_iff.mp (show ceilSqrt 4366≤47 by omega)
    omega
  rw [root_2183,min_eq_left reach]
  exact Nat.Ico_succ_singleton ..

private theorem miss_2183 : ¬(47:ℕ)∣2183 := by
  rw [Nat.dvd_iff_mod_eq_zero]
  decide

private theorem scan_2183 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (order : p<q)
    (balance : q<2*p) (prod : p*q=2183) : prefixCount (p*q) 48=1 := by
  apply (scan_iff hp hq order balance (m:=48) (by rw [prod,root_2183]; decide)).mpr
  rw [prod,interval_2183]
  simpa only [mem_singleton,forall_eq] using miss_2183

/-- The count at 47 uses only the root. Extending to 48 adds the single
test at 47. The count at 120 follows from the squared public cutoff. -/
theorem example_2183 :
    ceilSqrt 2183=47 ∧ prefixCount 2183 47=1 ∧ candidates 2183 48={47} ∧
    (¬(47:ℕ)∣2183) ∧ prefixCount 2183 48=1 ∧ prefixCount 2183 120=0 := by
  have hp : Nat.Prime 37 := by decide
  have hq : Nat.Prime 59 := by decide
  have ord : 37<59 := by decide
  have bal : 59<2*37 := by decide
  have prod : 37*59=2183 := by decide
  have one := root_reading hp hq ord bal
  have at48 := scan_2183 hp hq ord bal prod
  have zero := public_zero hp hq ord bal (m:=120) (by decide)
  rw [prod,root_2183] at one
  rw [prod] at at48 zero
  exact ⟨root_2183,one,interval_2183,miss_2183,at48,zero⟩

/-- The first count and all residue pairs with the observed product modulo
48 give three candidate sums. -/
theorem example_candidates (s : ℕ) :
    (∃ x y : Fin 48, (x.val*y.val)%48=2183%48 ∧ s=48+(x.val+y.val)) ↔
    s=72 ∨ s=96 ∨ s=120 := by
  constructor
  · rintro ⟨x,y,prod,rfl⟩
    have complete : ∀ a b : Fin 48, (a.val*b.val)%48=2183%48 →
        48+(a.val+b.val)=72 ∨ 48+(a.val+b.val)=96 ∨ 48+(a.val+b.val)=120 := by decide +kernel
    exact complete x y prod
  · rintro (rfl | rfl | rfl)
    · exact ⟨1,23,by decide,by decide⟩
    · exact ⟨5,43,by decide,by decide⟩
    · exact ⟨25,47,by decide,by decide⟩

/-- On this bounded input the balance inequalities leave 96 as the only
candidate. The count uses divisibility by 47, without guessing a prime. -/
theorem example_balanced_sum {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (order : p<q)
    (balance : q<2*p) (prod : p*q=2183) : p+q=96 := by
  have count := scan_2183 hp hq order balance prod
  have residues := scaled hp hq order.ne (by decide : 1<48)
  rw [count,mul_one] at residues
  have possible : p+q=72 ∨ p+q=96 ∨ p+q=120 := by
    apply (example_candidates _).mp
    refine ⟨⟨p%48,Nat.mod_lt _ (by decide)⟩,⟨q%48,Nat.mod_lt _ (by decide)⟩,?_,residues.symm⟩
    change p%48*(q%48)%48=2183%48
    rw [←Nat.mul_mod,prod]
  have bounds := balanced_factorSum_bounds order.le balance.le
  rw [prod] at bounds
  rcases possible with a | a | a
  · rw [a] at bounds
    omega
  · exact a
  · rw [a] at bounds
    omega

/-- This toy product also determines the sum by a shorter route. Balance
puts it between 94 and 99, and the product modulo four makes it a
multiple of four. This control requires neither a prefix count nor a trial. -/
theorem example_sum_mod_four {p q : ℕ} (order : p≤q) (balance : q≤2*p)
    (prod : p*q=2183) : p+q=96 := by
  have bounds := balanced_factorSum_bounds order balance
  rw [prod] at bounds
  have low : 93<p+q := by
    by_contra! bad
    have sq := Nat.pow_le_pow_left bad 2
    omega
  have high : p+q<100 := by
    by_contra! bad
    have sq := Nat.pow_le_pow_left bad 2
    omega
  have table : ∀ x y : Fin 4, (x.val*y.val)%4=3 → (x.val+y.val)%4=0 := by decide +kernel
  have rem : (p+q)%4=0 := by
    rw [Nat.add_mod]
    apply table ⟨p%4,Nat.mod_lt _ (by decide)⟩ ⟨q%4,Nat.mod_lt _ (by decide)⟩
    change p%4*(q%4)%4=3
    rw [←Nat.mul_mod,prod]
  omega

end PrimeFactors.FractionalFreeReadings
