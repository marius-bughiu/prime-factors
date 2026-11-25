import Mathlib.Data.Nat.ModEq
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

namespace PrimeFactors.FactorLaneAdvice
open Finset

/-- At fixed first factor, distinct odd partners have products at least one high-word
bin apart when the bin width is at most twice the first factor. -/
theorem high_injective {M p q r : ℕ} (pos : 0 < M) (wide : M ≤ 2*p)
    (hq : Odd q) (hr : Odd r) (eq : p*q/M = p*r/M) : q = r := by
  have forward {a b : ℕ} (ha : Odd a) (hb : Odd b) (lt : a < b)
      (same : p*a/M=p*b/M) : False := by
    obtain ⟨i,hi⟩ := ha
    obtain ⟨j,hj⟩ := hb
    have gap : a+2 ≤ b := by omega
    have jump := Nat.mul_le_mul_left p gap
    rw [Nat.mul_add] at jump
    have upper := Nat.lt_div_mul_add (a := p*b) pos
    rw [← same] at upper
    have lower := Nat.div_mul_le_self (p*a) M
    omega
  exact le_antisymm (le_of_not_gt fun h => forward hr hq h eq.symm)
    (le_of_not_gt fun h => forward hq hr h eq)

/-- The low word is injective because multiplication by the fixed factor is a unit. -/
theorem low_injective {M p q r : ℕ} (unit : M.Coprime p) (hq : q < M) (hr : r < M)
    (eq : p*q%M=p*r%M) : q=r := by
  have h := Nat.ModEq.cancel_left_of_coprime unit eq
  simpa [Nat.ModEq, Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hr] using h

/-- Count successful oriented pairs in one transcript using either product word.
The first factor lies in exactly B complete blocks of R residues. -/
theorem one_word_bound {hits : Finset (ℕ × ℕ)} {A codes : Finset ℕ} {R B : ℕ}
    (pos : 0<R) (word : ℕ → ℕ)
    (inside : ∀ t ∈ hits, B*R ≤ t.1 ∧ t.1 < (2*B)*R ∧
      t.1%R ∈ A ∧ word (t.1*t.2) ∈ codes)
    (inj : ∀ p q r, (p,q) ∈ hits → (p,r) ∈ hits →
      word (p*q) = word (p*r) → q=r) :
    hits.card ≤ A.card * B * codes.card := by
  let bins := (A ×ˢ Ico B (2*B)) ×ˢ codes
  have count : bins.card=A.card*B*codes.card := by simp [bins, two_mul]
  rw [← count]
  apply card_le_card_of_injOn (fun t : ℕ × ℕ => ((t.1%R,t.1/R),word (t.1*t.2)))
  · intro t ht
    obtain ⟨lo,hi,ha,hc⟩ := inside t ht
    exact mem_product.mpr ⟨mem_product.mpr ⟨ha,mem_Ico.mpr
      ⟨(Nat.le_div_iff_mul_le pos).mpr lo,(Nat.div_lt_iff_lt_mul pos).mpr hi⟩⟩,hc⟩
  · rintro ⟨p,q⟩ hp ⟨s,r⟩ hs eq
    have rem := congrArg (fun z : (ℕ × ℕ) × ℕ => z.1.1) eq
    have quo := congrArg (fun z : (ℕ × ℕ) × ℕ => z.1.2) eq
    change p%R=s%R at rem
    change p/R=s/R at quo
    have same : p=s := by
      calc p = R*(p/R)+p%R := (Nat.div_add_mod p R).symm
           _ = s := by rw [rem,quo,Nat.div_add_mod]
    subst s
    exact Prod.ext rfl (inj p q r hp hs (congrArg Prod.snd eq))

/-- In a rectangle of high and low product words, either projection can be used.
Odd partners and the fixed prime factor make each map injective on a fiber. -/
theorem transcript_cell {hits : Finset (ℕ × ℕ)} {A high low : Finset ℕ} {R B M : ℕ}
    (pos : 0<R) (mp : 0<M)
    (domain : ∀ t ∈ hits, B*R ≤ t.1 ∧ t.1 < 2*B*R ∧ t.1%R ∈ A)
    (factors : ∀ t ∈ hits, M ≤ 2*t.1 ∧ Odd t.2 ∧ t.2 < M ∧ M.Coprime t.1)
    (words : ∀ t ∈ hits, t.1*t.2/M ∈ high ∧ t.1*t.2%M ∈ low) :
    hits.card ≤ A.card * B * min high.card low.card := by
  have bounds (t : ℕ × ℕ) (ht : t ∈ hits) := domain t ht
  have upper : hits.card ≤ A.card*B*high.card :=
    one_word_bound pos (fun n => n/M) (fun t ht => ⟨(bounds t ht).1,
      (bounds t ht).2.1,(bounds t ht).2.2,(words t ht).1⟩)
      (fun p q r hq hr eq => high_injective mp (factors (p,q) hq).1
        (factors (p,q) hq).2.1 (factors (p,r) hr).2.1 eq)
  have lower : hits.card ≤ A.card*B*low.card :=
    one_word_bound pos (fun n => n%M) (fun t ht => ⟨(bounds t ht).1,
      (bounds t ht).2.1,(bounds t ht).2.2,(words t ht).2⟩)
      (fun p q r hq hr eq => low_injective (factors (p,q) hq).2.2.2
        (factors (p,q) hq).2.2.1 (factors (p,r) hr).2.2.1 eq)
  rcases le_total high.card low.card with a | a
  · simpa [min_eq_left a] using upper
  · simpa [min_eq_right a] using lower

/-- For any collection of transcript rectangles, count the hits using the smaller side.
Cauchy–Schwarz charges their total area only once when they partition the inputs. -/
theorem rectangle_bound {ι : Type*} (leaves : Finset ι) (hits high low : ι → ℕ)
    {C X : ℕ} (bound : ∀ i ∈ leaves, hits i ≤ C * min (high i) (low i))
    (area : ∑ i ∈ leaves, high i * low i ≤ X^2) :
    (∑ i ∈ leaves, hits i)^2 ≤ C^2 * leaves.card * X^2 := by
  let side i := min (high i) (low i)
  have small : (∑ i ∈ leaves, hits i) ≤ C*∑ i ∈ leaves, side i := by
    rw [Finset.mul_sum]
    exact sum_le_sum bound
  have squares : ∑ i ∈ leaves, side i ^ 2 ≤ X^2 := by
    refine (sum_le_sum (fun i _ => ?_)).trans area
    simpa [pow_two] using Nat.mul_le_mul (min_le_left (high i) (low i)) (min_le_right (high i) (low i))
  have cs : (∑ i ∈ leaves, side i)^2 ≤ leaves.card * ∑ i ∈ leaves, side i^2 :=
    by simpa using Finset.sum_mul_sq_le_sq_mul_sq (R := ℕ) leaves 1 side
  calc
    _ ≤ (C*∑ i ∈ leaves, side i)^2 := Nat.pow_le_pow_left small 2
    _ = C^2 * (∑ i ∈ leaves, side i)^2 := mul_pow ..
    _ ≤ C^2 * (leaves.card * X^2) :=
      Nat.mul_le_mul_left _ (cs.trans (Nat.mul_le_mul_left _ squares))
    _ = _ := by ring

/-- Count the union of all hits for any disjoint family of transcript rectangles.
Different leaves can propose different remainder sets of the same bounded size. -/
theorem protocol_bound {ι : Type*} (leaves : Finset ι)
    (hits : ι → Finset (ℕ × ℕ)) (A high low : ι → Finset ℕ)
    (H L : Finset ℕ) {R B M X S : ℕ} (pos : 0<R) (mp : 0<M)
    (sizes : H.card ≤ X ∧ L.card ≤ X)
    (disjoint : (leaves : Set ι).PairwiseDisjoint (fun i => high i ×ˢ low i))
    (ranges : ∀ i ∈ leaves, high i ⊆ H ∧ low i ⊆ L ∧ (A i).card ≤ S)
    (domain : ∀ i ∈ leaves, ∀ t ∈ hits i,
      B*R ≤ t.1 ∧ t.1 < 2*B*R ∧ t.1%R ∈ A i)
    (factors : ∀ i ∈ leaves, ∀ t ∈ hits i,
      M ≤ 2*t.1 ∧ Odd t.2 ∧ t.2 < M ∧ M.Coprime t.1)
    (words : ∀ i ∈ leaves, ∀ t ∈ hits i,
      t.1*t.2/M ∈ high i ∧ t.1*t.2%M ∈ low i) :
    (leaves.biUnion hits).card^2 ≤ (S*B)^2 * leaves.card * X^2 := by
  have inside : leaves.biUnion (fun i => high i ×ˢ low i) ⊆ H ×ˢ L := by
    intro v hv
    obtain ⟨i,hi,hv⟩ := mem_biUnion.mp hv
    exact mem_product.mpr ⟨(ranges i hi).1 (mem_product.mp hv).1,
      (ranges i hi).2.1 (mem_product.mp hv).2⟩
  have area := (card_le_card inside).trans
    ((card_product H L) ▸ Nat.mul_le_mul sizes.1 sizes.2)
  rw [card_biUnion disjoint] at area
  simp only [card_product, ← sq] at area
  apply (Nat.pow_le_pow_left card_biUnion_le 2).trans
  apply rectangle_bound leaves (fun i => (hits i).card)
    (fun i => (high i).card) (fun i => (low i).card) _ area
  intro i hi
  exact (transcript_cell pos mp (domain i hi) (factors i hi) (words i hi)).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right B (ranges i hi).2.2))

/-- Even when the modulus varies with the proposed guess, a progression
of step R meets an interval of length at most B*R in at most B positions. -/
theorem interval_residue_card {points : Finset ℕ} {start R B a : ℕ}
    (pos : 0<R) (range : ∀ x ∈ points,
      start ≤ x ∧ x < start+B*R ∧ x ≡ a [MOD R]) : points.card ≤ B := by
  calc
    _ ≤ (Finset.range B).card := by
      apply card_le_card_of_injOn (fun x => (x-start)/R)
      · intro x hx
        exact mem_range.mpr ((Nat.div_lt_iff_lt_mul pos).mpr (by
          obtain ⟨_,h,_⟩ := range x hx
          omega))
      · intro x hx y hy same
        obtain ⟨xl,_,xc⟩ := range x hx
        obtain ⟨yl,_,yc⟩ := range y hy
        have h : (x-start)+start ≡ (y-start)+start [MOD R] := by
          simpa [Nat.sub_add_cancel xl,Nat.sub_add_cancel yl] using xc.trans yc.symm
        have rem : (x-start)%R=(y-start)%R := Nat.ModEq.add_right_cancel' start h
        have same_mul := congrArg (fun z => R*z) same
        have left := Nat.div_add_mod (x-start) R
        have right := Nat.div_add_mod (y-start) R
        change R*((x-start)/R) = R*((y-start)/R) at same_mul
        omega
    _ = B := card_range B

/-- After revealing a whole word, all transcripts reachable for that word may be
combined into one shortlist. Each proposed first factor determines at most one partner. -/
theorem revealed_word_bound (codes : Finset ℕ) (hits : ℕ → Finset (ℕ × ℕ))
    (shortlist : ℕ → Finset ℕ) {K : ℕ}
    (cap : ∀ i ∈ codes, (shortlist i).card ≤ K)
    (into : ∀ i ∈ codes, ∀ t ∈ hits i, t.1 ∈ shortlist i)
    (injective : ∀ i ∈ codes, ∀ p q r, (p,q) ∈ hits i → (p,r) ∈ hits i → q=r) :
    (codes.biUnion hits).card ≤ codes.card * K := by
  apply card_biUnion_le_card_mul _ _ _
  intro i hi
  apply le_trans _ (cap i hi)
  apply card_le_card_of_injOn Prod.fst (into i hi)
  rintro ⟨p,q⟩ hp ⟨r,s⟩ hr eq
  change p=r at eq
  subst r
  exact Prod.ext rfl (injective i hi p q s hp hr)

/-- Integer constants in the finite probability estimate, after clearing the
denominator 0.22². The density estimate for primes is applied separately. -/
theorem probability_constants :
    4 * 71000^2 < (2:ℕ)^26 * 22^2 ∧
    (2:ℕ)^38 * 2^26 * 2^40 * 2^512 = 2^616 := by decide +kernel

end PrimeFactors.FactorLaneAdvice
