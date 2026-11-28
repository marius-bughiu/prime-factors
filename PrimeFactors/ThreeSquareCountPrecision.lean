import PrimeFactors.ThreeSquareRadiusCounts
import PrimeFactors.QuarticLocalSquareCriterion

/-! What extra information the unfiltered lattice point count can supply
at an odd semiprime radius. General count formulas enter as explicit premises. -/
namespace PrimeFactors.ThreeSquareCountPrecision

open ThreeSquareRadiusCounts
attribute [local irreducible] count

/-- Subtract the six-times-radius baseline, in units of twelve points. -/
noncomputable def excess (n : ℕ) : ℤ := ((count n false:ℤ)-6*n)/12

/-- Only one of the two mixed cases is needed because the product is symmetric.
When both residues are three, subtracting two from the excess gives the sum. -/
theorem excess_cases (h : HurwitzFormula) {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (ne : p≠q) (op : Odd p) (oq : Odd q) :
    (p%4=1 → q%4=1 → excess (p*q)=0) ∧
    (p%4=1 → q%4=3 → excess (p*q)=p) ∧
    (p%4=3 → q%4=3 → excess (p*q)=(p:ℤ)+q+2) := by
  have raw := semiprime_total h pp qp ne op oq
  unfold excess
  rw [raw,Nat.cast_mul]
  refine ⟨?_,?_,?_⟩ <;> intro a b <;>
    simp only [sign,a,b,if_true,show ¬(3:ℕ)=1 by decide,if_false] <;>
    ring_nf <;> omega

private theorem split_iff {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (op : Odd p) (oq : Odd q) :
    IsSquare (-1:ZMod (p*q)) ↔ p%4=1 ∧ q%4=1 := by
  rw [QuarticLocalSquareCriterion.square_iff (op.mul oq)]
  constructor
  · intro h
    exact ⟨h _ pp (dvd_mul_right ..),h _ qp (dvd_mul_left ..)⟩
  · rintro ⟨a,b⟩ l prime div
    rcases prime.dvd_mul.mp div with left|right
    · rwa [(Nat.prime_dvd_prime_iff_eq prime pp).mp left]
    · rwa [(Nat.prime_dvd_prime_iff_eq prime qp).mp right]

private theorem same_class {p q : ℕ} (hp : Odd p) (hq : Odd q) (word : (p*q)%4=1) :
    (p%4=1 ∧ q%4=1) ∨ (p%4=3 ∧ q%4=3) := by
  obtain ⟨a,ea⟩ := hp
  obtain ⟨b,eb⟩ := hq
  have pc : p%4=1 ∨ p%4=3 := by omega
  have qc : q%4=1 ∨ q%4=3 := by omega
  rw [Nat.mul_mod] at word
  rcases pc with pc|pc <;> rcases qc with qc|qc <;> rw [pc,qc] at word <;> omega

private theorem bounds {p q : ℕ} (order : p≤q) :
    p≤(p*q).sqrt ∧ 2*(p*q).sqrt≤p+q := by
  refine ⟨Nat.le_sqrt.mpr (Nat.mul_le_mul_left p order),?_⟩
  have sqr := Nat.sqrt_le' (p*q)
  by_contra! bad
  have sq := Nat.pow_lt_pow_left bad (by decide : (2:ℕ)≠0)
  nlinarith [sq_nonneg ((p:ℤ)-q)]

/-- At a product equal to one modulo four, the permitted error is twelve
times the public integer square root. Even that coarse readout decides
whether minus one is a square at the whole input. -/
theorem identifies_square (h : HurwitzFormula) {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (ne : p≠q) (op : Odd p) (oq : Odd q) (order : p≤q) (word : (p*q)%4=1)
    (v : ℤ) (accuracy : |v-(count (p*q) false:ℤ)|<12*((p*q).sqrt:ℤ)) :
    IsSquare (-1:ZMod (p*q)) ↔ v<6*((p*q:ℕ):ℤ)+12*((p*q).sqrt:ℤ) := by
  rw [split_iff pp qp op oq]
  rw [abs_lt] at accuracy
  have raw := semiprime_total h pp qp ne op oq
  have sum := (bounds order).2
  rcases same_class op oq word with ⟨a,b⟩|⟨a,b⟩ <;>
    simp only [sign,a,b,if_true,show ¬(3:ℕ)=1 by decide,if_false] at raw ⊢ <;>
    push_cast <;> constructor <;> intro hs <;> first | trivial | nlinarith

/-- A cheap approximation at the same accuracy if supplied the answer
to the square question. The factors satisfy the usual balance promise. -/
theorem estimate_with_bit (h : HurwitzFormula) {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (ne : p≠q) (op : Odd p) (oq : Odd q) (order : p≤q) (balanced : q<2*p)
    (word : (p*q)%4=1) (bit : Bool) (correct : bit=true ↔ IsSquare (-1:ZMod (p*q))) :
    let n := p*q
    let v : ℤ := 6*n+(if bit then 0 else 24*(n.sqrt:ℤ)+24)
    |v-(count n false:ℤ)|<12*(n.sqrt:ℤ) := by
  rw [split_iff pp qp op oq] at correct
  have raw := semiprime_total h pp qp ne op oq
  obtain ⟨floor,sum⟩ := bounds order
  have pos := pp.pos
  dsimp only
  rw [abs_lt]
  rcases same_class op oq word with ⟨a,b⟩|⟨a,b⟩
  · rw [if_pos (correct.mpr ⟨a,b⟩)]
    simp only [sign,a,b,if_true] at raw
    push_cast
    constructor <;> nlinarith
  · have no : ¬ bit=true := fun yes => by have one := (correct.mp yes).1; omega
    rw [if_neg no]
    simp only [sign,a,b,show ¬(3:ℕ)=1 by decide,if_false] at raw
    push_cast
    constructor <;> nlinarith

end PrimeFactors.ThreeSquareCountPrecision
