import PrimeFactors.PublicPrimeSquareCounts
import PrimeFactors.MinimalPrimeSquarePeriod

/-! The complete joint pattern need only contain a squared prime when the
product admits a singular discriminant there. All other tests can use their
first digit without changing a single accepted sum. -/
namespace PrimeFactors.CompressedPrimeSquareWheel

open ChebyshevQuarticScale (fresh crossed)
open LocalSumMenu (count)
open PublicPrimeSquareCounts (squares)
open MinimalPrimeSquarePeriod (Period)

def freshMod := 4*9*25*7*11*13*17*19
def crossedMod := 4*9*25*49*11*13*17*361

/-- With one bit per residue, omit the modulo-four starting class and
machine-specific padding. -/
theorem local_table_bits :
    ([9,25,7,11,13,17,19] : List ℕ).sum = 101 ∧
    ([9,25,49,11,13,17,361] : List ℕ).sum = 485 := by decide

def Pass (n m s : ℕ) := AdmissibleSum (n : ZMod m) (s : ZMod m)

private theorem split {a b : ℕ} (cop : a.Coprime b) (n s : ℕ) :
    Pass n (a*b) s ↔ Pass n a s ∧ Pass n b s := PublicWheelLookupCosts.extend_prefix cop n s

private theorem same {n p square : ℕ} (hp : p.Prime) (odd : p ≠ 2) (eq : p^2 = square)
    (nonsq : ¬∃ x : ZMod p, x*x=(n : ZMod p)) (s : ℕ) :
    Pass n square s ↔ Pass n p s := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [←eq]
  exact MinimalPrimeSquarePeriod.nonsquare_pullback odd
    (fun ⟨x,h⟩ => nonsq ⟨x,h.symm⟩) s

/-- These equivalences hold at every position, including an incomplete period. -/
theorem fresh_iff (s : ℕ) : Pass fresh PublicPrimeSquareCounts.modulus s ↔ Pass fresh freshMod s := by
  simp (disch := decide) only [PublicPrimeSquareCounts.modulus, freshMod, split]
  simp only [same (n:=fresh) (p:=7) (square:=49) (by decide) (by decide) rfl (by decide +kernel),
    same (n:=fresh) (p:=11) (square:=121) (by decide) (by decide) rfl (by decide +kernel),
    same (n:=fresh) (p:=13) (square:=169) (by decide) (by decide) rfl (by decide +kernel),
    same (n:=fresh) (p:=17) (square:=289) (by decide) (by decide) rfl (by decide +kernel),
    same (n:=fresh) (p:=19) (square:=361) (by decide) (by decide) rfl (by decide +kernel)]

theorem crossed_iff (s : ℕ) : Pass crossed PublicPrimeSquareCounts.modulus s ↔ Pass crossed crossedMod s := by
  simp (disch := decide) only [PublicPrimeSquareCounts.modulus, crossedMod, split]
  simp only [same (n:=crossed) (p:=11) (square:=121) (by decide) (by decide) rfl (by decide +kernel),
    same (n:=crossed) (p:=13) (square:=169) (by decide) (by decide) rfl (by decide +kernel),
    same (n:=crossed) (p:=17) (square:=289) (by decide) (by decide) rfl (by decide +kernel)]

private theorem crt_count {a b : ℕ} (cop : a.Coprime b) (n : ℕ) :
    count n (a*b) = count n a * count n b := card_admissibleSum_crt cop n

theorem fresh_dimensions :
    freshMod = 290990700 ∧ count fresh freshMod = 90720 ∧
    323323*freshMod = PublicPrimeSquareCounts.modulus := by
  have c := IntervalWheelControls.fresh_components
  simp only [IntervalWheelControls.components,List.map_cons,List.map_nil,List.cons.injEq,and_true] at c
  obtain ⟨h4,_,_,h7,h11,h13,h17,h19⟩ := c
  exact ⟨by decide, by
    have sq := PublicPrimeSquareCounts.fresh_components
    simp only [squares,List.map_cons,List.map_nil,List.cons.injEq,and_true] at sq
    simp (disch := decide) only [freshMod,crt_count,h4,
      sq.1,sq.2.1,h7,h11,h13,h17,h19], by decide⟩

theorem crossed_dimensions :
    crossedMod = 38701763100 ∧ count crossed crossedMod = 8279040 ∧
    2431*crossedMod = PublicPrimeSquareCounts.modulus := by
  have c := IntervalWheelControls.crossed_components
  simp only [IntervalWheelControls.components,List.map_cons,List.map_nil,List.cons.injEq,and_true] at c
  obtain ⟨h4,_,_,_,h11,h13,h17,_⟩ := c
  exact ⟨by decide, by
    have sq := PublicPrimeSquareCounts.crossed_components
    simp only [squares,List.map_cons,List.map_nil,List.cons.injEq,and_true] at sq
    obtain ⟨h9,h25,h49,_,_,_,h361⟩ := sq
    simp (disch := decide) only [crossedMod,crt_count,h4,h9,h25,h49,h11,h13,h17,h361], by decide⟩

/-- A period must contain the part of a modulus not cancelled by its local count. -/
private def forced (m c : ℕ) := m / (m.gcd c)

private theorem force_of_row {n m c t : ℕ} [NeZero m] (count_eq : count n m=c)
    (period : Period n m t) : forced m c ∣ t := by
  have pos := Nat.gcd_pos_of_pos_left c (NeZero.pos m)
  apply (Nat.coprime_div_gcd_div_gcd pos).dvd_of_dvd_mul_right
  apply Nat.dvd_of_mul_dvd_mul_right pos
  rw [Nat.div_mul_cancel (Nat.gcd_dvd_left _ _),Nat.mul_assoc,
    Nat.div_mul_cancel (Nat.gcd_dvd_right _ _),Nat.mul_comm]
  rw [←count_eq]
  exact MinimalPrimeSquarePeriod.modulus_dvd_card_mul _ period

private def combined (counts : List ℕ) :=
  ((4::squares).zipWith forced (1::counts)).foldr Nat.lcm 1

private theorem least_from_rows {n t a b c d f g j : ℕ}
    (components : squares.map (count n) = [a,b,c,d,f,g,j])
    (four : count n 4=1) (pass : Period n PublicPrimeSquareCounts.modulus t) :
    combined [a,b,c,d,f,g,j] ∣ t := by
  simp (disch := decide) only [PublicPrimeSquareCounts.modulus,MinimalPrimeSquarePeriod.crt_iff] at pass
  simp only [squares,List.map_cons,List.map_nil,List.cons.injEq,and_true] at components
  obtain ⟨h9,h25,h49,h121,h169,h289,h361⟩ := components
  obtain ⟨⟨⟨⟨⟨⟨⟨p4,p9⟩,p25⟩,p49⟩,p121⟩,p169⟩,p289⟩,p361⟩ := pass
  exact Nat.lcm_dvd (force_of_row four p4) (Nat.lcm_dvd (force_of_row h9 p9)
    (Nat.lcm_dvd (force_of_row h25 p25) (Nat.lcm_dvd (force_of_row h49 p49)
    (Nat.lcm_dvd (force_of_row h121 p121) (Nat.lcm_dvd (force_of_row h169 p169)
    (Nat.lcm_dvd (force_of_row h289 p289) (Nat.lcm_dvd (force_of_row h361 p361) (one_dvd t))))))))

private theorem period_of_equiv {n m t : ℕ}
    (eq : ∀ s, Pass n PublicPrimeSquareCounts.modulus s ↔ Pass n m s) (div : m∣t) :
    Period n PublicPrimeSquareCounts.modulus t := by
  letI : NeZero PublicPrimeSquareCounts.modulus := ⟨by decide⟩
  intro x
  obtain ⟨s,rfl⟩ := ZMod.natCast_zmod_surjective x
  rw [←Nat.cast_add]
  change Pass n _ (s+t) ↔ Pass n _ s
  rw [eq,eq]
  unfold Pass
  rw [Nat.cast_add,(ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr div,add_zero]

theorem fresh_minimal (t : ℕ) : Period fresh PublicPrimeSquareCounts.modulus t ↔ freshMod∣t := by
  refine ⟨fun h => ?_,period_of_equiv fresh_iff⟩
  rw [show freshMod = combined [2,7,21,55,78,136,171] by decide +kernel]
  exact least_from_rows PublicPrimeSquareCounts.fresh_components
    (IntervalWheelResidues.count_four (by decide +kernel)) h

theorem crossed_minimal (t : ℕ) : Period crossed PublicPrimeSquareCounts.modulus t ↔ crossedMod∣t := by
  refine ⟨fun h => ?_,period_of_equiv crossed_iff⟩
  rw [show crossedMod = combined [2,7,16,55,78,136,154] by decide +kernel]
  exact least_from_rows PublicPrimeSquareCounts.crossed_components
    (IntervalWheelResidues.count_four (by decide +kernel)) h

end PrimeFactors.CompressedPrimeSquareWheel
