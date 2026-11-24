import PrimeFactors.DivisorSample

namespace PrimeFactors

/-- A common unit multiplier preserves the gcd of a modular difference exactly. -/
theorem maskedRelations_unit_gcd {n : ℕ} [NeZero n] (u : (ZMod n)ˣ) (x y : ZMod n) :
    Nat.gcd (((u : ZMod n)*x - (u : ZMod n)*y).val) n = Nat.gcd (x-y).val n := by
  have cop : (u : ZMod n).val.Coprime n := (ZMod.isUnit_iff_coprime _ _).mp
    (by simpa only [ZMod.natCast_zmod_val] using u.isUnit)
  rw [← mul_sub, ZMod.val_mul, ← Nat.gcd_rec, Nat.gcd_comm n,
    Nat.Coprime.gcd_mul_left_cancel _ cop]

/-- Each selected relation can use its own unit mask. In a square dependency
their product is the mask of both final roots. -/
theorem maskedRelations_dependency_gcd {n : ℕ} [NeZero n] {ι : Type*} (s : Finset ι)
    (u : ι → (ZMod n)ˣ) (a : ι → ZMod n) (b : ZMod n) :
    Nat.gcd ((∏ i ∈ s, (u i : ZMod n)*a i) - (∏ i ∈ s, (u i : ZMod n))*b).val n =
      Nat.gcd ((∏ i ∈ s, a i)-b).val n := by
  rw [Finset.prod_mul_distrib, ← Units.coe_prod]
  exact maskedRelations_unit_gcd _ _ _

/-- A modular congruence of squares with different global signs gives a proper gcd.
This direction even holds for products with more than two prime factors. -/
theorem maskedRelations_split {n : ℕ} [NeZero n] {x y : ZMod n}
    (square : x^2=y^2) (plus : x≠y) (minus : x≠-y) :
    1 < (x-y).val.gcd n ∧ (x-y).val.gcd n < n := by
  have left : x-y ≠ 0 := sub_ne_zero.mpr plus
  have right : x+y ≠ 0 := fun h => minus (eq_neg_of_add_eq_zero_left h)
  have product : (x-y)*(x+y) = 0 := by rw [mul_comm, ← sq_sub_sq, square, sub_self]
  have positive : 0 < (x-y).val.gcd n := Nat.gcd_pos_of_pos_right _ (NeZero.pos n)
  constructor
  · have nontrivial : (x-y).val.gcd n ≠ 1 := by
      intro cop
      have unit : IsUnit (x-y) := by
        simpa only [ZMod.natCast_zmod_val] using (ZMod.isUnit_iff_coprime _ _).mpr cop
      exact right (unit.mul_right_inj.mp (product.trans (mul_zero _).symm))
    omega
  · have nonzero : 0 < (x-y).val := Nat.pos_of_ne_zero (fun h => left (by
      rw [← ZMod.natCast_zmod_val (x-y), h, Nat.cast_zero]))
    exact (Nat.le_of_dvd nonzero (Nat.gcd_dvd_left _ _)).trans_lt (ZMod.val_lt _)

/-- For unit roots and odd modulus, a proper gcd is equivalent to the roots
occupying distinct classes modulo the single global sign. -/
theorem maskedRelations_split_iff {n : ℕ} [NeZero n] {x y : ZMod n}
    (two : IsUnit (2 : ZMod n)) (unit : IsUnit y) (square : x^2=y^2) :
    (1 < (x-y).val.gcd n ∧ (x-y).val.gcd n < n) ↔ (x≠y ∧ x≠-y) := by
  constructor
  · rintro ⟨lo, hi⟩
    constructor
    · rintro rfl
      simp at hi
    · intro h
      have diff : x-y = -(2*y) := by rw [h]; ring
      have unitDiff : IsUnit (x-y) := diff ▸ (two.mul unit).neg
      have cop : (x-y).val.Coprime n := (ZMod.isUnit_iff_coprime _ _).mp
        (by simpa only [ZMod.natCast_zmod_val] using unitDiff)
      rw [show (x-y).val.gcd n = 1 from cop] at lo
      omega
  · exact fun ⟨h, h'⟩ => maskedRelations_split square h h'

/-- Square cofactors can be put on opposite sides of two equal-core rows.
This includes signed cores and requires no factorization of the modulus. -/
theorem maskedRelations_overlap {R : Type*} [CommRing R] {a b s t d : R}
    (left : a^2=d*s^2) (right : b^2=d*t^2) : (a*t)^2=(b*s)^2 := by
  rw [mul_pow, mul_pow, left, right]
  ring

/-- Two distinct short roots of the same square modulo N force a proper gcd.
The height condition excludes both possible global signs. -/
theorem maskedRelations_short {N x y : ℕ} [NeZero N]
    (square : (x : ZMod N)^2=(y : ZMod N)^2) (distinct : x≠y) (short : x+y<N) :
    1 < (x+y).gcd N ∧ (x+y).gcd N < N := by
  have xpos : x<N := by omega
  have ypos : y<N := by omega
  have apart : (x : ZMod N)≠(y : ZMod N) := by
    intro h
    apply distinct
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt xpos, Nat.mod_eq_of_lt ypos]
      using congrArg ZMod.val h
  have opposite : (x : ZMod N) ≠ -(y : ZMod N) := by
    intro h
    have zero : ((x+y : ℕ) : ZMod N)=0 := by rw [Nat.cast_add, h, neg_add_cancel]
    exact Nat.not_dvd_of_pos_of_lt (by omega) short
      ((ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp zero)
  have found := maskedRelations_split (y := -(y : ZMod N))
    (by simpa only [neg_sq] using square) opposite (by simpa only [neg_neg] using apart)
  simpa only [sub_neg_eq_add, ← Nat.cast_add, ZMod.val_natCast, Nat.mod_eq_of_lt short] using found

/-- For first-convergent rows, comparing two negative norms after removing
bounded square divisors needs no random-sign hypothesis. All quantities in
the hypotheses are available from the product and the two multipliers. -/
theorem maskedRelations_bounded_overlap {N K S a b s t c m k : ℕ} [NeZero N]
    (left : a^2+c*s^2=m*N) (right : b^2+c*t^2=k*N)
    (weighted : m*t^2 ≠ k*s^2) (mBound : m≤K) (kBound : k≤K)
    (sBound : s≤S) (tBound : t≤S) (size : 4*K*S^2<N) :
    1 < (a*t+b*s).gcd N ∧ (a*t+b*s).gcd N < N := by
  have first : (a*t)^2+c*(s*t)^2=(m*t^2)*N := by
    calc
      _ = (a^2+c*s^2)*t^2 := by ring
      _ = _ := by rw [left]; ring
  have second : (b*s)^2+c*(s*t)^2=(k*s^2)*N := by
    calc
      _ = (b^2+c*t^2)*s^2 := by ring
      _ = _ := by rw [right]; ring
  have distinct : a*t≠b*s := by
    intro same
    apply weighted
    apply Nat.eq_of_mul_eq_mul_right (NeZero.pos N)
    rw [← first, ← second, same]
  have modular (X D H : ℕ) (eqn : X^2+D=H*N) : (X : ZMod N)^2+D=0 := by
    have h := congrArg (fun B : ℕ => (B : ZMod N)) eqn
    simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_mul, ZMod.natCast_self, mul_zero] using h
  have square := add_right_cancel ((modular _ _ _ first).trans (modular _ _ _ second).symm)
  apply maskedRelations_short square distinct
  have height (v u : ℕ) (hv : v^2≤K*N) (hu : u≤S) : 2*(v*u)<N := by
    apply (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp
    calc
      (2*(v*u))^2 = 4*(v^2*u^2) := by ring
      _ ≤ 4*((K*N)*S^2) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hv (Nat.pow_le_pow_left hu 2))
      _ = (4*K*S^2)*N := by ring
      _ < N^2 := by simpa [pow_two] using Nat.mul_lt_mul_of_pos_right size (NeZero.pos N)
  have ah := height a t ((Nat.le_add_right ..).trans
    (left.le.trans (Nat.mul_le_mul_right N mBound))) tBound
  have bh := height b s ((Nat.le_add_right ..).trans
    (right.le.trans (Nat.mul_le_mul_right N kBound))) sBound
  omega

/-- All pairwise comparisons in a bucket are globally signed copies if and only
if the comparisons against one anchor are. Roots here have already been
normalized by their known unit square cofactors. -/
theorem maskedRelations_anchor {R ι : Type*} [CommRing R] (roots : ι → R) (anchor : ι) :
    (∀ i j, roots i=roots j ∨ roots i= -roots j) ↔
    (∀ i, roots i=roots anchor ∨ roots i= -roots anchor) := by
  constructor
  · exact fun h i => h i anchor
  · intro h i j
    rcases h i with hi | hi <;> rcases h j with hj | hj <;> simp [hi, hj]

/-- Transporting a fixed square root by a random mask and comparing to an
independently specified root of the target gives the full four-element fiber.
The test function sees the ratio of the two roots. -/
theorem maskedRelations_blind_fiber {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (cop : p.Coprime q) (po : p≠2) (qo : q≠2) [NeZero (p*q)]
    (x y : (ZMod (p*q))ˣ) {A : Type*} [AddCommMonoid A] (f : ZMod (p*q) → A) :
    let u := y⁻¹*x
    (∑ t : ZMod (p*q), if ((x : ZMod (p*q))*t)^2=(y : ZMod (p*q))^2
      then f ((u : ZMod (p*q))*t) else 0) =
      f 1 + f (-1) + f (divisorSampleMixed cop) + f (-divisorSampleMixed cop) := by
  let u := y⁻¹*x
  have undo (t : ZMod (p*q)) : (y : ZMod (p*q))*((u : ZMod (p*q))*t) = x*t := by
    simp [u, ← mul_assoc]
  have target (t : ZMod (p*q)) : ((x : ZMod (p*q))*t)^2=(y : ZMod (p*q))^2 ↔
      ((u : ZMod (p*q))*t)^2=1 := by
    rw [← undo, mul_pow]
    constructor
    · exact fun h => (y.isUnit.pow 2).mul_right_inj.mp (h.trans (mul_one _).symm)
    · intro h
      rw [h, mul_one]
  dsimp only
  simp_rw [target]
  let g (w : ZMod (p*q)) := if w^2=1 then f w else 0
  change (∑ t, g (u.mulLeft t)) = _
  rw [Equiv.sum_comp u.mulLeft g]
  exact divisorSample_four_roots hp hq cop po qo f

/-- Of the four masks reaching a specified unit square, exactly two give a
ratio different from both global signs of one. Every counted mask is a unit,
since its square times a unit is a unit. -/
theorem maskedRelations_blind_counts {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (cop : p.Coprime q) (po : p≠2) (qo : q≠2) [NeZero (p*q)]
    (x y : (ZMod (p*q))ˣ) :
    let u := y⁻¹*x
    (∑ t : ZMod (p*q), if ((x : ZMod (p*q))*t)^2=(y : ZMod (p*q))^2 then 1 else 0) = 4 ∧
    (∑ t : ZMod (p*q), if ((x : ZMod (p*q))*t)^2=(y : ZMod (p*q))^2 then
      (if (u : ZMod (p*q))*t=1 ∨ (u : ZMod (p*q))*t= -1 then 0 else 1) else 0) = 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  have pSign : (-1 : ZMod p) ≠ 1 :=
    Ring.neg_one_ne_one_of_char_ne_two (by simpa only [ZMod.ringChar_zmod_n] using po)
  have qSign : (-1 : ZMod q) ≠ 1 :=
    Ring.neg_one_ne_one_of_char_ne_two (by simpa only [ZMod.ringChar_zmod_n] using qo)
  let e := ZMod.chineseRemainder cop
  have coordinates : e (divisorSampleMixed cop) = (1,-1) := e.apply_symm_apply _
  have pos : divisorSampleMixed cop ≠ 1 := by
    intro h
    rw [h, map_one] at coordinates
    exact qSign ((congrArg Prod.snd coordinates).symm)
  have neg : divisorSampleMixed cop ≠ -1 := by
    intro h
    rw [h, map_neg, map_one] at coordinates
    exact pSign (congrArg Prod.fst coordinates)
  constructor
  · exact maskedRelations_blind_fiber hp hq cop po qo x y (fun _ => (1 : ℕ))
  · let f (r : ZMod (p*q)) : ℕ := if r=1 ∨ r= -1 then 0 else 1
    have h := maskedRelations_blind_fiber hp hq cop po qo x y f
    simpa [f, pos, neg, neg_eq_iff_eq_neg] using h

/-- The first continued-fraction numerators of the public square roots of
3·77 and 5·77 yield the same signed squarefree core with two different roots. -/
theorem maskedRelations_77 :
    Nat.sqrt (3*77)=15 ∧ Nat.sqrt (5*77)=19 ∧ 15^2+6=3*77 ∧ 19^2+6*2^2=5*77 ∧
    Nat.gcd (15*2-19) 77=11 ∧ Nat.gcd (15*2+19) 77=7 ∧
    7*11=77 ∧ Nat.Prime 7 ∧ Nat.Prime 11 := by decide +kernel

/-- All masks reaching the second target in the 77 example, and the four
actual gcds. The difference is computed modulo 77 to handle negative lifts. -/
theorem maskedRelations_77_fiber :
    (List.range 77).filter (fun t => (15*t)^2%77=19^2%77) = [2,9,68,75] ∧
    [2,9,68,75].map (fun t => Nat.gcd ((15*t+77-19)%77) 77) = [11,1,77,7] := by
  decide +kernel

/-- The small multiplier bound already guarantees a proper divisor in this
second example. The common quotient 12 needs no squarefree decomposition. -/
theorem maskedRelations_247 :
    Nat.sqrt (3*247)=27 ∧ Nat.sqrt (7*247)=41 ∧ 27^2+12=3*247 ∧
    41^2+12*2^2=7*247 ∧ 4*7*2^2<247 ∧ 3*2^2≠7*1^2 ∧
    Nat.gcd (27*2+41) 247=19 ∧ Nat.gcd (27*2-41) 247=13 ∧
    13*19=247 ∧ Nat.Prime 13 ∧ Nat.Prime 19 := by decide +kernel

/-- The Pell unit 55 + 12√21 preserves the equation that forces the two
first-row deficits to be 12 and 48. -/
theorem maskedRelations_family_step {h b : ℕ} (eqn : b^2+20=21*h^2) :
    (252*h+55*b)^2+20=21*(55*h+12*b)^2 := by nlinarith only [eqn]

/-- Every member of this family above the initial pair is split by the same
two public first-convergent rows. The factors need not be prime. -/
theorem maskedRelations_family {h b : ℕ} (hh : 9≤h) (hb : 41≤b)
    (eqn : b^2+20=21*h^2) :
    let N := 3*h^2+4
    (3*N).sqrt=3*h ∧ (7*N).sqrt=b ∧ 1<(6*h+b).gcd N ∧ (6*h+b).gcd N<N := by
  let N := 3*h^2+4
  haveI : NeZero N := ⟨by simp [N]⟩
  have first : (3*h)^2+12=3*N := by dsimp [N]; ring
  have second : b^2+12*2^2=7*N := by dsimp [N]; nlinarith only [eqn]
  have floor (r E : ℕ) (bound : E<2*r+1) : (r^2+E).sqrt=r := by
    apply Nat.le_antisymm
    · apply Nat.lt_succ_iff.mp
      apply Nat.sqrt_lt'.mpr
      nlinarith only [bound]
    · exact Nat.le_sqrt'.mpr (Nat.le_add_right _ _)
  have size : 4*7*2^2<N := by
    dsimp [N]
    nlinarith only [Nat.pow_le_pow_left hh 2]
  have divisor := maskedRelations_bounded_overlap (m := 3) (k := 7) (s := 1) (t := 2)
    (c := 12) (by simpa using first) second (by decide) (by decide) (by decide)
    (by decide) (by decide) size
  change (3*N).sqrt=3*h ∧ (7*N).sqrt=b ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [← first]
    exact floor _ _ (by omega)
  · rw [← second]
    exact floor _ _ (by omega)
  · simpa only [show 3*h*2=6*h by ring, mul_one] using divisor

end PrimeFactors
