import PrimeFactors.CircleBranchReadout

/-! Draw a residue uniformly, or draw an ordered modular circle point
uniformly and observe its first coordinate. These laws give slightly
different probabilities to the same public mark. -/

namespace PrimeFactors.CircleBranchSampling
open Finset CircleBranchCount CircleBranchReadout CircleCoordinateFibers SphereCircleIdentity ThreeSquareRadiusCounts
open scoped Classical

noncomputable def markedPoints (n : ℕ) [NeZero n] (a : ℤ) : Finset (ZMod n×ZMod n) :=
  (circle (ZMod n) (a:ZMod n)).filter fun w => w.1∈marked n a

noncomputable def rawRate (n : ℕ) [NeZero n] (a : ℤ) : ℚ := ((marked n a).card:ℚ)/n

noncomputable def circleRate (n : ℕ) [NeZero n] (a : ℤ) : ℚ :=
  ((markedPoints n a).card:ℚ)/(circle (ZMod n) (a:ZMod n)).card

private theorem local_size {p : ℕ} [Fact p.Prime] (op : p≠2) {t x y : ZMod p}
    (onCircle : x^2+y^2=t) : (fiber t x).card=(if y=0 then 1 else 2) := by
  have two : (2:ZMod p)≠0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  by_cases zero : y=0
  · rw [if_pos zero]
    exact (one_iff two t x).mpr (by simpa [zero] using onCircle)
  · rw [if_neg zero]
    have le := at_most_two t x
    have pos := card_pos.mpr ⟨y,mem_fiber.mpr onCircle⟩
    have ne : (fiber t x).card≠1 := by
      intro one
      have eqn := (one_iff two t x).mp one
      apply (pow_ne_zero 2 zero)
      linear_combination onCircle-eqn
    omega

private theorem marked_on {n : ℕ} [NeZero n] {a : ℤ} {x y : ZMod n}
    (onCircle : x^2+y^2=(a:ZMod n)) : x∈marked n a ↔ ¬IsUnit y := by
  have remainder : (a:ZMod n)-x^2=y^2 := by linear_combination -onCircle
  simp only [marked,mem_filter,mem_univ,true_and,remainder,isUnit_pow_iff (by decide : 2≠0)]

/-- For an occupied first coordinate of a negative-Jacobi circle, a public
mark is equivalent to exactly two second coordinates. -/
theorem two_lifts {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) {a : ℤ} (neg : jacobiSym a (p*q)= -1)
    {x y : ZMod (p*q)} (onCircle : x^2+y^2=(a:ZMod (p*q))) :
    x∈marked (p*q) a ↔ (fiber (a:ZMod (p*q)) x).card=2 := by
  let cop := (Nat.coprime_primes hp.out hq.out).mpr diff
  let e := ZMod.chineseRemainder cop
  have eqn := congrArg e onCircle
  rw [map_add,map_pow,map_pow,Prod.ext_iff] at eqn
  have pl := local_size op eqn.1
  have ql := local_size oq eqn.2
  have both : ¬((e y).1=0 ∧ (e y).2=0) := by
    rintro ⟨l,r⟩
    have zero : y=0 := e.injective ((Prod.ext l r).trans (map_zero e).symm)
    apply never_square diff neg x
    simpa [zero] using (show (a:ZMod (p*q))-x^2=y^2 by linear_combination -onCircle)
  rw [marked_on onCircle,fiber_crt cop,←isUnit_map_iff e,Prod.isUnit_iff]
  change (¬(IsUnit (e y).1 ∧ IsUnit (e y).2)) ↔
    (fiber (e (a:ZMod (p*q))).1 (e x).1).card*(fiber (e (a:ZMod (p*q))).2 (e x).2).card=2
  rw [pl,ql]
  simp only [isUnit_iff_ne_zero]
  split_ifs <;> simp_all

/-- Either the public difference or the second coordinate gives a proper gcd
on exactly the same occupied first coordinates. -/
theorem both_gcd {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) {a : ℤ} (neg : jacobiSym a (p*q)= -1)
    {x y : ZMod (p*q)} (onCircle : x^2+y^2=(a:ZMod (p*q))) :
    (x∈marked (p*q) a ↔ 1<y.val.gcd (p*q) ∧ y.val.gcd (p*q)<p*q) ∧
    (x∈marked (p*q) a ↔ 1<((a:ZMod (p*q))-x^2).val.gcd (p*q) ∧
      ((a:ZMod (p*q))-x^2).val.gcd (p*q)<p*q) := by
  refine ⟨?_,proper_gcd diff neg x⟩
  rw [marked_on onCircle]
  have nz : y.val≠0 := by
    intro zero
    have y0 := ZMod.val_injective (p*q) (zero.trans ZMod.val_zero.symm)
    apply never_square diff neg x
    simpa [y0] using (show (a:ZMod (p*q))-x^2=y^2 by linear_combination -onCircle)
  have small := (Nat.gcd_le_left (p*q) (Nat.pos_of_ne_zero nz)).trans_lt (ZMod.val_lt y)
  have pos := Nat.gcd_pos_of_pos_right y.val (Nat.mul_pos hp.out.pos hq.out.pos)
  have unit : IsUnit y ↔ y.val.gcd (p*q)=1 := by
    simpa only [ZMod.natCast_zmod_val,Nat.Coprime] using ZMod.isUnit_iff_coprime y.val (p*q)
  rw [unit]
  omega

theorem marked_point_count {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) {a : ℤ} (neg : jacobiSym a (p*q)= -1) :
    (markedPoints (p*q) a).card=2*(level (ZMod (p*q)) (a:ZMod (p*q)) 2).card := by
  rw [←points_at_level (a:ZMod (p*q)) 2]
  apply congrArg Finset.card
  ext w
  simp only [markedPoints,mem_filter,mem_circle]
  apply and_congr_right
  exact fun onCircle => two_lifts diff op oq neg onCircle

/-- Give the name p to the prime at which the target is a square. -/
theorem rates {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) {a : ℤ} (neg : jacobiSym a (p*q)= -1)
    (sq : legendreSym p a=1) :
    rawRate (p*q) a=2/(p:ℚ) ∧ circleRate (p*q) a=2/((p:ℚ)-(sign p:ℚ)) := by
  have count := half_count diff op oq neg
  have read := readout diff op oq neg
  dsimp only at read
  obtain ⟨raw,ns⟩ : (marked (p*q) a).card=2*q ∧ legendreSym q a= -1 := by
    rcases count with h|h
    · exact ⟨h.1,h.2.2⟩
    · omega
  have lev : ((level (ZMod (p*q)) (a:ZMod (p*q)) 2).card:ℤ)=q-sign q := by
    rcases read with h|h
    · exact h.2.2
    · omega
  have cop := (Nat.coprime_primes hp.out hq.out).mpr diff
  have cr := circle_crt cop (a:ZMod (p*q))
  simp only [map_intCast,Prod.fst_intCast,Prod.snd_intCast] at cr
  have P := prime_unit op (a:ZMod p) (fun h => by rw [(legendreSym.eq_zero_iff p a).mpr h] at sq; contradiction)
  have Q := prime_unit oq (a:ZMod q) (fun h => by rw [(legendreSym.eq_zero_iff q a).mpr h] at ns; contradiction)
  have nz : (q:ℚ)≠0 := by exact_mod_cast hq.out.ne_zero
  have qg : 1<(q:ℚ) := by exact_mod_cast hq.out.one_lt
  have sc : sign q=1 ∨ sign q= -1 := by unfold sign; split <;> simp
  have good : (q:ℚ)-(sign q:ℚ)≠0 := by
    rcases sc with h|h <;> rw [h] <;> push_cast <;> linarith
  constructor
  · rw [rawRate,raw]
    push_cast
    exact mul_div_mul_right _ _ nz
  · rw [circleRate,marked_point_count diff op oq neg,cr]
    push_cast
    have pr : ((circle (ZMod p) (a:ZMod p)).card:ℚ)=(p:ℚ)-(sign p:ℚ) := by exact_mod_cast P
    have qr : ((circle (ZMod q) (a:ZMod q)).card:ℚ)=(q:ℚ)-(sign q:ℚ) := by exact_mod_cast Q
    have lr : ((level (ZMod (p*q)) (a:ZMod (p*q)) 2).card:ℚ)=q-(sign q:ℚ) := by exact_mod_cast lev
    rw [pr,qr,lr]
    exact mul_div_mul_right _ _ good

theorem relative {p q : ℕ} [hp : Fact p.Prime] [Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) {a : ℤ} (neg : jacobiSym a (p*q)= -1)
    (sq : legendreSym p a=1) :
    |circleRate (p*q) a/rawRate (p*q) a-1|≤1/((p:ℚ)-1) := by
  obtain ⟨raw,circ⟩ := rates diff op oq neg sq
  have pos : 1<(p:ℚ) := by exact_mod_cast hp.out.one_lt
  have nonzero : (p:ℚ)≠0 := by linarith
  have minus : (p:ℚ)-1≠0 := by linarith
  have plus : (p:ℚ)+1≠0 := by linarith
  rw [raw,circ]
  unfold sign
  split
  · simp only [Int.cast_one]
    have eqn : 2/((p:ℚ)-1)/(2/p)-1=1/(p-1) := by
      rw [div_div_div_comm, div_self (by norm_num : (2:ℚ)≠0)]
      field_simp [minus,nonzero]
    rw [eqn,abs_of_nonneg (one_div_nonneg.mpr (by linarith))]
  · simp only [Int.cast_neg,Int.cast_one,sub_neg_eq_add]
    have eqn : 2/((p:ℚ)+1)/(2/p)-1= -(1/(p+1)) := by
      rw [div_div_div_comm, div_self (by norm_num : (2:ℚ)≠0)]
      field_simp [plus,nonzero]
    rw [eqn,abs_neg,abs_of_nonneg (one_div_nonneg.mpr (by linarith))]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)

set_option exponentiation.threshold 2048 in
theorem full_width {p q : ℕ} [hp : Fact p.Prime] [Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) {a : ℤ} (neg : jacobiSym a (p*q)= -1)
    (sq : legendreSym p a=1) (size : 2^1023≤p) :
    |circleRate (p*q) a/rawRate (p*q) a-1|<1/(2:ℚ)^1022 := by
  apply (relative diff op oq neg sq).trans_lt
  apply one_div_lt_one_div_of_lt (by positivity)
  have big : (2:ℚ)^1023≤p := by exact_mod_cast size
  linarith only [big,show (2:ℚ)^1022+1<2^1023 by norm_num]

/-- The projection decreases the probability for target 7 and increases it for
target 11 on the same modulus. -/
theorem controls :
    (rawRate 15 7=2/3 ∧ circleRate 15 7=1/2) ∧
    (rawRate 15 11=2/5 ∧ circleRate 15 11=1/2) := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have left := rates (p:=3) (q:=5) (a:=7) (by decide) (by decide) (by decide)
    (by norm_num) (by rw [jacobiSym.legendreSym.to_jacobiSym]; norm_num)
  have right := rates (p:=5) (q:=3) (a:=11) (by decide) (by decide) (by decide)
    (by norm_num) (by rw [jacobiSym.legendreSym.to_jacobiSym]; norm_num)
  constructor
  · exact ⟨left.1,left.2.trans (by norm_num [sign])⟩
  · exact ⟨right.1,right.2.trans (by norm_num [sign])⟩

end PrimeFactors.CircleBranchSampling
