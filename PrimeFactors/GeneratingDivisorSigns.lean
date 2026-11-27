import PrimeFactors.ReciprocalDivisorClasses
import PrimeFactors.SaturatedTraceSplit
import Mathlib.Algebra.Order.Floor.Div

/-! Generate positive factor-sign residues from half-root indices. For an odd
prime power of odd exponent, the output progressions have stride the prime.
When the prime is 3 modulo 4, there is also a direct inverse to the generator. -/

namespace PrimeFactors.GeneratingDivisorSigns

open ReciprocalSumCharacter
open scoped Nat

/-- Index 0 uses root 1; the largest root is floor(p/2). -/
def residue (p : ℕ) (i : Fin (p/2)) : ℕ := (i.val+1)^2 % p

private def root (p : ℕ) (i : Fin (p/2)) : ZMod p := ((i.val+1 : ℕ) : ZMod p)

private theorem root_val {p : ℕ} [NeZero p] (i : Fin (p/2)) :
    (root p i).val = i.val+1 := by
  have h := i.isLt
  rw [root, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

private theorem root_ne {p : ℕ} [NeZero p] (i : Fin (p/2)) : root p i ≠ 0 := by
  intro h
  have z := (ZMod.val_eq_zero _).mpr h
  rw [root_val] at z
  omega

private theorem val_sq {p : ℕ} [NeZero p] (i : Fin (p/2)) :
    ((root p i)^2).val = residue p i := by
  rw [root, ← Nat.cast_pow, ZMod.val_natCast, residue]

private theorem square_inj {p : ℕ} [Fact p.Prime] (odd : Odd p) {i j : Fin (p/2)}
    (h : (root p i)^2 = (root p j)^2) : i = j := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with eq | eq
  · have hv := congrArg ZMod.val eq
    rw [root_val,root_val] at hv
    exact Fin.ext (by omega)
  · haveI : NeZero (root p j) := ⟨root_ne _⟩
    have hv := congrArg ZMod.val eq
    rw [ZMod.val_neg_of_ne_zero, root_val, root_val] at hv
    have hi := i.isLt
    have hj := j.isLt
    have par := Nat.odd_iff.mp odd
    omega

private theorem root_pair {p : ℕ} [NeZero p] {x : ZMod p} (nz : x ≠ 0) :
    ∃ i : Fin (p/2), root p i = x ∨ root p i = -x := by
  haveI : NeZero x := ⟨nz⟩
  have ne := (ZMod.val_eq_zero x).not.mpr nz
  have bound := x.val_lt
  by_cases h : x.val ≤ p/2
  · refine ⟨⟨x.val-1,by omega⟩,Or.inl (ZMod.val_injective p ?_)⟩
    rw [root_val]
    simp; omega
  · refine ⟨⟨p-x.val-1,by omega⟩,Or.inr (ZMod.val_injective p ?_)⟩
    rw [root_val,ZMod.val_neg_of_ne_zero]
    simp; omega

/-- Every positive residue modulo an odd prime has exactly one half-root
index. Each index produces its residue with one modular squaring. -/
theorem prime_residues {p : ℕ} [Fact p.Prime] (odd : Odd p) (x : ℕ) :
    jacobiSym (x : ℤ) p = 1 ↔ ∃! i : Fin (p/2), x%p = residue p i := by
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast]
  have same (i : Fin (p/2)) : x%p = residue p i ↔ (x : ZMod p) = (root p i)^2 := by
    rw [← ZMod.val_natCast, ← val_sq, (ZMod.val_injective p).eq_iff]
  simp_rw [same]
  constructor
  · intro pos
    have nz : (x : ZMod p) ≠ 0 := fun h => by simp [h] at pos
    obtain ⟨y,hy⟩ := (quadraticChar_one_iff_isSquare nz).mp pos
    have yn : y ≠ 0 := fun h => nz (by simpa [h] using hy)
    obtain ⟨i,h⟩ := root_pair yn
    have eq : (x : ZMod p) = (root p i)^2 := by
      rcases h with h | h
      · rw [h,pow_two,hy]
      · rw [h,neg_sq,pow_two,hy]
    exact ⟨i,eq,fun j hj => square_inj odd (hj.symm.trans eq)⟩
  · rintro ⟨i,h,_⟩
    rw [h]
    exact (quadraticChar_one_iff_isSquare (pow_ne_zero _ (root_ne i))).mpr (IsSquare.sq _)

/-- For p ≡ 3 modulo 4, the inverse index needs one modular power and a reflection. -/
def index {p : ℕ} (x : ZMod p) : ℕ :=
  let y := SaturatedTraceSplit.powerMod p x.val ((p+1)/4)
  min y (p-y) - 1

private theorem reducedPower {p : ℕ} [NeZero p] (x : ZMod p) (n : ℕ) :
    SaturatedTraceSplit.powerMod p x.val n = (x^n).val := by
  rw [SaturatedTraceSplit.powerMod_eq, ← ZMod.val_natCast, Nat.cast_pow, ZMod.natCast_zmod_val]

theorem index_residue {p : ℕ} [Fact p.Prime] (three : p%4=3) (i : Fin (p/2)) :
    index (residue p i : ZMod p) = i.val := by
  let x := root p i
  have xp : x ≠ 0 := root_ne i
  haveI : NeZero x := ⟨xp⟩
  have id : (residue p i : ZMod p) = x^2 := by rw [← val_sq, ZMod.natCast_zmod_val]
  have leg : (x^2)^((p+1)/4*2) = x^2 := by
    rw [← pow_mul]
    have eq : 2*((p+1)/4*2) = p-1+2 := by omega
    rw [eq, pow_add, ZMod.pow_card_sub_one_eq_one xp, one_mul]
  have either : (x^2)^((p+1)/4) = x ∨ (x^2)^((p+1)/4) = -x :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by rw [← pow_mul]; exact leg)
  have small : x.val ≤ (-x).val := by
    rw [ZMod.val_neg_of_ne_zero,show x.val = i.val+1 from root_val i]
    have := i.isLt
    omega
  haveI : NeZero ((x^2)^((p+1)/4)) := ⟨pow_ne_zero _ (pow_ne_zero _ xp)⟩
  rw [index,reducedPower,id,← ZMod.val_neg_of_ne_zero]
  rcases either with yes | yes
  · rw [yes,min_eq_left small,show x.val = i.val+1 from root_val i]; omega
  · rw [yes,neg_neg,min_eq_right small,show x.val = i.val+1 from root_val i]; omega

/-- The actual half-open quotient interval for a residue lane in [lo,hi].
The high endpoint is expressed by ceiling division so empty lanes, including
residues strictly above hi, require no special case. -/
def beginLane (p a lo : ℕ) : ℕ := (lo-a) ⌈/⌉ p
def endLane (p a hi : ℕ) : ℕ := (hi+1-a) ⌈/⌉ p

theorem lane_iff {p a j lo hi : ℕ} (pos : 0 < p) :
    (lo ≤ a+p*j ∧ a+p*j ≤ hi) ↔ beginLane p a lo ≤ j ∧ j < endLane p a hi := by
  have h : ¬ (hi+1-a ≤ p*j) ↔ j < endLane p a hi := by
    rw [endLane, ← not_le, ceilDiv_le_iff_le_mul pos]
  rw [beginLane, ceilDiv_le_iff_le_mul pos, ← h]
  omega

/-- For an odd power of p, an integer in the interval passes exactly when it
has a unique generated index and quotient. This enumerates with prime stride
even if the supplied modulus is a much larger prime power. -/
theorem interval_iff {p e : ℕ} [Fact p.Prime] (odd : Odd p) (exponent : Odd e)
    (lo hi x : ℕ) :
    (lo ≤ x ∧ x ≤ hi ∧ jacobiSym (x : ℤ) (p^e) = 1) ↔
      ∃! w : Fin (p/2) × ℕ,
        beginLane p (residue p w.1) lo ≤ w.2 ∧ w.2 < endLane p (residue p w.1) hi ∧
          x = residue p w.1 + p*w.2 := by
  have sym : jacobiSym (x : ℤ) (p^e) = 1 ↔ jacobiSym (x : ℤ) p = 1 := by
    rw [jacobiSym.pow_right]
    rcases jacobiSym.trichotomy (x : ℤ) p with h|h|h <;> rw [h] <;>
      simp [exponent.pos.ne', exponent.neg_one_pow]
  rw [sym,prime_residues odd]
  have pos := (Fact.out : p.Prime).pos
  have modEq (i : Fin (p/2)) (j : ℕ) (eq : x = residue p i+p*j) : x%p = residue p i := by
    rw [eq,Nat.add_mul_mod_self_left,residue,Nat.mod_mod]
  constructor
  · rintro ⟨low,high,i,hi',unique⟩
    have eq : x = residue p i + p*(x/p) := by rw [← hi',Nat.mod_add_div]
    obtain ⟨l,h⟩ := (lane_iff pos).mp (show lo ≤ residue p i+p*(x/p) ∧ _ ≤ hi by simpa [← eq] using And.intro low high)
    refine ⟨(i,x/p),⟨l,h,eq⟩,?_⟩
    rintro ⟨k,j⟩ ⟨_,_,hkj⟩
    have ki := unique k (modEq k j hkj)
    subst k
    congr 1
    exact Nat.eq_of_mul_eq_mul_left pos (Nat.add_left_cancel (hkj.symm.trans eq))
  · rintro ⟨⟨i,j⟩,⟨l,h,eq⟩,_⟩
    obtain ⟨low,high⟩ := (lane_iff pos).mpr (And.intro l h)
    refine ⟨eq ▸ low,eq ▸ high,i,modEq i j eq,?_⟩
    intro k hk
    exact square_inj odd ((ZMod.val_injective p) (by rw [val_sq,val_sq,← hk,← modEq i j eq]))

/-- The ordinary representative of a unit, used for the half-period ordering. -/
def unitValue {d : ℕ} (u : (ZMod d)ˣ) : ℕ := (u : ZMod d).val

/-- Executable character test on the ordinary representative. -/
def unitSign {d : ℕ} (u : (ZMod d)ˣ) : ℤ := jacobiSym (unitValue u : ℤ) d

private theorem sign_eq {d : ℕ} [NeZero d] (u : (ZMod d)ˣ) :
    unitSign u = sign (u : ZMod d) := by
  rw [unitSign, ← sign_cast]
  simp [unitValue]

private theorem sign_flip {d : ℕ} [NeZero d] (hd : d%4=3) (u : (ZMod d)ˣ) :
    unitSign (-u) = -unitSign u := by
  rw [sign_eq, sign_eq]
  exact sign_neg hd _

/-- The smaller representative of the opposite pair. -/
noncomputable def lowerUnit {d : ℕ} (u : (ZMod d)ˣ) : (ZMod d)ˣ :=
  if unitValue u ≤ unitValue (-u) then u else -u

/-- Choose a Jacobi-positive representative with a single symbol evaluation. -/
noncomputable def orient {d : ℕ} (u : (ZMod d)ˣ) : (ZMod d)ˣ :=
  if unitSign u = 1 then u else -u

private theorem lower_neg {d : ℕ} [NeZero d] (u : (ZMod d)ˣ) :
    lowerUnit (-u) = lowerUnit u := by
  simp only [lowerUnit,neg_neg]
  by_cases h : unitValue u = unitValue (-u)
  · have same := Units.ext (ZMod.val_injective d h)
    rw [if_pos h.ge,if_pos h.le]
    exact same.symm
  · rcases lt_or_gt_of_ne h with lt | gt
    · simp [lt.le,not_le.mpr lt]
    · simp [gt.le,not_le.mpr gt]

private theorem lower_spec {d : ℕ} (u : (ZMod d)ˣ) :
    unitValue (lowerUnit u) ≤ unitValue (-(lowerUnit u)) := by
  unfold lowerUnit
  split_ifs with h
  · exact h
  · simpa only [neg_neg] using le_of_not_ge h

private theorem orient_positive {d : ℕ} [NeZero d] (hd : d%4=3) (u : (ZMod d)ˣ) :
    unitSign (orient u) = 1 := by
  unfold orient
  split_ifs with h
  · exact h
  · rw [sign_flip hd, sign_eq] at *
    rcases ReciprocalDivisorClasses.unit_sign u with a | a <;> omega

private theorem orient_neg {d : ℕ} [NeZero d] (hd : d%4=3) (u : (ZMod d)ˣ) :
    orient (-u) = orient u := by
  simp only [orient, neg_neg, sign_flip hd, sign_eq]
  rcases ReciprocalDivisorClasses.unit_sign u with h | h <;> simp [h]

/-- Ordinary-integer implementation of the forward reflection. -/
def reflected (d r : ℕ) : ℕ := if jacobiSym (r : ℤ) d = 1 then r else d-r

theorem orient_value {d : ℕ} [NeZero d] (hd : d%4=3) (u : (ZMod d)ˣ) :
    unitValue (orient u) = reflected d (unitValue u) := by
  haveI : Fact (1 < d) := ⟨by omega⟩
  haveI : NeZero (u : ZMod d) := ⟨u.ne_zero⟩
  unfold orient reflected unitSign
  split_ifs
  · rfl
  · exact ZMod.val_neg_of_ne_zero _

theorem lower_value {d : ℕ} [NeZero d] (hd : d%4=3) (u : (ZMod d)ˣ) :
    unitValue (lowerUnit u) = min (unitValue u) (d-unitValue u) := by
  haveI : Fact (1 < d) := ⟨by omega⟩
  haveI : NeZero (u : ZMod d) := ⟨u.ne_zero⟩
  have v : unitValue (-u) = d-unitValue u := ZMod.val_neg_of_ne_zero (u : ZMod d)
  unfold lowerUnit
  split_ifs with h
  · rw [←v,min_eq_left h]
  · rw [←v,min_eq_right (le_of_not_ge h)]

/-- For any modulus congruent to 3 modulo 4, one Jacobi evaluation converts a
unit from the lower half of the residue interval into a positive unit without
rejection. The inverse is reflection into the lower half. -/
noncomputable def reflection {d : ℕ} [NeZero d] (hd : d%4=3) :
    {u : (ZMod d)ˣ // unitValue u ≤ unitValue (-u)} ≃ {u : (ZMod d)ˣ // unitSign u = 1} where
  toFun u := ⟨orient u.val, orient_positive hd u.val⟩
  invFun u := ⟨lowerUnit u.val, lower_spec u.val⟩
  left_inv := by
    intro u
    apply Subtype.ext
    change lowerUnit (orient u.val) = u.val
    have h : lowerUnit u.val = u.val := if_pos u.property
    unfold orient
    split_ifs
    · exact h
    · rw [lower_neg,h]
  right_inv := by
    intro u
    apply Subtype.ext
    change orient (lowerUnit u.val) = u.val
    have h : orient u.val = u.val := if_pos u.property
    unfold lowerUnit
    split_ifs
    · exact h
    · rw [orient_neg hd,h]

/-- For an outer residue v coprime to m, use +1 or −1 modulo p to
make the inner Legendre sign agree with the outer Jacobi sign. -/
def twist (p m v : ℕ) := if jacobiSym (v : ℤ) m = 1 then 1 else p-1

/-- Ordinary-integer CRT evaluator using Bézout coefficients. The published
Mathlib CRT theorem below identifies its result for coprime moduli. -/
def crtValue (p m a b : ℕ) : ℕ :=
  if p=0 then a else if m=0 then b else
    let (u,v) := Nat.xgcd p m
    (((p : ℤ)*u*b + (m : ℤ)*v*a)%(p*m : ℕ)).toNat

private theorem crt_eq {p m : ℕ} (co : p.Coprime m) (a b : ℕ) :
    crtValue p m a b = (Nat.chineseRemainder co a b).val := by
  by_cases hp : p=0
  · simp [crtValue,Nat.chineseRemainder,Nat.chineseRemainder',hp]
  by_cases hm : m=0
  · simp [crtValue,Nat.chineseRemainder,Nat.chineseRemainder',hp,hm]
  simp [crtValue,Nat.chineseRemainder,Nat.chineseRemainder',hp,hm,
    co.gcd_eq_one,co.lcm_eq_mul]

/-- The two CRT coefficients depend only on the outer class. Multiplying the
second coefficient by the square residue selects the inner digit. -/
def compositeBase {p m : ℕ} (_co : p.Coprime m) (v : ℕ) : Fin (p/2) → ℕ :=
  let offset := crtValue p m 0 v
  let weight := crtValue p m (twist p m v) 0
  fun i => (offset + weight*residue p i) % (p*m)

private theorem composite_digits {p m : ℕ} (co : p.Coprime m) (v : ℕ) (i : Fin (p/2)) :
    compositeBase co v i ≡ twist p m v * residue p i [MOD p] ∧
    compositeBase co v i ≡ v [MOD m] := by
  let a := Nat.chineseRemainder co 0 v
  let b := Nat.chineseRemainder co (twist p m v) 0
  have reduce := Nat.mod_modEq (a.val+b.val*residue p i) (p*m)
  unfold compositeBase
  rw [crt_eq co 0 v,crt_eq co (twist p m v) 0]
  constructor
  · apply (reduce.of_dvd (dvd_mul_right p m)).trans
    simpa only [zero_add] using a.property.1.add (b.property.1.mul_right (residue p i))
  · apply (reduce.of_dvd (dvd_mul_left m p)).trans
    simpa only [zero_mul,add_zero] using a.property.2.add (b.property.2.mul_right (residue p i))

/-- On each unit class v modulo m, the CRT bases enumerate the positive
classes modulo p^e*m with no rejection. The true stride is p*m. Iterating v
over all units modulo m covers all positive classes, and each x fixes its v.
Prime powers inside m are allowed. -/
theorem composite_iff {p m e : ℕ} [Fact p.Prime] (three : p%4=3) (exponent : Odd e)
    (co : p.Coprime m) (mn : m ≠ 0) (v x : ℕ) (unit : v.Coprime m) (fixed : x ≡ v [MOD m]) :
    jacobiSym (x : ℤ) (p^e*m) = 1 ↔ ∃! i : Fin (p/2), x ≡ compositeBase co v i [MOD p*m] := by
  have pp := Fact.out (p := p.Prime)
  have odd : Odd p := Nat.odd_iff.mpr (by omega)
  have pred : jacobiSym ((p-1 : ℕ) : ℤ) p = -1 := by
    rw [← sign_cast, Int.cast_natCast, Nat.cast_sub pp.one_le,
      ZMod.natCast_self, Nat.cast_one, zero_sub, sign_neg three]
    have one := (sign_cast (d := p) (1 : ℤ)).trans (jacobiSym.one_left p)
    simp only [Int.cast_one] at one
    rw [one]
  have predResidue : ((p-1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub pp.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub]
  let t := twist p m v
  have vt := jacobiSym.eq_one_or_neg_one
    (show (v : ℤ).gcd m = 1 by rw [Int.gcd_natCast_natCast]; exact unit)
  have ts : jacobiSym (t : ℤ) p = jacobiSym (v : ℤ) m := by
    dsimp [t,twist]
    rcases vt with h | h <;> simp [h,jacobiSym.one_left,pred]
  have t2 : (t : ZMod p)*(t : ZMod p) = 1 := by
    dsimp [t,twist]
    split_ifs <;> simp [predResidue]
  have outer := jacobiSym.mod_left' (Int.natCast_modEq_iff.mpr fixed)
  have power : jacobiSym (x : ℤ) p ^ e = jacobiSym (x : ℤ) p := by
    rcases jacobiSym.trichotomy (x : ℤ) p with h|h|h <;>
      rw [h] <;> simp [exponent.pos.ne',exponent.neg_one_pow]
  have transformed : jacobiSym ((t*x : ℕ) : ℤ) p = jacobiSym (x : ℤ) (p^e*m) := by
    rw [Nat.cast_mul,jacobiSym.mul_left,ts,jacobiSym.mul_right' _ (pow_ne_zero _ pp.ne_zero) mn,
      jacobiSym.pow_right,outer,power,mul_comm]
  have lift (i : Fin (p/2)) : (t*x)%p = residue p i ↔ x ≡ compositeBase co v i [MOD p*m] := by
    have digits := composite_digits co v i
    have small : residue p i %p = residue p i := Nat.mod_mod _ p
    calc
      _ ↔ t*x ≡ residue p i [MOD p] := by change _ ↔ _ = residue p i%p; rw [small]
      _ ↔ (t : ZMod p)*(x : ZMod p) = (residue p i : ZMod p) := by
        rw [← ZMod.natCast_eq_natCast_iff,Nat.cast_mul]
      _ ↔ (x : ZMod p) = (t : ZMod p)*(residue p i : ZMod p) := by
        constructor <;> intro h
        · rw [←h,←mul_assoc,t2,one_mul]
        · rw [h,←mul_assoc,t2,one_mul]
      _ ↔ x ≡ t*residue p i [MOD p] := by rw [← ZMod.natCast_eq_natCast_iff,Nat.cast_mul]
      _ ↔ _ := by
        rw [← Nat.modEq_and_modEq_iff_modEq_mul co]
        exact ⟨fun h => ⟨h.trans digits.1.symm,fixed.trans digits.2.symm⟩,
          fun h => h.1.trans digits.1⟩
  rw [←transformed,prime_residues odd]
  simp only [lift]

/-- Across all outer classes, each passing integer selects the unit
representative x mod m and exactly one inner index. -/
theorem composite_complete {p m e : ℕ} [Fact p.Prime] (three : p%4=3) (exponent : Odd e)
    (co : p.Coprime m) (mn : m ≠ 0) (x : ℕ) :
    jacobiSym (x : ℤ) (p^e*m) = 1 ↔ (x%m).Coprime m ∧
      ∃! i : Fin (p/2), x ≡ compositeBase co (x%m) i [MOD p*m] := by
  have fixed := (Nat.mod_modEq x m).symm
  constructor
  · intro pass
    have uc : x.Coprime m := by
      by_contra bad
      have z := jacobiSym.eq_zero_iff.mpr ⟨mn,show (x : ℤ).gcd m ≠ 1 by
        simpa only [Int.gcd_natCast_natCast] using bad⟩
      rw [jacobiSym.mul_right' _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) mn,z,mul_zero] at pass
      contradiction
    have vunit : (x%m).Coprime m := by
      rw [Nat.Coprime,←Nat.gcd_rec,Nat.gcd_comm]
      exact uc
    exact ⟨vunit,(composite_iff three exponent co mn _ x vunit fixed).mp pass⟩
  · rintro ⟨vunit,gen⟩
    exact (composite_iff three exponent co mn _ x vunit fixed).mpr gen

/-- A modulus congruent to 3 modulo 4 always admits the distinguished
prime power required by the CRT generator. Its complementary factor is
coprime to that prime. -/
theorem exists_pivot {d : ℕ} (three : d%4=3) :
    ∃ p e m : ℕ, p.Prime ∧ p%4=3 ∧ Odd e ∧ p.Coprime m ∧ m ≠ 0 ∧ d=p^e*m := by
  have dn : d ≠ 0 := by omega
  have od : Odd d := Nat.odd_iff.mpr (by omega)
  have pick : ∃ p ∈ d.primeFactors, Odd (d.factorization p) ∧ p%4=3 := by
    by_contra! no
    have localOne (p : ℕ) (hp : p ∈ d.primeFactors) :
        (p : ZMod 4)^(d.factorization p) = 1 := by
      have pr := Nat.prime_of_mem_primeFactors hp
      have pn : p ≠ 2 := fun h => od.not_two_dvd_nat (h ▸ Nat.dvd_of_mem_primeFactors hp)
      rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp (pr.odd_of_ne_two pn)) with h | h
      · have eq : (p : ZMod 4) = 1 :=
          (ZMod.natCast_eq_natCast_iff' p 1 4).mpr (by simpa using h)
        rw [eq,one_pow]
      · have eq : (p : ZMod 4) = -1 := calc
          (p : ZMod 4) = (3 : ℕ) :=
            (ZMod.natCast_eq_natCast_iff' p 3 4).mpr (by simpa using h)
          _ = -1 := by decide
        rw [eq]
        exact (Nat.not_odd_iff_even.mp (fun he => no p hp he h)).neg_one_pow
    have prod : ∏ p ∈ d.primeFactors, (p : ZMod 4)^(d.factorization p) = 1 :=
      Finset.prod_eq_one localOne
    have natProduct : ∏ p ∈ d.primeFactors, p^(d.factorization p) = d :=
      Nat.factorization_prod_pow_eq_self dn
    have copy := congrArg (Nat.cast : ℕ → ZMod 4) natProduct
    push_cast at copy
    rw [prod] at copy
    have h := (ZMod.natCast_eq_natCast_iff' 1 d 4).mp copy
    omega
  obtain ⟨p,hp,he,p3⟩ := pick
  have pr := Nat.prime_of_mem_primeFactors hp
  exact ⟨p,d.factorization p,d/p^(d.factorization p),pr,p3,he,Nat.coprime_ordCompl pr dn,
    (Nat.ordCompl_pos p dn).ne',(Nat.ordProj_mul_ordCompl_eq_self d p).symm⟩

/-- Every eligible actual odd divisor for a witnessed prime-power
discriminant occurs at exactly one of the generated interval positions. -/
theorem divisor_lanes {p e N f lo hi : ℕ} [Fact p.Prime] (odd : Odd p) (exponent : Odd e)
    (three : p^e%4=3) (fodd : Odd f) (dvd : f ∣ N) (co : N.Coprime (p^e))
    {a : ℤ} (anchor : (N : ℤ) ∣ a^2 + (p^e : ℕ)) (low : lo ≤ f) (high : f ≤ hi) :
    ∃! w : Fin (p/2) × ℕ,
      beginLane p (residue p w.1) lo ≤ w.2 ∧ w.2 < endLane p (residue p w.1) hi ∧
        f = residue p w.1 + p*w.2 :=
  (interval_iff odd exponent lo hi f).mp
    ⟨low,high,ReciprocalDivisorClasses.divisor_of_witness three fodd dvd co anchor⟩

/-- Modulo 7^3·13 the unit class 2 modulo 13 generates three classes
with effective stride 91. -/
theorem example_4459 :
    let emit := compositeBase (by decide : Nat.Coprime 7 13) 2
    emit 0 = 41 ∧ emit 1 = 80 ∧ emit 2 = 54 := by
  let co : Nat.Coprime 7 13 := by decide
  have t : twist 7 13 2 = 6 := by norm_num [twist]
  have unique (i : Fin (7/2)) (x : ℕ) (small : x < 91)
      (left : x ≡ 6*residue 7 i [MOD 7]) (right : x ≡ 2 [MOD 13]) :
      compositeBase co 2 i = x := by
    obtain ⟨a,b⟩ := composite_digits co 2 i
    have h := (Nat.modEq_and_modEq_iff_modEq_mul co).mp
      ⟨a.trans (t ▸ left.symm),b.trans right.symm⟩
    change (compositeBase co 2 i)%91 = x%91 at h
    rwa [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt (show compositeBase co 2 i < 91 from
      Nat.mod_lt _ (by decide))] at h
  exact ⟨unique 0 41 (by decide) (by decide) (by decide),
    unique 1 80 (by decide) (by decide) (by decide),unique 2 54 (by decide) (by decide) (by decide)⟩

end PrimeFactors.GeneratingDivisorSigns
