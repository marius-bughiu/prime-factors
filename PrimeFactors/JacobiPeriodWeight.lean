import PrimeFactors.JacobiTwoMomentPeriod

/-! A single weighted character sum detects a proposed even-moment period.
The prime 13 has one additional zero in a period. -/

namespace PrimeFactors.JacobiPeriodWeight

open JacobiMomentPeriod JacobiMomentRecurrence JacobiMomentZeros JacobiTwoMomentPeriod
  ProjectiveWordMoments
open private PrimeFactors.ProjectiveWordMoments.signed_boundary from PrimeFactors.ProjectiveWordMoments

/-- The half-degree just before the boundary has value (-1)^((p−1)/2)/8. -/
theorem penultimate {p j : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (edge : 2*(j+1)+1=p) :
    8*halfMoment p j = (-1 : ZMod p)^(j+1) := by
  have pred : p-1=2*(j+1) := by omega
  have half : (p-1)/2=j+1 := by omega
  have boundary := value_at_multiple (p:=p) (k:=p-1) (by omega) (by omega) dvd_rfl
  unfold component at boundary
  rw [PrimeFactors.ProjectiveWordMoments.signed_boundary (by omega), half] at boundary
  have central_eq : central (p-1) = (j+1).centralBinom := by
    rw [pred,central,if_pos (by omega),Nat.mul_div_cancel_left _ (by decide : 0<2)]
    rfl
  rw [central_eq] at boundary
  have last : ((j+1).centralBinom : ZMod p) = (-1 : ZMod p)^(j+1) := by linear_combination boundary
  have recu := congrArg (fun n : ℕ => (n : ZMod p)) (Nat.succ_mul_centralBinom_succ j)
  push_cast at recu
  rw [last] at recu
  have index : 2*(j : ZMod p)+3=0 := by
    calc
      _ = ((2*j+3 : ℕ) : ZMod p) := by push_cast; ring
      _ = 0 := by rw [show 2*j+3=p by omega, ZMod.natCast_self]
  rw [interior_value hp (by omega) (by omega)]
  linear_combination 2*recu - ((-1 : ZMod p)^(j+1)-4*(j.centralBinom : ZMod p))*index

private noncomputable def localWeight (p : ℕ) [Fact p.Prime] (d : ℕ) : ZMod p :=
  localEven p (d+1) - 3*localEven p d

private theorem small_ne_zero {p k : ℕ} (positive : 0<k) (small : k<p) : (k : ZMod p) ≠ 0 := by
  rw [ne_eq,ZMod.natCast_zmod_eq_zero_iff_dvd]
  exact Nat.not_dvd_of_pos_of_lt positive small

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

private theorem exception : localWeight 13 4=0 := by
  unfold localWeight localEven
  rw [value_at_multiple (by decide) (by decide) (by decide),at_remainder (by decide) (by decide) (by decide)]
  decide +kernel

/-- All local zeros of the difference of consecutive moments with weight three. -/
theorem local_weight_zero_iff {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (d : ℕ) :
    localEven p (d+1) - 3*localEven p d=0 ↔ localPeriod p ∣ d ∨ (p=13 ∧ d%6=4) := by
  change localWeight p d=0 ↔ _
  let a := (p-1)/2
  let r := d%a
  have period : localPeriod p=a := if_neg (by omega)
  have ra : r<a := Nat.mod_lt _ (show 0<a by dsimp [a]; omega)
  obtain ⟨k,hk⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have pred : p-1=2*a := by dsimp [a]; omega
  have cyc := (JacobiMomentPeriod.local_iff (p:=p) (by omega) a).mpr (period ▸ dvd_rfl)
  have weighted : Function.Periodic (localWeight p) a := by
    intro i
    change localEven p (i+a+1)-3*localEven p (i+a)=_
    rw [Nat.add_right_comm i a 1,cyc (i+1),cyc i]
    rfl
  have values := (local_pair hp 0).mp (dvd_zero _)
  have zero : localWeight p 0=0 := by
    unfold localWeight
    rw [values.1,values.2]
    ring
  rw [←weighted.map_mod_nat d]
  change localWeight p r=0 ↔ _
  constructor
  · intro h
    by_cases interior : r+2<a
    · have recu := interior_recurrence (j:=r+1) hp (by omega) interior
      have nz := interior_ne_zero (j:=r+1) hp (by omega) (by omega)
      change halfMoment p (r+1+1) - 3*halfMoment p (r+1)=0 at h
      have product : (((r+1 : ℕ) : ZMod p)-1)*halfMoment p (r+1)=0 := by
        linear_combination ((((r+1 : ℕ) : ZMod p)+1)*h - recu)
      have index := sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_right nz)
      have cast : ((r+1 : ℕ) : ZMod p)=(1 : ℕ) := by simpa only [Nat.cast_one] using index
      have one := (ZMod.natCast_eq_natCast_iff' _ _ p).mp cast
      rw [Nat.mod_eq_of_lt (show r+1<p by omega),Nat.mod_eq_of_lt (show 1<p by omega)] at one
      exact Or.inl (period ▸ Nat.dvd_of_mod_eq_zero (show r=0 by omega))
    have edgeVal : halfMoment p a = 1+(-1 : ZMod p)^a := by
      rw [halfMoment,←pred,value_at_multiple (by omega) (by omega) dvd_rfl]
    rcases (show r+1=a ∨ r+2=a by omega) with wrap | edge
    · unfold localWeight at h
      rw [wrap,show a=0+a by omega,cyc 0,values.1] at h
      change 2-3*halfMoment p (r+1)=0 at h
      rw [wrap,edgeVal] at h
      rcases neg_one_pow_eq_or (ZMod p) a with sign | sign
      · rw [sign] at h
        exact False.elim ((small_ne_zero (p:=p) (k:=4) (by decide) (by omega)) (by push_cast; linear_combination -h))
      · rw [sign] at h
        exact False.elim ((small_ne_zero (p:=p) (k:=2) (by decide) (by omega)) (by push_cast; linear_combination h))
    · have prev := penultimate (j:=r+1) hp (by omega)
      change halfMoment p (r+1+1)-3*halfMoment p (r+1)=0 at h
      rw [show r+1+1=a by omega,edgeVal] at h
      rw [show r+1+1=a by omega] at prev
      rcases neg_one_pow_eq_or (ZMod p) a with sign | sign
      · rw [sign] at h prev
        have thirteen : (13 : ZMod p)=0 := by linear_combination 8*h + 3*prev
        have dvd : p∣13 := (ZMod.natCast_zmod_eq_zero_iff_dvd 13 p).mp (by exact_mod_cast thirteen)
        have eq := ((Nat.dvd_prime (by decide : Nat.Prime 13)).mp dvd).resolve_left (by omega)
        exact Or.inr ⟨eq,by simpa [r,a,eq] using (show r=4 by dsimp [a] at *; omega)⟩
      · rw [sign] at h prev
        exact False.elim ((small_ne_zero (p:=p) (k:=3) (by decide) (by omega)) (by push_cast; linear_combination 8*h + 3*prev))
  · rintro (dv | ⟨eq,hr⟩)
    · rw [period] at dv
      exact (show r=0 from Nat.mod_eq_zero_of_dvd dv) ▸ zero
    · have hr' : r=4 := by simpa only [r,a,eq,show (13-1)/2=6 by decide] using hr
      rw [hr']
      clear hk
      subst p
      exact exception

/-- The two consecutive complete moments combined with constant weight three. -/
noncomputable def weight (n d : ℕ) [NeZero n] : ZMod n :=
  completeEven n (d+1) - 3*completeEven n d

/-- One pass over the residues evaluates the weighted moment. -/
theorem weight_eq_sum (n d : ℕ) [NeZero n] :
    weight n d = ∑ x : ZMod n, x^(2*(d+1))*(x^2-3)*
      ((jacobiSym ((x.val:ℤ)^2-4) n : ℤ) : ZMod n) := by
  simp only [weight,completeEven,moment,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [show 2*(d+1+1)=2*(d+1)+2 by omega,pow_add]
  ring

private theorem coordinates {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 7 ≤ p) (hq : 7 ≤ q) (d : ℕ) :
    ZMod.chineseRemainder cop (weight (p*q) d) = (localWeight p d, localWeight q d) := by
  simp only [weight,completeEven,map_sub,map_mul,map_ofNat,components cop (by omega) (by omega)]
  rfl

/-- Unless one of the factors is 13, the vanishing of one weighted character
sum is equivalent to the shift repeating every positive even moment. -/
theorem weight_zero_iff_periodic {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 7 ≤ p) (hq : 7 ≤ q) (p13 : p ≠ 13) (q13 : q ≠ 13) (d : ℕ) :
    weight (p*q) d=0 ↔ Function.Periodic (completeEven (p*q)) d := by
  rw [←(ZMod.chineseRemainder cop).injective.eq_iff,coordinates cop hp hq,map_zero,Prod.ext_iff]
  change (_ - _ = 0 ∧ _ - _ = 0) ↔ _
  simp only [local_weight_zero_iff hp,local_weight_zero_iff hq,p13,q13,false_and,or_false,
    composite_iff cop (by omega) (by omega),Nat.lcm_dvd_iff]

private theorem prime_gcd_iff (v l : ℕ) [Fact l.Prime] (P : Prop) [Decidable P]
    (dv : l ∣ v ↔ P) : v.gcd l = if P then l else 1 := by
  split_ifs with h
  · exact Nat.gcd_eq_right (dv.mpr h)
  · exact ((Fact.out : l.Prime).coprime_iff_not_dvd.mpr (fun a => h (dv.mp a))).symm.gcd_eq_one

/-- A gcd records each local period independently, including the extra
zero class at 13. -/
theorem weight_gcd {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 7 ≤ p) (hq : 7 ≤ q) (d : ℕ) :
    (p*q).gcd (weight (p*q) d).val =
      (if localPeriod p ∣ d ∨ (p=13 ∧ d%6=4) then p else 1) *
      (if localPeriod q ∣ d ∨ (q=13 ∧ d%6=4) then q else 1) := by
  let w := weight (p*q) d
  have coords : ((w.val : ZMod p),(w.val : ZMod q)) = (localWeight p d,localWeight q d) := calc
    _ = ZMod.chineseRemainder cop (w.val : ZMod (p*q)) := by rw [map_natCast]; rfl
    _ = _ := by rw [ZMod.natCast_zmod_val, coordinates cop hp hq]
  have prime_gcd (l : ℕ) [Fact l.Prime] (hl : 7 ≤ l)
      (coord : (w.val : ZMod l)=localWeight l d) :
      w.val.gcd l = if localPeriod l ∣ d ∨ (l=13 ∧ d%6=4) then l else 1 := by
    have dv : l ∣ w.val ↔ localPeriod l ∣ d ∨ (l=13 ∧ d%6=4) := by
      rw [← ZMod.natCast_zmod_eq_zero_iff_dvd,coord,localWeight,local_weight_zero_iff hl]
    exact prime_gcd_iff _ _ _ dv
  change (p*q).gcd w.val = _
  rw [Nat.gcd_comm,cop.gcd_mul,prime_gcd p hp (congrArg Prod.fst coords),
    prime_gcd q hq (congrArg Prod.snd coords)]

private theorem sign19 : (-1 : ZMod 19)^(9 : ℕ) ≠ 1 := by decide

private theorem nonzero38_of_even_sign {p : ℕ} [Fact p.Prime] (hp : 11 ≤ p)
    (sign : (-1 : ZMod p)^((p-1)/2)=1) : (38 : ZMod p) ≠ 0 := by
  intro zero
  have two := small_ne_zero (p:=p) (k:=2) (by decide) (by omega)
  have product : (2 : ZMod p)*19=0 := by linear_combination zero
  have nineteen := (mul_eq_zero.mp product).resolve_left (by simpa only [Nat.cast_ofNat] using two)
  have dvd : p∣19 := (ZMod.natCast_zmod_eq_zero_iff_dvd 19 p).mp (by simpa only [Nat.cast_ofNat] using nineteen)
  have eq := ((Nat.dvd_prime (by decide : Nat.Prime 19)).mp dvd).resolve_left (by omega)
  subst p
  exact sign19 sign

private noncomputable def localAnchor (p : ℕ) [Fact p.Prime] (u : ℕ) : ZMod p :=
  3*localEven p (u+1) - 10*localEven p u

/-- With the second starting pair 6,20, the coefficient ratio 10/3 has
no boundary aliases at primes at least eleven. -/
theorem second_local_zero_iff {p : ℕ} [Fact p.Prime] (hp : 11 ≤ p) (d : ℕ) :
    3*localEven p (d+2) - 10*localEven p (d+1)=0 ↔ localPeriod p ∣ d := by
  let a := (p-1)/2
  let r := (d+1)%a
  have ha : 5≤a := by dsimp only [a]; omega
  have period : localPeriod p=a := if_neg (by omega)
  have ra : r<a := Nat.mod_lt _ (by omega)
  obtain ⟨k,hk⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have pred : p-1=2*a := by dsimp only [a]; omega
  have cyc := (JacobiMomentPeriod.local_iff (p:=p) (by omega) a).mpr (period ▸ dvd_rfl)
  have anchorCyc : Function.Periodic (localAnchor p) a := by
    intro i
    change 3*localEven p (i+a+1)-10*localEven p (i+a)=_
    rw [Nat.add_right_comm i a 1,cyc (i+1),cyc i]
    rfl
  have congr : r=1 ↔ localPeriod p ∣ d := by
    rw [period,←Nat.modEq_zero_iff_dvd]
    have one : (0+1)%a=1 := Nat.mod_eq_of_lt (by omega)
    constructor
    · intro h
      apply Nat.ModEq.add_right_cancel' 1
      change r=(0+1)%a
      rwa [one]
    · intro h
      have hh := h.add_right 1
      change r=(0+1)%a at hh
      rwa [one] at hh
  have initial := (local_pair (by omega : 7≤p) 0).mp (dvd_zero _)
  have third : localEven p 2=20 := by
    simpa only [show Nat.centralBinom 3=20 by decide,Nat.cast_ofNat] using
      interior_value (j:=3) (by omega : 7≤p) (by decide) (by omega)
  have correct : localAnchor p 1=0 := by
    unfold localAnchor
    rw [third,initial.2]
    ring
  change localAnchor p (d+1)=0 ↔ _
  rw [← anchorCyc.map_mod_nat (d+1), ←congr]
  change localAnchor p r=0 ↔ r=1
  constructor
  · intro h
    by_cases interior : r+2<a
    · have recu := interior_recurrence (j:=r+1) (by omega : 7≤p) (by omega) interior
      have nz := interior_ne_zero (j:=r+1) (by omega : 7≤p) (by omega) (by omega)
      change 3*halfMoment p (r+1+1) - 10*halfMoment p (r+1)=0 at h
      have product : (2 : ZMod p)*((((r+1 : ℕ) : ZMod p)-2)*halfMoment p (r+1))=0 := by
        linear_combination ((((r+1 : ℕ) : ZMod p)+1)*h - 3*recu)
      have two := small_ne_zero (p:=p) (k:=2) (by decide) (by omega)
      have van := (mul_eq_zero.mp product).resolve_left (by simpa only [Nat.cast_ofNat] using two)
      have index := sub_eq_zero.mp ((mul_eq_zero.mp van).resolve_right nz)
      have cast : ((r+1 : ℕ) : ZMod p)=(2 : ℕ) := by simpa only [Nat.cast_ofNat] using index
      have eq := (ZMod.natCast_eq_natCast_iff' _ _ p).mp cast
      rw [Nat.mod_eq_of_lt (show r+1<p by omega),Nat.mod_eq_of_lt (show 2<p by omega)] at eq
      omega
    have edgeVal : halfMoment p a = 1+(-1 : ZMod p)^a := by
      rw [halfMoment,←pred,value_at_multiple (by omega) (by omega) dvd_rfl]
    rcases (show r+1=a ∨ r+2=a by omega) with wrap | edge
    · unfold localAnchor at h
      rw [wrap,show a=0+a by omega,cyc 0,initial.1] at h
      change 3*2-10*halfMoment p (r+1)=0 at h
      rw [wrap,edgeVal] at h
      rcases neg_one_pow_eq_or (ZMod p) a with sign | sign
      · rw [sign] at h
        have two := small_ne_zero (p:=p) (k:=2) (by decide) (by omega)
        have seven := small_ne_zero (p:=p) (k:=7) (by decide) (by omega)
        exact False.elim ((mul_ne_zero two seven) (by push_cast; linear_combination -h))
      · rw [sign] at h
        exact False.elim ((small_ne_zero (p:=p) (k:=6) (by decide) (by omega)) (by push_cast; linear_combination h))
    · have prev := penultimate (j:=r+1) (by omega : 7≤p) (by omega)
      change 3*halfMoment p (r+1+1)-10*halfMoment p (r+1)=0 at h
      rw [show r+1+1=a by omega,edgeVal] at h
      rw [show r+1+1=a by omega] at prev
      rcases neg_one_pow_eq_or (ZMod p) a with sign | sign
      · rw [sign] at h prev
        exact False.elim ((nonzero38_of_even_sign hp sign) (by linear_combination 8*h+10*prev))
      · rw [sign] at h prev
        exact False.elim ((small_ne_zero (p:=p) (k:=10) (by decide) (by omega)) (by push_cast; linear_combination 8*h+10*prev))
  · intro atOne
    rwa [atOne]

/-- One public weighted reading with coefficients 3 and 10. -/
noncomputable def secondWeight (n d : ℕ) [NeZero n] : ZMod n :=
  3*completeEven n (d+2) - 10*completeEven n (d+1)

theorem secondWeight_eq_sum (n d : ℕ) [NeZero n] :
    secondWeight n d = ∑ x : ZMod n, x^(2*(d+2))*(3*x^2-10)*
      ((jacobiSym ((x.val:ℤ)^2-4) n : ℤ) : ZMod n) := by
  simp only [secondWeight,completeEven,moment,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [show 2*(d+2+1)=2*(d+2)+2 by omega,pow_add]
  ring

private theorem second_coords {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 11 ≤ p) (hq : 11 ≤ q) (d : ℕ) :
    ZMod.chineseRemainder cop (secondWeight (p*q) d) =
      (localAnchor p (d+1),localAnchor q (d+1)) := by
  simp only [secondWeight,completeEven,map_sub,map_mul,map_ofNat,components cop (by omega) (by omega)]
  rfl

/-- For two distinct primes at least eleven, the single weighted reading
vanishes exactly at common periods, including when 13 divides the modulus. -/
theorem secondWeight_zero_iff_periodic {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 11 ≤ p) (hq : 11 ≤ q) (d : ℕ) :
    secondWeight (p*q) d=0 ↔ Function.Periodic (completeEven (p*q)) d := by
  rw [←(ZMod.chineseRemainder cop).injective.eq_iff,second_coords cop hp hq,map_zero,Prod.ext_iff]
  change (_-_ = 0 ∧ _-_ = 0) ↔ _
  rw [second_local_zero_iff hp,second_local_zero_iff hq,composite_iff cop (by omega) (by omega),Nat.lcm_dvd_iff]

/-- The second weighted sum distinguishes a period of either individual prime
from a shared period, with no exceptional classes. -/
theorem secondWeight_gcd {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (hp : 11 ≤ p) (hq : 11 ≤ q) (d : ℕ) :
    (p*q).gcd (secondWeight (p*q) d).val =
      (if localPeriod p ∣ d then p else 1) * (if localPeriod q ∣ d then q else 1) := by
  let w := secondWeight (p*q) d
  have coords : ((w.val : ZMod p),(w.val : ZMod q)) = (localAnchor p (d+1),localAnchor q (d+1)) := calc
    _ = ZMod.chineseRemainder cop (w.val : ZMod (p*q)) := by rw [map_natCast]; rfl
    _ = _ := by rw [ZMod.natCast_zmod_val, second_coords cop hp hq]
  have dv (l : ℕ) [Fact l.Prime] (hl : 11 ≤ l) (coord : (w.val : ZMod l)=localAnchor l (d+1)) :
      l ∣ w.val ↔ localPeriod l ∣ d := by
    rw [← ZMod.natCast_zmod_eq_zero_iff_dvd,coord]
    exact second_local_zero_iff hl d
  change (p*q).gcd w.val = _
  rw [Nat.gcd_comm,cop.gcd_mul,prime_gcd_iff _ _ _ (dv p hp (congrArg Prod.fst coords)),
    prime_gcd_iff _ _ _ (dv q hq (congrArg Prod.snd coords))]

end PrimeFactors.JacobiPeriodWeight
