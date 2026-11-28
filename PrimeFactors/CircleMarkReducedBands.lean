import PrimeFactors.CircleMarkCofactorBands

/-! Band checks after removing a known divisor of a squared remainder that
is coprime to the public modulus. -/
namespace PrimeFactors.CircleMarkReducedBands

open Finset CircleBranchCount CircleMarkCofactorBands
open private PrimeFactors.CircleMarkCofactorBands.nonunit from PrimeFactors.CircleMarkCofactorBands

/-- Removing a divisor known to be coprime to the modulus preserves the
exact gcd, including its value at a successful coordinate. -/
theorem gcd_preserved {n y c : ℕ} (dvd : c∣y) (unit : n.Coprime c) :
    n.gcd y=n.gcd (y/c) := by
  simpa only [Nat.mul_div_cancel' dvd] using unit.symm.gcd_mul_left_cancel_right (y/c)

/-- A positive multiple of a remainder admitted by the band is admitted too. -/
theorem inBands_mul {P H z c : ℕ} (pos : 0<c) (admitted : inBands P H z) :
    inBands P H (c*z) := by
  obtain ⟨k,kp,lo,hi⟩ := admitted
  refine ⟨c*k,Nat.mul_pos pos kp,?_,?_⟩
  · simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left c lo
  · simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left c hi

theorem refines {P H y c : ℕ} (pos : 0<c) (dvd : c∣y) (admitted : inBands P H (y/c)) :
    inBands P H y := by
  simpa only [Nat.mul_div_cancel' dvd] using inBands_mul pos admitted

/-- The finite inequality for the interval condition. Zero remainders
and zero quotients fail this test. -/
noncomputable def candidates (xs : Finset ℕ) (P H a : ℕ) (remove : ℕ→ℕ) : Finset ℕ :=
  xs.filter fun x =>
    let z := (x^2-a)/remove x
    0<z ∧ z≤(z/P)*H

private theorem mem_candidates {xs : Finset ℕ} {P H a x : ℕ} {c : ℕ→ℕ} (pos : 0<P) :
    x∈candidates xs P H a c ↔ x∈xs ∧ 0<(x^2-a)/c x ∧ inBands P H ((x^2-a)/c x) := by
  simp only [candidates,mem_filter]
  apply and_congr_right
  intro _
  exact and_congr_right fun zp => (inBands_iff pos zp).symm

/-- Testing only the reduced band keeps a subset of the ordinary band's
candidates. This inclusion requires no factorization or coprimality premise. -/
theorem candidates_subset (xs : Finset ℕ) (a H : ℕ) {P : ℕ} (pos : 0<P) (c : ℕ→ℕ)
    (div : ∀ x∈xs, 0<c x ∧ c x∣x^2-a) :
    candidates xs P H a c ⊆ candidates xs P H a (fun _ => 1) := by
  intro x hx
  obtain ⟨mem,zp,pass⟩ := (mem_candidates pos).mp hx
  obtain ⟨cp,dvd⟩ := div x mem
  apply (mem_candidates pos).mpr
  simp only [Nat.div_one]
  have yp : 0<x^2-a := (Nat.lt_of_lt_of_le zp (Nat.div_le_self ..))
  exact ⟨mem,yp,refines cp dvd pass⟩

/-- Filtering an arbitrary finite coordinate set using the reduced band and
its gcd reproduces exactly the original modular marks. In an ordered scan the
first successful coordinate and the factor read at that coordinate are preserved. -/
theorem hits_preserved {p q P H a : ℕ} [Fact p.Prime] [Fact q.Prime] (xs : Finset ℕ)
    (pl : P≤p) (ql : P≤q) (pu : p≤H) (qu : q≤H) (small : a<P)
    (neg : jacobiSym a (p*q)= -1) (c : ℕ→ℕ)
    (div : ∀ x∈xs, 0<c x ∧ c x∣x^2-a ∧ (p*q).Coprime (c x)) :
    (candidates xs P H a c).filter (fun x => (p*q).gcd ((x^2-a)/c x)≠1) =
    xs.filter (fun x : ℕ => (x:ZMod (p*q))∈marked (p*q) a) := by
  have pos : 0<P := by omega
  ext x
  simp only [mem_filter,mem_candidates pos]
  constructor
  · rintro ⟨⟨mem,zp,_⟩,hit⟩
    obtain ⟨_,dvd,unit⟩ := div x mem
    have yp := zp.trans_le (Nat.div_le_self ..)
    have form : x^2=a+(x^2-a) := by omega
    exact ⟨mem,(PrimeFactors.CircleMarkCofactorBands.nonunit form).mpr
      (by simpa only [Nat.Coprime,gcd_preserved dvd unit] using hit)⟩
  · rintro ⟨mem,hit⟩
    obtain ⟨cp,dvd,unit⟩ := div x mem
    have above := positive_of_marked neg pl ql small hit
    have yp : 0<x^2-a := by omega
    have zp := Nat.div_pos (Nat.le_of_dvd yp dvd) cp
    have form : x^2=a+c x*((x^2-a)/c x) := by rw [Nat.mul_div_cancel' dvd]; omega
    have cop := (PrimeFactors.CircleMarkCofactorBands.nonunit form).mp hit
    rw [Nat.coprime_mul_iff_right,and_iff_right unit] at cop
    exact ⟨⟨mem,zp,reduced pl ql pu qu unit zp form hit⟩,cop⟩

/-- The full power of two dividing a remainder is a valid choice in the
finite search whenever the modulus is odd. This also covers the zero
remainder, where the natural factorization gives the multiplier one. -/
theorem two_power_valid {n : ℕ} (odd : Odd n) (y : ℕ) :
    let c := 2^(y.factorization 2)
    0<c ∧ c∣y ∧ n.Coprime c := by
  exact ⟨pow_pos (by decide) _,Nat.ordProj_dvd y 2,odd.coprime_two_right.pow_right _⟩

/-- In this seven-bit control, dividing even remainders by two removes two
additional gcd tests. Both scans first encounter a factor at coordinate 21. -/
theorem control :
    let n := 8249
    let xs := Icc 1 21
    let half := fun x : ℕ => if 2∣x^2-3 then 2 else 1
    n=73*113 ∧ n/128+1=65 ∧ jacobiSym 3 n= -1 ∧
    candidates xs 65 127 3 (fun _ => 1)=Icc 9 21 ∧
    candidates xs 65 127 3 half=(Icc 9 21) \ {9,11} ∧
    (candidates xs 65 127 3 half).filter (fun x => n.gcd ((x^2-3)/half x)≠1)={21} ∧
    xs.filter (fun x : ℕ => (x:ZMod 8249)∈marked 8249 3)={21} ∧
    n.gcd (21^2-3)=73 ∧ n.gcd ((21^2-3)/2)=73 := by
  dsimp only
  letI : Fact (Nat.Prime 73) := ⟨by decide⟩
  letI : Fact (Nat.Prime 113) := ⟨by decide⟩
  have neg : jacobiSym 3 (73*113)= -1 := by norm_num
  let halve := fun x : ℕ => if 2∣x^2-3 then 2 else 1
  have valid (x : ℕ) : 0<halve x ∧ halve x∣x^2-3 ∧ (73*113).Coprime (halve x) := by
    dsimp only [halve]
    split_ifs with dv
    · exact ⟨by decide,dv,by decide⟩
    · exact ⟨by decide,one_dvd _,Nat.coprime_one_right _⟩
  have all := hits_preserved (Icc 1 21) (p:=73) (q:=113) (a:=3)
    (by decide : 65≤73) (by decide) (by decide : 73≤127) (by decide)
    (by decide) neg halve (fun x _ => valid x)
  refine ⟨by decide,by decide,neg,by decide,by decide,by decide,?_,by decide,by decide⟩
  exact all.symm.trans (by decide)

end PrimeFactors.CircleMarkReducedBands
