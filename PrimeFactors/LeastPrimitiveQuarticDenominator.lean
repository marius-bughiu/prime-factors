import PrimeFactors.BalancedQuarticLocalExample
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-! Prime support and the first possible balanced denominator of a supplied
primitive rational point on x⁴+4y⁴=N. -/
namespace PrimeFactors.LeastPrimitiveQuarticDenominator

private theorem even_table : ∀ a b : Fin 16, (a.val^4+4*b.val^4)%16=0 →
    a.val%2=0 ∧ b.val%2=0 := by decide +kernel

/-- With coprime numerator coordinates a common denominator must be odd. -/
theorem two_not_dvd {n a b d : ℕ} (prim : a.Coprime b) (repr : d^4*n=a^4+4*b^4) : ¬2∣d := by
  intro even
  have divides : 16 ∣ a^4+4*b^4 := repr ▸ dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd even 4) n
  have reduce : (a%16)^4+4*(b%16)^4 ≡ a^4+4*b^4 [MOD 16] :=
    ((Nat.mod_modEq a 16).pow 4).add (((Nat.mod_modEq b 16).pow 4).mul_left 4)
  have parity := even_table ⟨a%16,Nat.mod_lt _ (by decide)⟩ ⟨b%16,Nat.mod_lt _ (by decide)⟩
    (Eq.trans reduce (Nat.mod_eq_zero_of_dvd divides))
  have pa : 2∣a := Nat.dvd_of_mod_eq_zero (by have := parity.1; dsimp at this; omega)
  have pb : 2∣b := Nat.dvd_of_mod_eq_zero (by have := parity.2; dsimp at this; omega)
  exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨2,Nat.prime_two,pa,pb⟩) prim

/-- Every denominator prime splits in the Gaussian integers. No parity
hypothesis on N is needed. -/
theorem prime_support {n a b d : ℕ} (prim : a.Coprime b) (repr : d^4*n=a^4+4*b^4)
    {p : ℕ} (prime : p.Prime) (dvd : p∣d) : p%4=1 := by
  letI : Fact p.Prime := ⟨prime⟩
  have odd : p≠2 := by rintro rfl; exact two_not_dvd prim repr dvd
  have shape : (d:ZMod p)^4*n=(a:ZMod p)^4+4*(b:ZMod p)^4 := by
    exact_mod_cast congrArg (fun k : ℕ => (k:ZMod p)) repr
  have d0 : (d : ZMod p)=0 := (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mpr dvd
  rw [d0,zero_pow (by decide),zero_mul] at shape
  have b0 : (b:ZMod p)≠0 := by
    intro zero
    have a0 : (a:ZMod p)=0 := by simpa [zero] using shape.symm
    exact (Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨p,prime,(ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp a0,(ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp zero⟩) prim
  have t0 : (2:ZMod p)≠0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  have neg : ((a:ZMod p)^2)^2 = -(2*(b:ZMod p)^2)^2 := by linear_combination -shape
  have three := ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (mul_ne_zero t0 (pow_ne_zero _ b0)) neg
  have parity := prime.eq_two_or_odd.resolve_left odd
  omega

private abbrev Clean (n : ℕ) : Prop := ¬2∣n ∧ ¬3∣n ∧ ¬7∣n ∧ ¬11∣n

set_option synthInstance.maxSize 500 in
set_option maxRecDepth 4096 in
private theorem small_split : ∀ u v : Fin 30, 1<u.val*v.val → u.val.Coprime v.val →
    u.val^4≤12*v.val^4 → v.val^4≤12*u.val^4 → Clean (u.val*v.val) → 221≤u.val*v.val := by
  unfold Clean
  decide +kernel

private theorem small_coordinate {u v : ℕ} (size : u*v<221) (ratio : u^4≤12*v^4) : u<30 := by
  by_contra! big
  have other : v≤7 := by
    by_contra! large
    have := Nat.mul_le_mul big (show 8≤v by omega)
    omega
  have := Nat.pow_le_pow_left big 4
  have := Nat.pow_le_pow_left other 4
  omega

/-- Four excluded primes already suffice for this denominator threshold. -/
theorem least_of_four_exclusions {d u v : ℕ} (nontrivial : 1<d) (split : d=u*v) (cop : u.Coprime v)
    (two : ¬2∣d) (three : ¬3∣d) (seven : ¬7∣d) (eleven : ¬11∣d)
    (uv : u^4≤12*v^4) (vu : v^4≤12*u^4) : 221≤d := by
  subst d
  by_contra! small
  exact (not_le_of_gt small) (small_split ⟨u,small_coordinate small uv⟩
    ⟨v,small_coordinate (by simpa only [Nat.mul_comm v u] using small) vu⟩ nontrivial cop uv vu
    ⟨two,three,seven,eleven⟩)

/-- The abstract denominator bound assumes only its coprime split, its prime
support, and the two fourth-power comparisons. -/
theorem least {d u v : ℕ} (nontrivial : 1<d) (split : d=u*v) (cop : u.Coprime v)
    (support : ∀ p, p.Prime → p∣d → p%4=1)
    (uv : u^4≤12*v^4) (vu : v^4≤12*u^4) : 221≤d := by
  apply least_of_four_exclusions nontrivial split cop _ _ _ _ uv vu
  · intro dvd; have := support 2 (by decide) dvd; omega
  · intro dvd; have := support 3 (by decide) dvd; omega
  · intro dvd; have := support 7 (by decide) dvd; omega
  · intro dvd; have := support 11 (by decide) dvd; omega

/-- The smallest denominator is attained on a 48-bit semiprime with two
24-bit prime factors. The same supplied point is checked in the local example. -/
theorem example_attained :
    let n := BalancedQuarticLocalExample.N
    let p := BalancedQuarticLocalExample.p
    let q := BalancedQuarticLocalExample.q
    (221:ℕ)=13*17 ∧ Nat.Coprime 13 17 ∧ Nat.Coprime 318065 552963 ∧
    221^4*n=318065^4+4*552963^4 ∧ n=p*q ∧ p.Prime ∧ q.Prime ∧ p<q ∧ q<2*p ∧
    2^23≤p ∧ q<2^24 ∧ 2^47≤n ∧ n<2^48 ∧ 6*221^4≤n ∧
    (13:ℕ)^4≤12*17^4 ∧ (17:ℕ)^4≤12*13^4 ∧
    RecognizingQuarticProducts.factors 318065 552963=(13^4*p,17^4*q) := by
  obtain ⟨prod,pp,qp,order,balanced⟩ := BalancedQuarticLocalExample.data
  obtain ⟨lp,hq,ln,hn⟩ := BalancedQuarticLocalExample.widths
  obtain ⟨primitive,size,_⟩ := BalancedQuarticLocalExample.supplied_pair
  exact ⟨by decide,by decide,primitive,BalancedQuarticLocalExample.identity,prod,pp,qp,order,
    balanced,lp,hq,ln,hn,size,by decide,by decide,by decide +kernel⟩

end PrimeFactors.LeastPrimitiveQuarticDenominator
