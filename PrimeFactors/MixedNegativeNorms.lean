import PrimeFactors.MaskedRelations
import Mathlib.Data.Int.ModEq

/-! A square match between two negative remainders from different multiples
of the input. A globally trivial sign forces an integral representation of the
product of the multipliers by the same quadratic form. -/
namespace PrimeFactors.MixedNegativeNorms

/-- If one of the two global signs agrees, the integral composition of the
two representations is divisible by N in both coordinates. -/
theorem quotient {N d k l : ℕ} [NeZero N] (cop : N.Coprime d) {t s a b : ℤ}
    (first : t^2+(d:ℤ)*a^2=(k:ℤ)*N) (second : s^2+(d:ℤ)*b^2=(l:ℤ)*N)
    (same : (N:ℤ) ∣ t*s-(d:ℤ)*a*b) :
    ∃ j v : ℤ, (k:ℤ)*l=j^2+(d:ℤ)*v^2 ∧ t*s-(d:ℤ)*a*b=(N:ℤ)*j ∧ t*b+s*a=(N:ℤ)*v := by
  obtain ⟨j, eq⟩ := same
  have compose : (t*s-(d:ℤ)*a*b)^2+(d:ℤ)*(t*b+s*a)^2=((k:ℤ)*l)*N^2 := by
    calc
      _ = (t^2+(d:ℤ)*a^2)*(s^2+(d:ℤ)*b^2) := by ring
      _ = _ := by rw [first,second]; ring
  rw [eq,mul_pow] at compose
  have divides : (N:ℤ)^2 ∣ (d:ℤ)*(t*b+s*a)^2 := by
    refine ⟨(k:ℤ)*l-j^2, ?_⟩
    linear_combination compose
  obtain ⟨v,hv⟩ := (Int.pow_dvd_pow_iff (by decide : 2≠0)).mp
    (cop.isCoprime.pow_left.dvd_of_dvd_mul_left divides)
  refine ⟨j,v,?_,eq,hv⟩
  have nonzero : (N:ℤ)^2≠0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne N)
  apply mul_right_cancel₀ nonzero
  rw [hv] at compose
  linear_combination -compose

/-- Each global agreement is an explicit transformation between the rows.
This identifies the actual coordinates of a failing match when a form does
represent the multiplier product. -/
theorem transport_iff {N d k l : ℕ} [NeZero N] (cop : N.Coprime d) (kp : 0<k)
    {t s a b : ℤ} (first : t^2+(d:ℤ)*a^2=(k:ℤ)*N)
    (second : s^2+(d:ℤ)*b^2=(l:ℤ)*N) :
    ((N:ℤ) ∣ t*s-(d:ℤ)*a*b) ↔ ∃ j v : ℤ, (k:ℤ)*l=j^2+(d:ℤ)*v^2 ∧
      (k:ℤ)*s=j*t+(d:ℤ)*v*a ∧ (k:ℤ)*b=v*t-j*a := by
  have nz : (N:ℤ)≠0 := by exact_mod_cast NeZero.ne N
  have kz : (k:ℤ)≠0 := by exact_mod_cast kp.ne'
  constructor
  · intro same
    obtain ⟨j,v,form,hj,hv⟩ := quotient cop first second same
    refine ⟨j,v,form,?_,?_⟩
    · apply mul_right_cancel₀ nz
      linear_combination -s*first+t*hj+(d:ℤ)*a*hv
    · apply mul_right_cancel₀ nz
      linear_combination -b*first+t*hv-a*hj
  · rintro ⟨j,v,_,hs,hb⟩
    refine ⟨j,?_⟩
    apply mul_left_cancel₀ kz
    linear_combination t*hs-(d:ℤ)*a*hb+j*first

/-- A multiplier product not represented by j²+d v² rules out both global
signs, so the actual matched-remainder gcd is proper. -/
theorem split {N d k l : ℕ} [NeZero N] (cop : N.Coprime d) {t s a b : ℤ}
    (first : t^2+(d:ℤ)*a^2=(k:ℤ)*N) (second : s^2+(d:ℤ)*b^2=(l:ℤ)*N)
    (absent : ∀ j v : ℤ, (k:ℤ)*l≠j^2+(d:ℤ)*v^2) :
    let x : ZMod N := ↑(t*s)
    let y : ZMod N := ↑((d:ℤ)*a*b)
    1<(x-y).val.gcd N ∧ (x-y).val.gcd N<N := by
  have forbid (b' : ℤ) (row : s^2+(d:ℤ)*b'^2=(l:ℤ)*N) :
      (↑(t*s) : ZMod N) ≠ ↑((d:ℤ)*a*b') := by
    intro h
    obtain ⟨j,v,eq,_⟩ := quotient cop first row ((ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp h.symm)
    exact absent j v eq
  apply maskedRelations_split
  · have a0 : (t:ZMod N)^2+(d:ZMod N)*(a:ZMod N)^2=0 := by
      simpa using congrArg (fun u : ℤ => (u : ZMod N)) first
    have b0 : (s:ZMod N)^2+(d:ZMod N)*(b:ZMod N)^2=0 := by
      simpa using congrArg (fun u : ℤ => (u : ZMod N)) second
    push_cast
    linear_combination (s:ZMod N)^2*a0-(d:ZMod N)*(a:ZMod N)^2*b0
  · exact forbid b second
  · simpa using forbid (-b) (by simpa using second)

/-- Even without factoring d, any d larger than the nonsquare multiplier
product certifies a split. A common square divisor may be retained in d. -/
theorem large_class {d k l : ℕ} (large : k*l<d) (nonsquare : ¬IsSquare (k*l : ℕ)) :
    ∀ j v : ℤ, (k:ℤ)*l≠j^2+(d:ℤ)*v^2 := by
  intro j v eq
  by_cases zero : v=0
  · rw [zero,zero_pow (by decide : 2≠0),mul_zero,add_zero] at eq
    apply nonsquare
    use j.natAbs
    simpa [Int.natAbs_mul,pow_two] using congrArg Int.natAbs eq
  · have one : 1≤v^2 := by nlinarith [sq_pos_of_ne_zero zero]
    have too : (k:ℤ)*l<(d:ℤ) := by exact_mod_cast large
    nlinarith [mul_le_mul_of_nonneg_left one (show 0≤(d:ℤ) by positivity),sq_nonneg j]

/-- For N=7 mod 8, neither x²+y² nor x²+2y² represents N. These
are the only positive coefficients d that could represent the multiplier
product 2, so every unit match between the weights 1 and 2 splits. -/
theorem split_two_seven {N d : ℕ} [NeZero N] (seven : N%8=7) (positive : 0<d)
    (cop : N.Coprime d) {t s a b : ℤ}
    (first : t^2+(d:ℤ)*a^2=(N:ℤ)) (second : s^2+(d:ℤ)*b^2=2*(N:ℤ)) :
    let x : ZMod N := ↑(t*s)
    let y : ZMod N := ↑((d:ℤ)*a*b)
    1<(x-y).val.gcd N ∧ (x-y).val.gcd N<N := by
  apply split (k:=1) (l:=2) cop (by simpa using first) (by simpa using second)
  by_cases large : 2<d
  · exact large_class (by simpa using large) (by decide)
  have n8 : (N : ZMod 8)=7 := by
    apply ZMod.val_injective
    simpa only [ZMod.val_natCast] using seven
  have obstruction : ∀ u v : ZMod 8, u^2+v^2≠7 ∧ u^2+2*v^2≠7 := by decide
  have reduction := congrArg (fun z : ℤ => (z:ZMod 8)) first
  rcases (show d=1 ∨ d=2 by omega) with rfl|rfl
  · exact ((obstruction t a).1 (by simpa [n8] using reduction)).elim
  · exact ((obstruction t a).2 (by simpa [n8] using reduction)).elim

/-- The equal-remainder collision always exists for a balanced pair. Setting
the half-gap t and midpoint s makes t*s+D a multiple of p. The common
remainder is at least seven eighths of N whenever q ≤ 2p. -/
theorem midpoint_match {p q t s N : ℕ} (pp : 2≤p) (order : p<q) (balanced : q≤2*p)
    (gap : p+t=s) (total : s+t=q) (product : p*q=N) :
    ∃ D : ℕ, 2<D ∧ t^2+D=N ∧ s^2+D=2*N ∧ (t*s+D)=p*q+t*p ∧
      (7:ℕ)*N≤8*D := by
  have bound : t*2≤p := by omega
  have base : N=t^2+(p^2+2*p*t-t^2) := by
    have hs : t^2≤p^2 := Nat.pow_le_pow_left (by omega) 2
    have eq : N=p^2+2*p*t := by rw [←product,←total,←gap]; ring
    omega
  use N-t^2
  have dt : t^2≤N := by omega
  have eq : N=p^2+2*p*t := by rw [←product,←total,←gap]; ring
  have add := Nat.sub_add_cancel dt
  have small : 8*t^2≤N := by
    nlinarith [Nat.mul_le_mul bound bound, Nat.mul_le_mul_left (2*t) bound]
  have nn : 8≤N := by nlinarith [show 1≤t by omega, eq]
  refine ⟨by omega, by omega, ?_, ?_, by omega⟩
  · rw [←gap]
    nlinarith
  · rw [←gap,product]
    nlinarith

/-- The universal equal-remainder match recovers the smaller prime. -/
theorem midpoint_prime {p q t s D : ℕ} (prime : q.Prime) (order : p<q)
    (gap : p+t=s) (total : s+t=q) (sum : t*s+D=p*q+t*p) :
    (t*s+D).gcd (p*q)=p := by
  have pos : 0<t := by omega
  have lt : t<q := by omega
  have cop := prime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt pos lt)
  rw [sum, Nat.mul_comm t p, ←Nat.mul_add,Nat.gcd_mul_left]
  simp [Nat.gcd_comm, cop.gcd_eq_one]

end PrimeFactors.MixedNegativeNorms
