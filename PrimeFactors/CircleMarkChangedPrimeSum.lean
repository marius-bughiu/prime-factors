import PrimeFactors.CircleMarkSharedOccurrence

/-! Counting changed scores, irrespective of sign, gives a different reading
from summing the scores. Even one root yields the prime sum for every odd
semiprime. Longer collision-free square prefixes amplify its spacing. -/
namespace PrimeFactors.CircleMarkChangedPrimeSum

open Finset CircleMarkSharedOccurrence CircleMarkSharedScores CircleMarkTargetFrequency

noncomputable def tally (n : ℕ) [NeZero n] (d : ℕ) : ℕ :=
  (changed n {Icc 1 d}).card

/-- Length-d prefix before either prime starts repeating square roots. -/
theorem tally_eq {p q d : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) (cap : d≤(p-1)/2) :
    tally (p*q) d=d*(p+q-2-d) := by
  have capq : d≤(q-1)/2 := by omega
  have e := count order.ne ({Icc 1 d} : Finset (Finset ℕ))
  simp only [singleton_biUnion,id_eq,live,prefix_cover op,prefix_cover oq,
    min_eq_left cap,min_eq_left capq] at e
  change tally (p*q) d+(p-1-d)*(q-1-d)=(p-1)*(q-1) at e
  let x := p-1-d
  let y := q-1-d
  have P : p-1=x+d := by dsimp [x]; omega
  have Q : q-1=y+d := by dsimp [y]; omega
  have sum : p+q-2-d=x+y+d := by have := hp.out.two_le; have := hq.out.two_le; omega
  change tally (p*q) d+x*y=(p-1)*(q-1) at e
  rw [P,Q] at e
  rw [sum]
  nlinarith only [e]

/-- The prime sum can be read by dividing this unsigned count by its length. -/
theorem decode {p q d : ℕ} [Fact p.Prime] [Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) (pos : 0<d) (cap : d≤(p-1)/2) :
    tally (p*q) d / d + d + 2 = p+q := by
  rw [tally_eq order op oq cap,Nat.mul_div_cancel_left _ pos]
  omega

/-- A single linear mask has signed sum one, yet its unsigned changes
from the unmasked character have total p+q−3. -/
theorem singleton {p q : ℕ} [hp : Fact p.Prime] [Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) :
    tally (p*q) 1=p+q-3 ∧ CircleMarkJacobiMask.globalSum (p*q) (CircleMarkJacobiMask.prefixMask 1)=1 := by
  have pp := hp.out.two_le
  have cap : 1≤(p-1)/2 := by omega
  have capq : 1≤(q-1)/2 := by omega
  exact ⟨by rw [tally_eq order op oq cap,one_mul]; omega,
    by rw [CircleMarkJacobiMask.prefix_sum order.ne op oq,min_eq_left cap,min_eq_left capq]; decide⟩

/-- An exact singleton tally is arithmetically equivalent to the totient. -/
theorem singleton_totient {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) :
    tally (p*q) 1+(p*q).totient+2=p*q := by
  rw [(singleton order op oq).1,Nat.totient_mul ((Nat.coprime_primes hp.out hq.out).mpr order.ne),
    Nat.totient_prime hp.out,Nat.totient_prime hq.out]
  have P := Nat.sub_add_cancel hp.out.one_le
  have Q := Nat.sub_add_cancel hq.out.one_le
  have total : p+q-3+3=p+q := by have := hp.out.two_le; have := hq.out.two_le; omega
  nlinarith only [total,P,Q,congrArg₂ Nat.mul P Q]

/-- Product-only length that is safe whenever the larger prime is below twice the smaller. -/
def publicLength (n : ℕ) := (n/2).sqrt/2

theorem public_safe {p q : ℕ} [hp : Fact p.Prime] (order : p<q) (bal : q<2*p) (op : p≠2) :
    0<publicLength (p*q) ∧ publicLength (p*q)≤(p-1)/2 := by
  have pp := hp.out.two_le
  have sq : (p*q/2).sqrt<p := Nat.sqrt_lt.mpr ((Nat.div_lt_iff_lt_mul (by decide : 0<2)).mpr
    (by simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using Nat.mul_lt_mul_of_pos_left bal hp.out.pos))
  have large : 8≤p*q := by nlinarith [show 3≤p by omega, show 4≤q by omega]
  have root : 2≤(p*q/2).sqrt := Nat.le_sqrt.mpr (by omega)
  unfold publicLength
  omega

private theorem length_lower (n w : ℕ) (h : 2*((2^w*2)*(2^w*2))≤n) :
    2^w≤publicLength n := by
  unfold publicLength
  apply (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
  apply Nat.le_sqrt.mpr
  apply (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
  simpa only [Nat.mul_comm 2 _] using h

set_option exponentiation.threshold 8192 in
/-- The product-only prefix makes absolute error below 2^(-1026) in the
changed fraction sufficient at any pair of distinct 1024-bit primes. -/
theorem public_scale {p q : ℕ} (lo : 2^1023≤p) (order : p<q) (hi : q<2^1024) :
    p*q < publicLength (p*q)*2^1026 := by
  have lower : 2^2046≤p*q := (show (2:ℕ)^2046=2^1023*2^1023 by decide +kernel) ▸
    Nat.mul_le_mul lo (lo.trans order.le)
  have upper : p*q<2^2048 := (Nat.mul_lt_mul_of_pos_right (order.trans hi) (by omega)).trans_le
    ((Nat.mul_le_mul_left (2^1024) hi.le).trans_eq (by decide +kernel))
  by_cases big : 2^2047≤p*q
  · have cap := length_lower (p*q) 1022 ((by decide +kernel : 2*((2^1022*2)*(2^1022*2))≤2^2047).trans big)
    exact upper.trans_le ((by decide +kernel : (2:ℕ)^2048≤2^1022*2^1026).trans (Nat.mul_le_mul_right _ cap))
  · have cap := length_lower (p*q) 1021 ((by decide +kernel : 2*((2^1021*2)*(2^1021*2))≤2^2046).trans lower)
    exact (lt_of_not_ge big).trans_le ((by decide +kernel : (2:ℕ)^2047≤2^1021*2^1026).trans (Nat.mul_le_mul_right _ cap))

/-- The nearest even prime sum is stable under a strict absolute count error of d. -/
theorem rounded_sum {p q d : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) (pos : 0<d) (cap : d≤(p-1)/2)
    (y : ℚ) (err : |y-(tally (p*q) d:ℚ)|<d) :
    2*⌊(y/d+d+2)/2+1/2⌋=(p:ℤ)+q := by
  have P := hp.out.two_le
  have dd : 0<(d:ℚ) := by exact_mod_cast pos
  have room : d+2≤p+q := by omega
  have counts : (tally (p*q) d:ℚ) = d*((p:ℚ)+q-2-d) := by
    rw [tally_eq order op oq cap,Nat.cast_mul]
    rw [show p+q-2-d=p+q-(d+2) by omega,Nat.cast_sub room]
    push_cast
    ring
  obtain ⟨a,pa⟩ := hp.out.odd_of_ne_two op
  obtain ⟨b,qb⟩ := hq.out.odd_of_ne_two oq
  have even : (p:ℚ)+q=2*((a:ℚ)+b+1) := by rw [pa,qb]; push_cast; ring
  rw [counts,even,abs_lt] at err
  have low : 2*((a:ℚ)+b+1)-2-d-1<y/d :=
    (lt_div_iff₀ dd).mpr (by linarith only [err.1])
  have high : y/d<2*((a:ℚ)+b+1)-2-d+1 :=
    (div_lt_iff₀ dd).mpr (by linarith only [err.2])
  have rounded : ⌊(y/d+d+2)/2+1/2⌋=(a:ℤ)+b+1 := by
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith only [low,high]
  rw [rounded,pa,qb]
  push_cast
  ring

/-- Exact factor recovery from the singleton count with ordinary integer arithmetic. -/
theorem factors {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (order : p<q) (op : p≠2) (oq : q≠2) :
    let s := tally (p*q) 1+3
    let g := (s^2-4*(p*q)).sqrt
    ((s-g)/2,(s+g)/2)=(p,q) := by
  have s : tally (p*q) 1+3=p+q := by have := (singleton order op oq).1; have := Fact.out (p:=p.Prime) |>.two_le; omega
  have h : p+(q-p)=q := by omega
  have disc : (p+q)^2-4*(p*q)=(q-p)^2 := by
    apply Nat.sub_eq_of_eq_add
    nlinarith only [congrArg (fun t : ℕ => t^2) h,congrArg (fun t : ℕ => p*t) h]
  dsimp only
  rw [s,disc,Nat.sqrt_eq']
  congr 1 <;> omega

end PrimeFactors.CircleMarkChangedPrimeSum
