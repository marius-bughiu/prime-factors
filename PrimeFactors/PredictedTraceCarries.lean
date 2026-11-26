import PrimeFactors.TraceProgression
import PrimeFactors.PartialOrder
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum.Prime

/-! A weighted-sum label directly from two rounded digits of the product.
At radix D write p=AD+u, q=BD+v with signed displacements. Only the
product AB of the anchor coefficients enters the discriminant. -/

namespace PrimeFactors.PredictedTraceCarries

/-- Nearest quotient, with half ties rounded upward, including negative inputs. -/
def nearest (n d : ℤ) : ℤ := (2*n+d)/(2*d)

theorem nearest_shift {d : ℤ} (pos : 0<d) (x k : ℤ) :
    nearest (x+d*k) d=nearest x d+k := by
  unfold nearest
  rw [show 2*(x+d*k)+d=(2*x+d)+(2*d)*k by ring,
    Int.add_mul_ediv_left _ _ (by positivity)]

/-- Every centered remainder has magnitude at most half the radix. -/
theorem nearest_error {n d : ℤ} (pos : 0<d) : 2*|n-d*nearest n d|≤d := by
  have den : 0<2*d := by omega
  have lo := (Int.le_ediv_iff_mul_le den).mp (show nearest n d≤(2*n+d)/(2*d) from le_rfl)
  have hi := (Int.ediv_lt_iff_lt_mul den).mp (show (2*n+d)/(2*d)<nearest n d+1 from Int.lt_add_one_iff.mpr le_rfl)
  rcases le_total 0 (n-d*nearest n d) with h|h
  · rw [abs_of_nonneg h]; nlinarith only [hi]
  · rw [abs_of_nonpos h]; nlinarith only [lo]

/-- Exact bounds for the signed carry, including the lower half tie. -/
theorem nearest_abs_iff {n d : ℤ} (H : ℕ) (pos : 0<d) :
    |nearest n d|≤H ↔ -(2*(H:ℤ)+1)*d≤2*n ∧ 2*n<(2*(H:ℤ)+1)*d := by
  have den : 0<2*d := by omega
  rw [abs_le]
  constructor
  · rintro ⟨lo,hi⟩
    have l := (Int.le_ediv_iff_mul_le den).mp lo
    have r := (Int.ediv_lt_iff_lt_mul den).mp (show nearest n d<(H:ℤ)+1 by omega)
    constructor <;> nlinarith only [l,r]
  · rintro ⟨lo,hi⟩
    constructor
    · exact (Int.le_ediv_iff_mul_le den).mpr (by nlinarith only [lo])
    · have t : nearest n d<(H:ℤ)+1 :=
        (Int.ediv_lt_iff_lt_mul den).mpr (by nlinarith only [hi])
      omega

/-- A sufficient symmetric error tolerance, excluding any boundary tie. -/
theorem nearest_abs_le {n d : ℤ} {H : ℕ} (pos : 0<d)
    (bound : |2*n|<(2*(H:ℤ)+1)*d) : |nearest n d|≤H := by
  obtain ⟨lo,hi⟩ := abs_lt.mp bound
  exact (nearest_abs_iff H pos).mpr ⟨by simpa only [neg_mul] using lo.le,hi⟩

def coefficient (n D : ℕ) (h : ℤ) : ℤ := nearest n ((D:ℤ)^2)+h

def label (n D : ℕ) (h k : ℤ) : ℤ := coefficient n D h*D+nearest n D-k

/-- These signed carries describe the promise. Neither is an input to the
public search, which can enumerate the chosen ranges for h and k. -/
def highCarry (p q D A B : ℕ) : ℤ := (A:ℤ)*B-nearest ((p:ℤ)*q) ((D:ℤ)^2)

def lowCarry (p q D A B : ℕ) : ℤ :=
  nearest (((p:ℤ)-A*D)*((q:ℤ)-B*D)) D

/-- This identity works for every pair of integer anchors at every positive
radix. It explains why trial values of only two carries suffice. -/
theorem predicted {p q D A B : ℕ} (pos : 0<D) :
    coefficient (p*q) D (highCarry p q D A B)=(A*B:ℕ) ∧
    label (p*q) D (highCarry p q D A B) (lowCarry p q D A B)=(B*p+A*q:ℕ) := by
  have hc : coefficient (p*q) D (highCarry p q D A B)=(A*B:ℕ) := by
    simp only [coefficient,highCarry,Nat.cast_mul]; ring
  refine ⟨hc,?_⟩
  unfold label
  rw [hc]
  unfold lowCarry
  push_cast
  have hi : (p:ℤ)*q=(((p:ℤ)-A*D)*((q:ℤ)-B*D))+
      D*((B:ℤ)*p+A*q-A*B*D) := by ring
  conv_lhs => arg 1; arg 2; rw [hi,nearest_shift (by exact_mod_cast pos)]
  ring

/-- A single trial uses the input, radix and two signed proposed carries.
It tests one square, then checks one gcd of an integer root with N. -/
def probe (n D : ℕ) (h k : ℤ) : Option ℕ :=
  let c := coefficient n D h
  let t := label n D h k
  let v := 4*c.toNat*n
  let r := (t.toNat^2-v).sqrt
  let d := n.gcd ((t.toNat+r)/2)
  if 0<c ∧ 0<t ∧ r^2+v=t.toNat^2 ∧ (t.toNat+r)%2=0 ∧ 1<d ∧ d<n then some d else none

/-- Every successful trial exhibits a proper divisor, with no carry or factor hypotheses. -/
theorem probe_sound {n D divisor : ℕ} {h k : ℤ} (hit : probe n D h k=some divisor) :
    1<divisor ∧ divisor<n ∧ divisor∣n := by
  simp only [probe] at hit
  split at hit
  next guards =>
    injection hit with h
    subst divisor
    exact ⟨guards.2.2.2.2.1,guards.2.2.2.2.2,Nat.gcd_dvd_left ..⟩
  next => contradiction

/-- An exact square witness checks a concrete trial without evaluating a
large integer square root inside the kernel. -/
theorem probe_of_square {n D c t r divisor : ℕ} {h k : ℤ}
    (coef : coefficient n D h=c) (trace : label n D h k=t)
    (pos : 0<c ∧ 0<t) (square : t^2=r^2+4*c*n) (even : (t+r)%2=0)
    (val : n.gcd ((t+r)/2)=divisor) (proper : 1<divisor ∧ divisor<n) :
    probe n D h k=some divisor := by
  have root : (t^2-4*c*n).sqrt=r := by rw [square,Nat.add_sub_cancel,Nat.sqrt_eq']
  have cp : (0:ℤ)<c := by exact_mod_cast pos.1
  have tp : (0:ℤ)<t := by exact_mod_cast pos.2
  simp only [probe,coef,trace,Int.toNat_natCast,root,cp,tp,square.symm,even,val,
    proper.1,proper.2,and_self,ite_true]

private theorem root_read (x y : ℕ) :
    let r := ((x+y)^2-4*(x*y)).sqrt
    r^2+4*(x*y)=(x+y)^2 ∧ (x+y+r)%2=0 ∧ (x+y+r)/2=max x y := by
  wlog h : x≤y generalizing x y
  · simpa only [add_comm y x,mul_comm y x,max_comm y x] using this y x (by omega)
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le h
  have eq : (x+(x+j))^2=j^2+4*(x*(x+j)) := by ring
  dsimp only
  rw [eq,Nat.add_sub_cancel,Nat.sqrt_eq']
  simp only [max_eq_right (by omega : x≤x+j),true_and]
  omega

/-- Use the larger quadratic root; coprimality of AB with the input prevents
the other prime from entering its gcd. Distinct primality can be relaxed:
the argument works for any nontrivial factors under the stated coprimality. -/
theorem probe_complete {p q D A B : ℕ} (pos : 0<D) (pa : 1<p) (qa : 1<q)
    (Apos : 0<A) (Bpos : 0<B) (cop : (A*B).Coprime (p*q)) :
    let h := highCarry p q D A B
    let k := lowCarry p q D A B
    probe (p*q) D h k=some p ∨ probe (p*q) D h k=some q := by
  obtain ⟨coef,trace⟩ := predicted (p:=p) (q:=q) (A:=A) (B:=B) pos
  dsimp only
  simp only [probe,coef,trace,Int.toNat_natCast]
  have pro : 4*(A*B)*(p*q)=4*((B*p)*(A*q)) := by ring
  simp only [pro]
  obtain ⟨square,even,read⟩ := root_read (B*p) (A*q)
  simp only [read]
  have one : 0<((A*B:ℕ):ℤ) := by positivity
  have two : 0<((B*p+A*q:ℕ):ℤ) := by positivity
  have pp : p<p*q := by simpa using Nat.mul_lt_mul_of_pos_left qa (by omega : 0<p)
  have qp : q<p*q := by simpa using Nat.mul_lt_mul_of_pos_right pa (by omega : 0<q)
  by_cases cmp : A*q≤B*p
  · left
    have ok : q.Coprime B :=
      (cop.coprime_dvd_left (dvd_mul_left B A) |>.coprime_dvd_right (dvd_mul_left q p)).symm
    have key : (p*q).gcd (B*p)=p := by rw [mul_comm B p,Nat.gcd_mul_left,ok.gcd_eq_one,Nat.mul_one]
    simp only [max_eq_left cmp,key,one,two,square,even,pa,pp,and_self,ite_true]
  · right
    have ok : p.Coprime A :=
      (cop.coprime_dvd_left (dvd_mul_right A B) |>.coprime_dvd_right (dvd_mul_right p q)).symm
    have key : (p*q).gcd (A*q)=q := by rw [mul_comm p q,mul_comm A q,Nat.gcd_mul_left,ok.gcd_eq_one,Nat.mul_one]
    simp only [max_eq_right (by omega : B*p≤A*q),key,one,two,square,even,qa,qp,and_self,ite_true]

/-- Recovers a factor whenever both actual integer carries are in the
advertised box, including cases on the rounding boundary. -/
theorem bounded_carries {p q D A B H K : ℕ} (pos : 0<D) (pa : 1<p) (qa : 1<q)
    (Apos : 0<A) (Bpos : 0<B) (cop : (A*B).Coprime (p*q))
    (hh : |highCarry p q D A B|≤H) (kk : |lowCarry p q D A B|≤K) :
    ∃ h∈Finset.Icc (-(H:ℤ)) H, ∃ k∈Finset.Icc (-(K:ℤ)) K,
      probe (p*q) D h k=some p ∨ probe (p*q) D h k=some q :=
  ⟨_,Finset.mem_Icc.mpr (abs_le.mp hh),_,Finset.mem_Icc.mpr (abs_le.mp kk),
    probe_complete pos pa qa Apos Bpos cop⟩

/-- Complete scan over the rectangular carry budget. The number of distinct
trials is (2H+1)(2K+1), independent of the sizes of the high anchor digits. -/
theorem bounded_complete {p q D A B H K : ℕ} (pos : 0<D) (pa : 1<p) (qa : 1<q)
    (Apos : 0<A) (Bpos : 0<B) (cop : (A*B).Coprime (p*q))
    (upper : |2*((p:ℤ)*q-A*B*(D:ℤ)^2)| < (2*(H:ℤ)+1)*(D:ℤ)^2)
    (lower : |2*(((p:ℤ)-A*D)*((q:ℤ)-B*D))| < (2*(K:ℤ)+1)*D) :
    ∃ h∈Finset.Icc (-(H:ℤ)) H, ∃ k∈Finset.Icc (-(K:ℤ)) K,
      probe (p*q) D h k=some p ∨ probe (p*q) D h k=some q := by
  have d : (0:ℤ)<D := by exact_mod_cast pos
  have high := nearest_abs_le (sq_pos_of_pos d) upper
  have low := nearest_abs_le d lower
  have tr := nearest_shift (sq_pos_of_pos d) ((p:ℤ)*q-A*B*(D:ℤ)^2) ((A:ℤ)*B)
  rw [show (p:ℤ)*q-A*B*(D:ℤ)^2+(D:ℤ)^2*(A*B)=p*q by ring] at tr
  have hh : |highCarry p q D A B|≤H := by
    unfold highCarry
    rw [tr,show (A:ℤ)*B-(nearest ((p:ℤ)*q-A*B*(D:ℤ)^2) ((D:ℤ)^2)+A*B)=
      -nearest ((p:ℤ)*q-A*B*(D:ℤ)^2) ((D:ℤ)^2) by ring,abs_neg]
    exact high
  exact bounded_carries pos pa qa Apos Bpos cop hh low

/-- Exact count of public square tests if the entire correction box is searched. -/
theorem box_card (H K : ℕ) :
    ((Finset.Icc (-(H:ℤ)) H) ×ˢ (Finset.Icc (-(K:ℤ)) K)).card=(2*H+1)*(2*K+1) := by
  rw [Finset.card_product,Int.card_Icc,Int.card_Icc]
  congr 1 <;> omega

/-- Example rule: retain roughly three leading bits per factor, using N alone. -/
def sampleRadix (n : ℕ) : ℕ := 2^((n.log2-5)/2)

private theorem prime_binary {n : ℕ} (g : ZMod n) (large : 1<n) (small : n≤32768^2)
    (full : g^32768=1) (half : Nat.Coprime ((g^16384-1).val) n) : n.Prime := by
  apply prime_of_partial_order_cover g large (by decide : 0<32768) small
    (ps:=[2]) (Covers.cons 15 Nat.prime_two covers_one) full
  intro l hl
  have eq : l=2 := by simpa only [List.mem_singleton] using hl
  subst l
  exact half

private theorem sample_smaller_prime : Nat.Prime 167772161 := by
  apply prime_binary (34951379:ZMod 167772161) (by decide) (by decide)
  · reduce_mod_char
  · have eq : (34951379:ZMod 167772161)^16384=167772160 := by reduce_mod_char
    rw [eq]; decide +kernel

private theorem sample_larger_prime : Nat.Prime 237273089 := by
  apply prime_binary (80581608:ZMod 237273089) (by decide) (by decide)
  · reduce_mod_char
  · have eq : (80581608:ZMod 237273089)^16384=237273088 := by reduce_mod_char
    rw [eq]; decide +kernel

/-- Constructed example with p=5D+1 and q=7D+2392065. A single product-only
square test recovers the larger prime at label 1262 of the ordinary canonical
(7,5) trace row. The large offset is never enumerated. -/
theorem one_trial_example :
    let n := 39807818888675329
    let D := sampleRadix n
    D=33554432 ∧ coefficient n D 0=35 ∧ label n D 0 0=2360770572 ∧
    TraceCoverCertificate.validStart n ⟨7,5,2360740284,24⟩ ∧
    2360740284+24*1262=label n D 0 0 ∧ probe n D 0 0=some 237273089 ∧
    167772161*237273089=n ∧ Nat.Prime 167772161 ∧ Nat.Prime 237273089 := by
  dsimp only
  have size : Nat.log2 39807818888675329=55 := by
    have lo := (Nat.le_log2 (by decide : (39807818888675329:ℕ)≠0)).mpr
      (by decide +kernel : (2:ℕ)^55≤39807818888675329)
    have hi := (Nat.log2_lt (by decide : (39807818888675329:ℕ)≠0)).mpr
      (by decide +kernel : (39807818888675329:ℕ)<2^56)
    omega
  simp only [sampleRadix,size]
  refine ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    by decide +kernel,?_,by decide +kernel,sample_smaller_prime,sample_larger_prime⟩
  apply probe_of_square (c:=35) (t:=2360770572) (r:=11960318)
  all_goals decide +kernel

set_option maxRecDepth 8192 in
/-- At the nonbinary base supplied in Example 3.3 of Mackall's
"A factorization algorithm based on Cohn's irreducibility criterion",
the two signed corrections select the smaller prime. -/
theorem mackall_example :
    probe 207314063849 40098 (-1) 1 = some 323131 ∧
    323131*641579=(207314063849:ℕ) ∧ Nat.Prime 323131 ∧ Nat.Prime 641579 := by
  refine ⟨?_,by decide +kernel,by norm_num,by norm_num⟩
  apply probe_of_square (c:=128) (t:=10302728) (r:=37464)
  all_goals decide +kernel

end PrimeFactors.PredictedTraceCarries
