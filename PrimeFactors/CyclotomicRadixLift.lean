import PrimeFactors.CyclotomicSumDigit
import PrimeFactors.ProductDeficitBand

/-! Use the congruences of odd factors to reduce the precision of a supplied cyclotomic
evaluation. All integer bounds and radix choices use only the product and factor width. -/
namespace PrimeFactors.CyclotomicRadixLift

open CyclotomicSumDigit (digit)
open Polynomial

set_option exponentiation.threshold 4096

/-- The forced factors of the totient in addition to the unconditional factor four. -/
def bonus (N : ℕ) := (if N%4=3 then 2 else 1)*(if N%3=2 then 3 else 1)
def weight (N : ℕ) := 2*bonus N
def stride (N : ℕ) := 2*weight N

theorem weights (N : ℕ) : weight N=2 ∨ weight N=4 ∨ weight N=6 ∨ weight N=12 := by
  unfold weight bonus
  split_ifs <;> decide

private theorem local_table (a b : Fin 6) : bonus ((2*a.val+1)*(2*b.val+1)) ∣ a.val*b.val := by
  have h : ∀ a b : Fin 6, bonus ((2*a.val+1)*(2*b.val+1))∣a.val*b.val := by decide +kernel
  exact h a b

/-- F is a multiple of 4, 8, 12 or 24 according to N modulo 12. -/
theorem divides {p q : ℕ} (po : Odd p) (qo : Odd q) : stride (p*q)∣(p-1)*(q-1) := by
  obtain ⟨a,rfl⟩ := po
  obtain ⟨b,rfl⟩ := qo
  let h := bonus ((2*a+1)*(2*b+1))
  have lift (a : ℕ) : 2*(a%6)+1 ≡ 2*a+1 [MOD 12] :=
    ((Nat.mod_modEq a 6).mul_left' 2).add_right 1
  have key := (lift a).mul (lift b)
  have same : bonus ((2*(a%6)+1)*(2*(b%6)+1))=h := by
    unfold h bonus
    rw [show ((2*(a%6)+1)*(2*(b%6)+1))%4=((2*a+1)*(2*b+1))%4 from
      key.of_dvd (by decide : 4∣12),
      show ((2*(a%6)+1)*(2*(b%6)+1))%3=((2*a+1)*(2*b+1))%3 from
      key.of_dvd (by decide : 3∣12)]
  have h6 : h∣6 := by unfold h bonus; split_ifs <;> decide
  have t := local_table ⟨a%6,Nat.mod_lt _ (by decide)⟩ ⟨b%6,Nat.mod_lt _ (by decide)⟩
  simp only at t
  rw [same] at t
  obtain ⟨z,hz⟩ := (((Nat.mod_modEq a 6).mul (Nat.mod_modEq b 6)).dvd_iff h6).1 t
  refine ⟨z,?_⟩
  simp only [Nat.add_one_sub_one]
  change (2*a)*(2*b)=(2*(2*h))*z
  nlinarith only [hz]

/-- F=W*x. The possible x form the interval [bottom, bottom+choices). -/
def bottom (N W H : ℕ) := (N+W-H)/W
def choices (N W L H : ℕ) := (N-L)/W+1-bottom N W H

theorem in_range {N W L H x : ℕ} (wp : 0<W) (fn : W*x≤N)
    (lo : L≤N-W*x) (hi : N-W*x<H) :
    bottom N W H≤x ∧ x<bottom N W H+choices N W L H := by
  have lower : bottom N W H<x+1 := (Nat.div_lt_iff_lt_mul wp).mpr (by
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm x W]
    omega)
  have upper : x≤(N-L)/W := (Nat.le_div_iff_mul_le wp).mpr (by rw [Nat.mul_comm]; omega)
  unfold choices
  omega

/-- This digit cannot distinguish indices separated by M/gcd(M,g). On a consecutive
list the bound on the index count is exact, including when the digit and stride share factors. -/
theorem injective_iff {M g start count : ℕ} (mp : 0<M) :
    (∀ i<count, ∀ j<count, g*(start+i) ≡ g*(start+j) [MOD M] → i=j) ↔
      count≤M/(M.gcd g) := by
  let k := M/(M.gcd g)
  have div := Nat.gcd_dvd_left M g
  have den : 0<M.gcd g := Nat.gcd_pos_of_pos_left g mp
  have kp : 0<k := Nat.div_pos (Nat.le_of_dvd mp div) den
  have full : k*(M.gcd g)=M := Nat.div_mul_cancel div
  constructor
  · intro inject
    by_contra! bad
    have period : M∣g*k := by
      obtain ⟨v,vg⟩ := Nat.gcd_dvd_right M g
      refine ⟨v,?_⟩
      calc
        _ = (M.gcd g*v)*k := congrArg (·*k) vg
        _ = (k*(M.gcd g))*v := by ring
        _ = _ := by rw [full]
    have same : g*(start+0) ≡ g*(start+k) [MOD M] := by
      rw [Nat.add_zero,Nat.mul_add]
      exact (Nat.modEq_zero_iff_dvd.mpr period).symm.add_left _
    have eq := inject 0 (by omega) k bad same
    omega
  · intro short i il j jl eq
    have reduced := Nat.ModEq.add_left_cancel' start (eq.cancel_left_div_gcd mp)
    exact reduced.eq_of_lt_of_lt (il.trans_le short) (jl.trans_le short)

/-- Decode a supplied modular evaluation by a Bézout inverse and one modular reduction. -/
def decode (N g M H : ℕ) (value : ℤ) : ℤ :=
  let first : ℤ := bottom N (2*g) H
  let pos := first+(digit value M * g.gcdA M-first) % M
  N+1-2*(g:ℤ)*pos

theorem recover {p q M L H : ℕ} {value : ℤ} (hp : p.Prime) (hq : q.Prime)
    (neq : p≠q) (po : Odd p) (qo : Odd q) (mp : 0<M)
    (cop : (weight (p*q)).Coprime M)
    (lo : L≤p+q-1) (hi : p+q-1<H) (enough : choices (p*q) (stride (p*q)) L H≤M)
    (supplied : value ≡ (cyclotomic (p*q) ℤ).eval (1+(M:ℤ)) [ZMOD (M:ℤ)^2]) :
    decode (p*q) (weight (p*q)) M H value = p+q := by
  let g := weight (p*q)
  let f := (p-1)*(q-1)
  let first := bottom (p*q) (2*g) H
  have gp : 0<g := by rcases weights (p*q) with h|h|h|h <;> dsimp only [g] <;> omega
  obtain ⟨x,hx⟩ := divides po qo
  change f=2*g*x at hx
  have off : p*q=f+(p+q-1) := PowerImageWidth.offset hp.pos hq.pos
  have xr := in_range (N:=p*q) (W:=2*g) (x:=x) (L:=L) (H:=H) (by positivity : 0<2*g) (by omega) (by omega) (by omega)
  change first≤x ∧ x<first+choices (p*q) (stride (p*q)) L H at xr
  obtain ⟨c,dig⟩ := CyclotomicSumDigit.digit_of_evaluation hp hq neq (by exact_mod_cast mp) supplied
  have sum : ((p:ℤ)*q+1)-(p+q)=f := by
    dsimp [f]
    push_cast [hp.one_le,hq.one_le]
    ring
  have xm : (g:ℤ)*x=digit value M+M*c := by
    have e : (f:ℤ)=2*(g:ℤ)*x := by exact_mod_cast hx
    linarith only [dig,sum,e]
  have bez := Nat.gcd_eq_gcd_ab g M
  rw [cop.gcd_eq_one,Nat.cast_one] at bez
  have modEq : digit value M*g.gcdA M-(first:ℤ) ≡ (x:ℤ)-first [ZMOD (M:ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨c*g.gcdA M+(x:ℤ)*g.gcdB M,?_⟩
    nlinarith only [congrArg (fun v => (x:ℤ)*v) bez,congrArg (fun v => v*g.gcdA M) xm]
  have r : ((x:ℤ)-first)%(M:ℤ)=(x:ℤ)-first := Int.emod_eq_of_lt (by omega) (by omega)
  change (p*q:ℕ)+1-2*(g:ℤ)*((first:ℤ)+(digit value M*g.gcdA M-first)%(M:ℤ))=_
  rw [show (digit value M*g.gcdA M-(first:ℤ))%(M:ℤ)=((x:ℤ)-first)%(M:ℤ) from modEq,r]
  push_cast
  have e : (f:ℤ)=2*(g:ℤ)*x := by exact_mod_cast hx
  nlinarith only [sum,e]

/-- Round up to an odd radix, also avoiding three when the public stride contains three.
This examines at most four consecutive integers, independent of their bit width. -/
def radix (N c : ℕ) :=
  let o := c+(c+1)%2
  if N%3=2 ∧ o%3=0 then o+2 else o

theorem radix_spec (N c : ℕ) :
    c≤radix N c ∧ radix N c≤c+3 ∧ radix N c%2=1 ∧ (weight N).Coprime (radix N c) := by
  let m := radix N c
  have limits : c≤m ∧ m≤c+3 ∧ m%2=1 ∧ (N%3=2 → m%3≠0) := by
    dsimp [m,radix]
    split_ifs <;> omega
  have two : Nat.Coprime 2 m := Nat.prime_two.coprime_iff_not_dvd.mpr (by
    rw [Nat.dvd_iff_mod_eq_zero]; omega)
  have three (h : N%3=2) : Nat.Coprime 3 m := Nat.prime_three.coprime_iff_not_dvd.mpr (by
    rw [Nat.dvd_iff_mod_eq_zero]; exact limits.2.2.2 h)
  refine ⟨limits.1,limits.2.1,limits.2.2.1,?_⟩
  change (weight N).Coprime m
  unfold weight bonus
  split_ifs with four th th
  · exact Nat.coprime_mul_iff_left.mpr ⟨two,Nat.coprime_mul_iff_left.mpr ⟨two,three th⟩⟩
  · exact Nat.coprime_mul_iff_left.mpr ⟨two,by simpa only [Nat.mul_one] using two⟩
  · exact Nat.coprime_mul_iff_left.mpr ⟨two,by simpa only [Nat.one_mul] using three th⟩
  · simpa using two

/-- The least odd effective radix even if a noncoprime radix is permitted. -/
theorem minimal {N c M : ℕ} (odd : M%2=1) (works : c≤M/(M.gcd (weight N))) :
    radix N c≤M := by
  have spec := radix_spec N c
  have mp : 0<M := by omega
  have gp := Nat.gcd_pos_of_pos_left (weight N) mp
  have cm := works.trans (Nat.div_le_self ..)
  by_contra! before
  have co : M.Coprime (weight N) := by
    by_contra bad
    have g2 : 2≤M.gcd (weight N) := by change ¬M.gcd (weight N)=1 at bad; omega
    have size := (Nat.le_div_iff_mul_le gp).mp works
    have cc := Nat.mul_le_mul_left c g2
    rcases le_or_gt c 1 with small|large
    · have : radix N c=1 := by dsimp [radix]; split_ifs <;> omega
      omega
    · omega
  have three : N%3=2 → M%3≠0 := by
    intro h zero
    have dv : 3∣weight N := by unfold weight bonus; rw [if_pos h]; exact dvd_mul_of_dvd_right (dvd_mul_left ..) _
    have d := Nat.dvd_gcd (Nat.dvd_iff_mod_eq_zero.mpr zero) dv
    rw [co.gcd_eq_one] at d
    exact (by decide : ¬3∣1) d
  dsimp [radix] at before
  split_ifs at before <;> omega

/-- Product-only adaptive recovery for the published equal-width deficit interval. -/
theorem adaptive {p q A : ℕ} {value : ℤ} (hp : p.Prime) (hq : q.Prime) (neq : p≠q)
    (po : Odd p) (qo : Odd q) (ap : 0<A) (even : Even A)
    (pl : A≤p) (ql : A≤q) (pu : p<2*A) (qu : q<2*A) :
    let N := p*q
    let L := ProductDeficitBand.lower N A
    let H := ProductDeficitBand.upper N A
    let M := radix N (choices N (stride N) L H)
    value ≡ (cyclotomic N ℤ).eval (1+(M:ℤ)) [ZMOD (M:ℤ)^2] →
      decode N (weight N) M H value=p+q := by
  let N := p*q
  let L := ProductDeficitBand.lower N A
  let H := ProductDeficitBand.upper N A
  let c := choices N (stride N) L H
  have band := ProductDeficitBand.contains ap even po qo pl ql pu qu
  have spec := radix_spec N c
  exact recover hp hq neq po qo (by omega : 0<radix N c) spec.2.2.2 band.1 band.2 spec.1

/-- A uniform upper bound on the progression length for arbitrary boundaries.
The per-product count can be smaller when the endpoints miss the public residue. -/
theorem choices_le {N W L H M : ℕ} (wp : 0<W) (hn : H≤N) (room : H-L≤W*M) :
    choices N W L H≤M := by
  have eq : N+W-H=(N-H)+W := by omega
  have first : bottom N W H=(N-H)/W+1 := by rw [bottom,eq,Nat.add_div_right _ wp]
  have full := Nat.mod_add_div (N-H) W
  have rem := Nat.mod_lt (N-H) wp
  have left : N-H<bottom N W H*W := by rw [first,Nat.add_mul,Nat.one_mul]; nlinarith only [full,rem]
  have top : (N-L)/W<bottom N W H+M := by
    apply (Nat.div_lt_iff_lt_mul wp).2
    rw [Nat.add_mul,Nat.mul_comm M W]
    omega
  unfold choices
  omega

/-- A worst-case public radix using the 11/64 equal-width estimate, before narrowing
to the actual endpoint count. -/
def uniformRadix (w : ℕ) (r : ℕ) := radix r ((11*2^1017+1+w-1)/w)

/-- When p,q are 1024-bit, this table gives enough slots independently of the product's
position in the range. Each listed modulus fits in the stated number of bits. -/
theorem precision_table :
    ∀ r : Fin 12, let w := stride r.val
      let M := uniformRadix w r.val
      11*2^1017+1≤w*M ∧
      (w=4 → M^2≤2^2037) ∧ (w=8 → M^2≤2^2035) ∧
      (w=12 → M^2≤2^2034) ∧ (w=24 → M^2≤2^2032) := by decide +kernel

/-- Worst-case precision of the adaptively minimal odd radix for 1024-bit factors.
The four bounds price the supplied residue modulo the square of the radix. -/
theorem full_precision {N : ℕ} (lo : (2^1023)*(2^1023)≤N)
    (hi : N≤(2*2^1023-1)^2) :
    let w := stride N
    let M := radix N (choices N w (ProductDeficitBand.lower N (2^1023))
      (ProductDeficitBand.upper N (2^1023)))
    (w=4 → M^2≤2^2037) ∧ (w=8 → M^2≤2^2035) ∧
      (w=12 → M^2≤2^2034) ∧ (w=24 → M^2≤2^2032) := by
  let c := choices N (stride N) (ProductDeficitBand.lower N (2^1023))
    (ProductDeficitBand.upper N (2^1023))
  let m := uniformRadix (stride N) (N%12)
  have eqW : weight (N%12)=weight N := by
    unfold weight bonus
    rw [Nat.mod_mod_of_dvd N (by decide : 4∣12),Nat.mod_mod_of_dvd N (by decide : 3∣12)]
  have eqS : stride (N%12)=stride N := congrArg (2*·) eqW
  have t := precision_table ⟨N%12,Nat.mod_lt _ (by decide)⟩
  dsimp only at t
  rw [eqS] at t
  have hw : 0<stride N := by dsimp only [stride]; rcases weights N with h|h|h|h <;> omega
  have bound {x : ℕ} (h : 64*x≤11*2^1023+64) : x≤11*2^1017+1 := by
    rw [show 11*2^1023+64=64*(11*2^1017+1) by decide +kernel] at h
    exact Nat.le_of_mul_le_mul_left h (by decide)
  have width := bound (ProductDeficitBand.length (A:=2^1023) (by decide) lo hi)
  have hn : ProductDeficitBand.upper N (2^1023)≤N :=
    (min_le_left ..).trans ((by decide +kernel : 4*2^1023≤2^1023*2^1023).trans lo)
  have fit : c≤m := choices_le hw hn (width.trans t.1)
  have rs := radix_spec (N%12) ((11*2^1017+1+stride N-1)/stride N)
  have cop : (weight N).Coprime m := eqW ▸ rs.2.2.2
  have small : radix N c≤m := minimal rs.2.2.1 (by simpa only [cop.symm.gcd_eq_one,Nat.div_one] using fit)
  have powLe := Nat.pow_le_pow_left small 2
  exact ⟨fun h => powLe.trans (t.2.1 h),fun h => powLe.trans (t.2.2.1 h),
    fun h => powLe.trans (t.2.2.2.1 h),fun h => powLe.trans (t.2.2.2.2 h)⟩

/-- For 9017 the public interval and congruence alone suffice. -/
theorem example_9017 :
    choices 9017 (stride 9017) 189 198=1 ∧
    radix 9017 1=1 ∧ decode 9017 (weight 9017) 1 198 0=198 :=
  by
    refine ⟨by decide +kernel,by decide +kernel,?_⟩
    simp only [decode, Nat.cast_one, Int.emod_one, add_zero]
    decide +kernel

/-- For 107683 the residue 7 modulo 9 selects the correct sum from three possibilities. -/
theorem example_107683 :
    (cyclotomic 107683 ℤ).eval 4 % 9=7 ∧
    choices 107683 (stride 107683) 657 676=3 ∧
    radix 107683 3=3 ∧ decode 107683 (weight 107683) 3 676 7=676 ∧
    Nat.Prime 257 ∧ Nat.Prime 419 ∧ 257*419=107683 := by
  have hp : Nat.Prime 257 := by norm_num
  have hq : Nat.Prime 419 := by norm_num
  have e := CyclotomicSumDigit.evaluation_mod (p:=257) (q:=419) hp hq (by decide) 3
  have v : (cyclotomic 107683 ℤ).eval 4 ≡ 7 [ZMOD 9] := e.trans (by decide)
  have r := recover (p:=257) (q:=419) (L:=657) (H:=676) (M:=3) hp hq (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide)
    (by decide +kernel) v.symm
  exact ⟨v,by decide +kernel,by decide +kernel,r,hp,hq,by decide⟩

end PrimeFactors.CyclotomicRadixLift
