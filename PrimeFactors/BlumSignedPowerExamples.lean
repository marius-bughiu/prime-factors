import PrimeFactors.BlumSignedPowers
import PrimeFactors.PartialOrder
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

namespace PrimeFactors.BlumSignedPowerExamples
open BlumSignedPowers

/-- The first signed return on 5,609 splits both labelled factors. -/
theorem simultaneous :
    jacobiSym 3 5609= -1 ∧ 5609=71*79 ∧ Nat.Prime 71 ∧ Nat.Prime 79 ∧
    (3 : ZMod 5609)^701=3766 ∧ (3766 : ZMod 5609)^(2^12-1)=1421 ∧
    (1421-1).gcd 5609=71 ∧ (1421+1).gcd 5609=79 := by
  refine ⟨by norm_num,by decide,by decide,by decide,?_,?_,by decide,by decide⟩ <;> reduce_mod_char

private theorem finite_order {M : Type*} [Monoid M] {k : ℕ} {x : M}
    (kp : 0<k) (top : x^k=1) (rest : ∀ i : Fin k, 0<(i:ℕ) → x^(i:ℕ)≠1) :
    orderOf x=k := (orderOf_eq_iff kp).mpr ⟨top,fun i lt => rest ⟨i,lt⟩⟩

/-- The unsigned returns have exactly the same period, so extending the
ordinary orbit comparison on 5,609 can never separate these primes. -/
theorem synchronized (j : ℕ) :
    ((3 : ZMod 71)^5608)^(2^j-1)=1 ↔ ((3 : ZMod 79)^5608)^(2^j-1)=1 := by
  have left : (3 : ZMod 71)^5608=29 := by reduce_mod_char
  have right : (3 : ZMod 79)^5608=20 := by reduce_mod_char
  have ol : orderOf (29 : ZMod 71)=35 := finite_order (by decide) (by decide +kernel) (by decide +kernel)
  have oq : orderOf (20 : ZMod 79)=39 := finite_order (by decide) (by decide +kernel) (by decide +kernel)
  have rl : orderOf (2 : ZMod 35)=12 := finite_order (by decide) (by decide +kernel) (by decide +kernel)
  have rq : orderOf (2 : ZMod 39)=12 := finite_order (by decide) (by decide +kernel) (by decide +kernel)
  rw [left,right,←orderOf_dvd_iff_pow_eq_one,←orderOf_dvd_iff_pow_eq_one,ol,oq,mersenne,mersenne,rl,rq]

private abbrev p : ℕ := 2000004719
private abbrev q : ℕ := 2000026079
private abbrev r : ℕ := 1000002359
private abbrev s : ℕ := 1000013039
private abbrev rp : ℕ := 500001179
private abbrev sp : ℕ := 500006519
private abbrev n : ℕ := 4000061596123066801
private abbrev t : ℕ := 250003849757691675

private theorem one_prime_certificate {p r : ℕ} (z : ZMod p) (prime : r.Prime)
    (large : 1<p) (fit : p≤r^2) (order : z^r=1) (unit : Nat.Coprime (z-1).val p) : p.Prime := by
  apply prime_of_partial_order_cover z large prime.pos fit (ps:=[r])
  · simpa using (Covers.cons (n:=1) 1 prime covers_one)
  · exact order
  · intro l hl
    obtain rfl : l=r := List.mem_singleton.mp hl
    simpa [Nat.div_self prime.pos] using unit

private instance rpp : Fact rp.Prime := ⟨by
  apply prime_of_partial_order_cover (495658664 : ZMod rp) (F:=29801) (ps:=[17,1753])
    (by decide) (by decide) (by decide +kernel)
  · exact Covers.cons 1 (by norm_num : Nat.Prime 17)
      (Covers.cons 1 (by norm_num : Nat.Prime 1753) covers_one)
  · unfold rp
    reduce_mod_char
  · intro l hl
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
    rcases hl with rfl|rfl <;> decide +kernel⟩
private instance spp : Fact sp.Prime := ⟨one_prime_certificate 23949265 (by norm_num : Nat.Prime 73079)
  (by decide) (by decide +kernel) (by unfold sp; reduce_mod_char) (by decide +kernel)⟩
private instance rr : Fact r.Prime := ⟨one_prime_certificate 2 rpp.out (by decide) (by decide +kernel)
  (by unfold rp r; reduce_mod_char) (by decide +kernel)⟩
private instance ss : Fact s.Prime := ⟨one_prime_certificate 2 spp.out (by decide) (by decide +kernel)
  (by unfold sp s; reduce_mod_char) (by decide +kernel)⟩
private instance pp : Fact p.Prime := ⟨one_prime_certificate 2 rr.out (by decide) (by decide +kernel)
  (by unfold r p; reduce_mod_char) (by decide +kernel)⟩
private instance qp : Fact q.Prime := ⟨one_prime_certificate 2 ss.out (by decide) (by decide +kernel)
  (by unfold s q; reduce_mod_char) (by decide +kernel)⟩

private theorem period_left : orderOf (2 : ZMod r)=rp := by
  apply orderOf_eq_prime
  · unfold rp r
    reduce_mod_char
  · decide +kernel

private theorem period_right : orderOf (2 : ZMod s)=sp := by
  apply orderOf_eq_prime
  · unfold sp s
    reduce_mod_char
  · decide +kernel

/-- The first profitable squaring for EVERY negative-Jacobi seed
surviving the precheck is 500,001,179 even on this 62-bit product. -/
theorem all_bases (a j : ℕ) (ap : 0<a) (jp : 0<j) (unit : a.Coprime n)
    (neg : jacobiSym (a:ℤ) n= -1) (live : (a^2-1).Coprime n) :
    Separates ((a:ZMod p)^(t*(2^j-1))) ((a:ZMod q)^(t*(2^j-1))) ↔ rp∣j ∨ sp∣j := by
  have prod : p*q=n := by decide +kernel
  have dvp : p∣n := prod ▸ dvd_mul_right ..
  have dvq : q∣n := prod ▸ dvd_mul_left ..
  have up : (a:ZMod p)≠0 := fun h => pp.out.coprime_iff_not_dvd.mp
    (unit.coprime_dvd_right dvp).symm ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp h)
  have uq : (a:ZMod q)≠0 := fun h => qp.out.coprime_iff_not_dvd.mp
    (unit.coprime_dvd_right dvq).symm ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp h)
  have left := safe_order (p:=p) (r:=r) (E:=n-1) (e:=(n-1)/2) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (a:ZMod p) up (live_of_precheck dvp ap live)
  have right := safe_order (p:=q) (r:=s) (E:=n-1) (e:=(n-1)/2) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (a:ZMod q) uq (live_of_precheck dvq ap live)
  have classification := iteration (p:=p) (q:=q) (E:=n-1) (t:=t) (k:=3) (j:=j)
    (by decide) (by decide) (a:=(a:ℤ)) (by rwa [prod])
    (by exact_mod_cast up) (by exact_mod_cast uq) (by decide +kernel)
    (Nat.odd_iff.mpr (by decide +kernel)) jp
  push_cast at classification
  have perP : orderOf (2 : ZMod (orderOf ((a:ZMod p)^(n-1))))=rp :=
    (congrArg (fun v : ℕ => orderOf (2 : ZMod v)) left).trans period_left
  have perQ : orderOf (2 : ZMod (orderOf ((a:ZMod q)^(n-1))))=sp :=
    (congrArg (fun v : ℕ => orderOf (2 : ZMod v)) right).trans period_right
  have changeOrder {u v : ℕ} (h : u=v) : u∣j ↔ v∣j := h ▸ Iff.rfl
  exact classification.trans (or_congr (changeOrder perP) (changeOrder perQ))

/-- Base seven meets the hypotheses; the tested 64-step prefix is empty. -/
theorem seven :
    jacobiSym 7 n= -1 ∧ Nat.Coprime 7 n ∧ Nat.Coprime (7^2-1) n ∧ n=p*q ∧
    Nat.Prime p ∧ Nat.Prime q ∧ 2^61≤n ∧ n<2^62 := by
  exact ⟨by norm_num [n],by decide +kernel,by decide +kernel,by decide +kernel,
    pp.out,qp.out,by decide +kernel,by decide +kernel⟩

end PrimeFactors.BlumSignedPowerExamples
