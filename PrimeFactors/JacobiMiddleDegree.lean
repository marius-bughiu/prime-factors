import PrimeFactors.JacobiMomentRecurrence
import PrimeFactors.ShortPascalRow
import PrimeFactors.FactorSum
import Mathlib.Data.Nat.Choose.Central

/-! A public even degree in the interval between the two odd prime
predecessors. The complete Jacobi moment isolates the larger prime throughout
this interval. At an interior degree the ordinary central binomial coefficient
already isolates the smaller prime. -/

namespace PrimeFactors.JacobiMiddleDegree

open Finset ProjectiveWordMoments JacobiMomentRecurrence
open private PrimeFactors.ProjectiveWordMoments.signed_moment from PrimeFactors.ProjectiveWordMoments

/-- At a degree below the prime predecessor, its signed component is the
universal central coefficient. -/
theorem component_low {p : ℕ} [Fact p.Prime] (odd : p≠2) (k : ℕ) (small : k<p-1) :
    component p k = (central k : ZMod p) := by
  rw [component,PrimeFactors.ProjectiveWordMoments.signed_moment odd k small,neg_neg]

/-- Positive degrees above the predecessor can be reduced by one full
prime-field period, with the zero field element accounted for. -/
theorem component_subtract_period {p k : ℕ} [Fact p.Prime] (hi : p-1<k) :
    component p k = component p (k-(p-1)) := by
  unfold component
  congr 1
  apply sum_congr rfl
  intro x _
  congr 1
  by_cases zero : x=0
  · simp [zero,show k≠0 by omega,show k-(p-1)≠0 by omega]
  · have unit : x^(p-1)=1 := by simpa only [ZMod.card] using FiniteField.pow_card_sub_one_eq_one x zero
    conv_lhs => rw [show k=k-(p-1)+(p-1) by omega,pow_add,unit,mul_one]

private theorem central_dvd {p k : ℕ} (pp : p.Prime) (even : k%2=0) (lo : p≤k) (hi : k<2*p) :
    p ∣ central k := by
  rw [central,if_pos even]
  exact (ShortPascalRow.column_iff pp (by omega) lo hi).mpr ⟨by omega,by omega⟩

/-- For each even interior index the coefficient alone has gcd p. -/
theorem central_gcd {p q k : ℕ} (pp : p.Prime) (qp : q.Prime) (balanced : q<2*p)
    (lo : p-1<k) (hi : k<q-1) (even : k%2=0) :
    (central k).gcd (p*q) = p := by
  apply NormBatchGCD.one_batch qp (central_dvd pp even (by omega) (by omega))
  rw [central,if_pos even]
  exact ShortPascalRow.prime_above_row qp (by omega) (by omega)

/-- Every even degree between the predecessors, including the smaller endpoint,
isolates the larger prime through the canonical Jacobi discrepancy. -/
theorem interval_gcd {p q k : ℕ} [Fact p.Prime] [Fact q.Prime] (oddp : p≠2) (oddq : q≠2)
    (ordered : p<q) (balanced : q<2*p) (lo : p-1≤k) (hi : k<q-1) (even : k%2=0) :
    (p*q).gcd (moment (p*q) k - (central k : ZMod (p*q))).val = q := by
  have pp : p.Prime := Fact.out
  have qp : q.Prime := Fact.out
  have cop := (Nat.coprime_primes pp qp).mpr ordered.ne
  rcases lo.eq_or_lt with rfl | interior
  · exact boundary_gcd cop oddp oddq ordered
  let r := k-(p-1)
  have rsmall : r<p-1 := by dsimp [r]; omega
  obtain ⟨a,pa⟩ := pp.odd_of_ne_two oddp
  have re : r%2=0 := by dsimp [r]; omega
  have nonzero : (central r : ZMod p) ≠ 0 := by
    rw [ne_eq,ZMod.natCast_zmod_eq_zero_iff_dvd,central,if_pos re]
    exact ShortPascalRow.prime_above_row pp (by omega) (by omega)
  have cz : (central k : ZMod p)=0 :=
    (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mpr (central_dvd pp even (by omega) (by omega))
  let d := moment (p*q) k - (central k : ZMod (p*q))
  have crt : ZMod.chineseRemainder cop d = ((central r : ZMod p),0) := by
    change ZMod.chineseRemainder cop (_ - _) = _
    rw [map_sub,components cop oddp oddq,map_natCast]
    change ((component p k - (central k : ZMod p)),(component q k - (central k : ZMod q))) = _
    rw [component_subtract_period interior,component_low oddp _ rsmall,component_low oddq k hi,cz,sub_zero,sub_self]
  have coords : ((d.val : ZMod p),(d.val : ZMod q)) = ((central r : ZMod p),0) := calc
    _ = ZMod.chineseRemainder cop (d.val : ZMod (p*q)) := by rw [map_natCast]; rfl
    _ = _ := by rw [ZMod.natCast_zmod_val,crt]
  have qdiv := (ZMod.natCast_zmod_eq_zero_iff_dvd d.val q).mp (congrArg Prod.snd coords)
  have pnot : ¬p ∣ d.val := by
    intro dvd
    exact nonzero ((congrArg Prod.fst coords).symm.trans ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mpr dvd))
  change (p*q).gcd d.val = q
  exact Nat.gcd_mul_of_coprime_of_dvd (pp.coprime_iff_not_dvd.mpr pnot) qdiv

/-- Largest even index at or below the ordinary integer square root. -/
def degree (n : ℕ) := 2*(n.sqrt/2)

theorem degree_interval {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (oddp : p≠2)
    (oddq : q≠2) (ordered : p<q) :
    p-1 ≤ degree (p*q) ∧ degree (p*q) < q-1 ∧ degree (p*q)%2 = 0 := by
  obtain ⟨a,pa⟩ := pp.odd_of_ne_two oddp
  obtain ⟨b,qb⟩ := qp.odd_of_ne_two oddq
  have bot : p ≤ (p*q).sqrt := Nat.le_sqrt.mpr (Nat.mul_le_mul_left _ ordered.le)
  have sep : p+2≤q := by omega
  have qq : q=q-1+1 := by omega
  have upper : p*q < (q-1)*(q-1) := by
    have key := Nat.mul_le_mul_right q sep
    nth_rw 1 [qq] at key
    nlinarith only [key,qq]
  have top := Nat.sqrt_lt.mpr upper
  unfold degree
  omega

/-- A single degree computed from N suffices without knowing either prime. -/
theorem public_gcd {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (oddp : p≠2) (oddq : q≠2)
    (ordered : p<q) (balanced : q<2*p) :
    (p*q).gcd (moment (p*q) (degree (p*q)) - (central (degree (p*q)) : ZMod (p*q))).val = q := by
  obtain ⟨lo,hi,ev⟩ := degree_interval Fact.out Fact.out oddp oddq ordered
  exact interval_gcd oddp oddq ordered balanced lo hi ev

/-- The public degree hits the boundary exactly for twin primes. -/
theorem endpoint_iff {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (oddp : p≠2) (oddq : q≠2)
    (ordered : p<q) : degree (p*q)=p-1 ↔ q=p+2 := by
  obtain ⟨a,pa⟩ := pp.odd_of_ne_two oddp
  obtain ⟨b,qb⟩ := qp.odd_of_ne_two oddq
  have bot : p≤(p*q).sqrt := Nat.le_sqrt.mpr (Nat.mul_le_mul_left _ ordered.le)
  have ppos := pp.one_lt
  unfold degree
  constructor
  · intro endpoint
    have top := Nat.sqrt_lt.mp (show (p*q).sqrt<p+1 by omega)
    by_contra wrong
    have wide := Nat.mul_le_mul_left p (show p+3≤q by omega)
    nlinarith only [top,wide,ppos]
  · intro twin
    have top : (p*q).sqrt<p+1 := Nat.sqrt_lt.mpr (by rw [twin]; nlinarith)
    omega

/-- Direct witnesses of twinhood from the factors and of the factorization from
the product: its successor is a square, whose two neighbors multiply to N. -/
theorem twin_square {p q : ℕ} (twin : q=p+2) :
    p*q+1=(p+1)^2 ∧ (p*q+1).sqrt-1=p ∧ (p*q+1).sqrt+1=q := by
  have eq : p*q+1=(p+1)^2 := by rw [twin]; ring
  rw [eq,Nat.sqrt_eq']
  omega

/-- For the promised semiprime, a square successor characterizes the twin case. -/
theorem square_iff_twins {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ordered : p<q) :
    (p*q+1).sqrt^2=p*q+1 ↔ q=p+2 := by
  constructor
  · intro square
    generalize h : (p*q+1).sqrt=r at square
    cases r with
    | zero => simp at square
    | succ a =>
      have lower := pp.one_lt
      have prod : a*(a+2)=p*q := by nlinarith only [square]
      have one : 1<a := by
        by_contra! low
        have small := Nat.mul_le_mul low (show a+2≤3 by omega)
        have big := Nat.mul_le_mul (show 2≤p by omega) (show 3≤q by omega)
        omega
      obtain ⟨left,right⟩ := ordered_semiprime_pair_unique pp qp ordered.le (by omega) one prod
      omega
  · intro twin
    rw [(twin_square twin).1,Nat.sqrt_eq']

/-- A product-only baseline first tries the twin square, then the ordinary
central coefficient at the same public degree. -/
def ordinary (n : ℕ) :=
  if (n+1).sqrt^2=n+1 then (n+1).sqrt-1 else (central (degree n)).gcd n

theorem ordinary_correct {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (oddp : p≠2)
    (oddq : q≠2) (ordered : p<q) (balanced : q<2*p) : ordinary (p*q)=p := by
  by_cases twin : q=p+2
  · rw [ordinary,if_pos ((square_iff_twins pp qp ordered).mpr twin)]
    exact (twin_square twin).2.1
  · rw [ordinary,if_neg (fun square => twin ((square_iff_twins pp qp ordered).mp square))]
    have away := (endpoint_iff pp qp oddp oddq ordered).not.mpr twin
    obtain ⟨lo,hi,even⟩ := degree_interval pp qp oddp oddq ordered
    exact central_gcd pp qp balanced (lt_of_le_of_ne lo (Ne.symm away)) hi even

/-- In an increasing scan beginning at x=3, the two positive factors of
the Jacobi discriminant are both below p until x=p−2. At that row their
gcd with the product reveals p exactly. -/
theorem discriminant_scan {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (large : 7≤p)
    (ordered : p<q) :
    (∀ x : ℕ, 3≤x → x<p-2 → (p*q).gcd ((x-2)*(x+2))=1) ∧
    (p*q).gcd (((p-2)-2)*((p-2)+2))=p := by
  constructor
  · intro x start before
    have clean {r : ℕ} (prime : r.Prime) (lo : p≤r) : r.Coprime ((x-2)*(x+2)) := by
      apply prime.coprime_iff_not_dvd.mpr
      intro hit
      rcases prime.dvd_mul.mp hit with left | right
      · exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) left
      · exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) right
    exact (Nat.coprime_mul_iff_left.mpr ⟨clean pp le_rfl,clean qp ordered.le⟩).gcd_eq_one
  · rw [show p-2+2=p by omega,Nat.gcd_comm]
    apply NormBatchGCD.one_batch qp (dvd_mul_left ..)
    intro hit
    rcases qp.dvd_mul.mp hit with left | right
    · exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) left
    · exact Nat.not_dvd_of_pos_of_lt pp.pos ordered right

/-- The factorial at the integer square root already contains p and has
no multiple of q, for every product of two distinct ordered primes. -/
theorem factorial_gcd {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ordered : p<q) :
    (p*q).gcd (p*q).sqrt.factorial=p := by
  have low : p≤(p*q).sqrt := Nat.le_sqrt.mpr (Nat.mul_le_mul_left _ ordered.le)
  have high : (p*q).sqrt<q := Nat.sqrt_lt.mpr (Nat.mul_lt_mul_of_pos_right ordered qp.pos)
  rw [Nat.gcd_comm]
  exact NormBatchGCD.one_batch qp (Nat.dvd_factorial pp.pos low)
    (fun hit => (not_le_of_gt high) (qp.dvd_factorial.mp hit))

/-- Computing the central coefficient as an exact integer requires more
than floor(√N/2) bits once that half-index is at least four. The bound
measures storage for the unreduced integer. -/
theorem exact_coefficient_size (n : ℕ) (large : 4≤n.sqrt/2) :
    2^(n.sqrt/2) < central (degree n) := by
  let m := n.sqrt/2
  have eq : central (degree n)=m.centralBinom := by
    change (if (2*m)%2=0 then (2*m).choose (2*m/2) else 0)=m.centralBinom
    rw [if_pos (by omega),Nat.mul_div_cancel_left m (by decide)]
    rfl
  rw [eq]
  change 2^m < m.centralBinom
  by_contra! small
  have ub := Nat.mul_le_mul (show m≤2^m from Nat.lt_two_pow_self.le) small
  rw [←mul_pow,show (2:ℕ)*2=4 by decide] at ub
  exact (not_le_of_gt (Nat.four_pow_lt_mul_centralBinom m large)) ub

/-- Prime certificate for the additional middle-degree fixture. -/
theorem control_493 : ExactFactorization 493 [17,29] ∧ degree 493=22 ∧ ordinary 493=17 := by
  refine ⟨by norm_num [ExactFactorization],by decide +kernel,?_⟩
  exact ordinary_correct (p:=17) (q:=29) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

end PrimeFactors.JacobiMiddleDegree
