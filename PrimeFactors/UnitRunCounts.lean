import PrimeFactors.Fermat
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Tactic

/-! Exact counts of starting positions for runs of consecutive units modulo a semiprime.
One translated factorial block is cheaper than estimating the total number of clean runs,
and the known factor width gives a deterministic comparator. -/
namespace PrimeFactors.UnitRunCounts

open Finset

set_option exponentiation.threshold 4096

/-- The t consecutive integers immediately after s. -/
noncomputable def block (s t : ℕ) := ∏ i ∈ range t, (s+i+1)

/-- Number-theoretic predicates on starts use only N, the length and the block product. -/
noncomputable def clean (N t : ℕ) := (range N).filter fun s => (block s t).gcd N=1
noncomputable def whole (N t : ℕ) := (range N).filter fun s => N∣block s t
noncomputable def wins (N t : ℕ) := (range N).filter fun s =>
  1<(block s t).gcd N ∧ (block s t).gcd N<N

/-- A length of at most one local period hits zero exactly when the interval wraps. -/
theorem local_hit {p t s : ℕ} (hp : p.Prime) (tp : t≤p) :
    p ∣ block s t ↔ p-t≤s%p := by
  have rem := Nat.mod_lt s hp.pos
  have exchange (i : ℕ) : p∣s%p+i+1 ↔ p∣s+i+1 :=
    (((Nat.mod_modEq s p).add_right i).add_right 1).dvd_iff dvd_rfl
  rw [block,hp.prime.dvd_finset_prod_iff]
  constructor
  · rintro ⟨i,hi,hit⟩
    have ti := mem_range.mp hi
    have eq := Nat.eq_of_dvd_of_lt_two_mul (by omega : s%p+i+1≠0)
      ((exchange i).2 hit) (by omega)
    omega
  · intro h
    let i := p-1-s%p
    have eq : s%p+i+1=p := by dsimp [i]; omega
    exact ⟨i,mem_range.mpr (by omega),(exchange i).1 (by rw [eq])⟩

private noncomputable def cell (p q : ℕ) (A B : Finset ℕ) :=
  (range (p*q)).filter fun s => s%p∈A ∧ s%q∈B

private theorem cell_card {p q : ℕ} (pp : 0<p) (qp : 0<q) (cop : p.Coprime q)
    {A B : Finset ℕ} (ha : ∀ a∈A,a<p) (hb : ∀ b∈B,b<q) :
    (cell p q A B).card=A.card*B.card := by
  rw [←card_product]
  apply card_bij (fun s _ => (s%p,s%q))
  · intro s hs
    exact mem_product.mpr (mem_filter.mp hs).2
  · intro s hs t ht eq
    have both := (Nat.modEq_and_modEq_iff_modEq_mul cop).1
      ⟨congrArg Prod.fst eq,congrArg Prod.snd eq⟩
    exact both.eq_of_lt_of_lt (mem_range.mp (mem_filter.mp hs).1)
      (mem_range.mp (mem_filter.mp ht).1)
  · rintro ⟨a,b⟩ v
    obtain ⟨va,vb⟩ := mem_product.mp v
    let s := Nat.chineseRemainder cop a b
    have pa : s.val%p=a := Eq.trans s.property.1 (Nat.mod_eq_of_lt (ha a va))
    have qb : s.val%q=b := Eq.trans s.property.2 (Nat.mod_eq_of_lt (hb b vb))
    exact ⟨s.val,mem_filter.mpr ⟨mem_range.mpr
      (Nat.chineseRemainder_lt_mul cop a b pp.ne' qp.ne'),by simpa [pa,qb] using And.intro va vb⟩,
      by simp [pa,qb]⟩

/-- All starts avoiding both primes. This exact count contains the unknown prime sum. -/
theorem clean_count {p q t : ℕ} (pp : p.Prime) (qp : q.Prime) (lt : p<q) (tp : t≤p) :
    (clean (p*q) t).card=(p-t)*(q-t) := by
  have eq : clean (p*q) t=cell p q (range (p-t)) (range (q-t)) := by
    ext s
    simp only [clean,cell,mem_filter,mem_range,and_congr_right_iff]
    intro _
    change (block s t).Coprime (p*q) ↔ _
    rw [Nat.coprime_mul_iff_right,(Nat.coprime_comm (n:=block s t) (m:=p)),
      (Nat.coprime_comm (n:=block s t) (m:=q)),pp.coprime_iff_not_dvd,qp.coprime_iff_not_dvd,
      local_hit pp tp,local_hit qp (tp.trans lt.le)]
    omega
  rw [eq,cell_card pp.pos qp.pos (Nat.coprime_primes pp qp |>.2 lt.ne)
    (fun a h => (mem_range.mp h).trans_le (Nat.sub_le ..))
    (fun b h => (mem_range.mp h).trans_le (Nat.sub_le ..))]
  simp

/-- Every period has exactly t² starts whose product contains both primes. -/
theorem whole_count {p q t : ℕ} (pp : p.Prime) (qp : q.Prime) (lt : p<q) (tp : t≤p) :
    (whole (p*q) t).card=t^2 := by
  have cop := (Nat.coprime_primes pp qp).2 lt.ne
  have eq : whole (p*q) t=cell p q (Ico (p-t) p) (Ico (q-t) q) := by
    ext s
    simp only [whole,cell,mem_filter,mem_Ico,and_congr_right_iff]
    intro _
    have dv : p*q∣block s t ↔ p∣block s t ∧ q∣block s t :=
      ⟨fun h => ⟨(dvd_mul_right ..).trans h,(dvd_mul_left ..).trans h⟩,
       fun h => cop.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
    rw [dv,local_hit pp tp,local_hit qp (tp.trans lt.le)]
    have := Nat.mod_lt s pp.pos
    have := Nat.mod_lt s qp.pos
    tauto
  rw [eq,cell_card pp.pos qp.pos cop (fun _ h => (mem_Ico.mp h).2) (fun _ h => (mem_Ico.mp h).2)]
  simp only [Nat.card_Ico]
  rw [show p-(p-t)=t by omega,show q-(q-t)=t by omega,pow_two]

private theorem partition {N : ℕ} (np : 1<N) (t : ℕ) :
    (wins N t).card+(clean N t).card+(whole N t).card=N := by
  have separate : Disjoint (clean N t) (whole N t) := by
    rw [disjoint_left]
    intro s hs hw
    have a := (mem_filter.mp hs).2
    have b := Nat.gcd_eq_right (mem_filter.mp hw).2
    omega
  have cover : wins N t=range N \ (clean N t∪whole N t) := by
    ext s
    simp only [wins,clean,whole,mem_sdiff,mem_union,mem_filter,mem_range]
    have gp := Nat.gcd_pos_of_pos_right (block s t) (by omega : 0<N)
    have gn := Nat.le_of_dvd (by omega : 0<N) (Nat.gcd_dvd_right (block s t) N)
    have iff : N∣block s t ↔ (block s t).gcd N=N :=
      ⟨Nat.gcd_eq_right,fun h => h ▸ Nat.gcd_dvd_left ..⟩
    omega
  have sub : clean N t∪whole N t ⊆ range N := union_subset (filter_subset ..) (filter_subset ..)
  rw [cover,card_sdiff sub,card_range,card_union_of_disjoint separate]
  have size := card_le_card sub
  rw [card_range,card_union_of_disjoint separate] at size
  omega

theorem win_count {p q t : ℕ} (pp : p.Prime) (qp : q.Prime) (lt : p<q) (tp : t≤p) :
    (wins (p*q) t).card=t*(p+q-2*t) := by
  have np : 1<p*q := pp.one_lt.trans_le (Nat.le_mul_of_pos_right p qp.pos)
  have count := partition np t
  rw [clean_count pp qp lt tp,whole_count pp qp lt tp] at count
  have p' := Nat.sub_add_cancel tp
  have q' := Nat.sub_add_cancel (tp.trans lt.le)
  have s' := Nat.sub_add_cancel (show 2*t≤p+q by omega)
  nlinarith only [count,congrArg (fun x => x*(q-t)) p',congrArg (fun x => p*x) q',
    congrArg (fun x => t*x) q',congrArg (fun x => t*x) s']

/-- The dependence of the clean count on the prime sum is linear, with slope t. -/
theorem mass {p q t : ℕ} (pp : p.Prime) (qp : q.Prime) (lt : p<q) (tp : t≤p) :
    (clean (p*q) t).card+t*(p+q)=p*q+t^2 := by
  rw [clean_count pp qp lt tp]
  have p' := Nat.sub_add_cancel tp
  have q' := Nat.sub_add_cancel (tp.trans lt.le)
  nlinarith only [congrArg (fun x => x*(q-t)) p',congrArg (fun x => p*x) q',
    congrArg (fun x => t*x) q']

/-- Absolute count error strictly less than the block length suffices to recover an
even factor sum by rounding, using only integers. -/
theorem readout {N t S C : ℕ} (tp : 0<t) (even : Even S) (count : C+t*S=N+t^2)
    {measured : ℤ} (error : |measured-(C:ℤ)|<(t:ℤ)) :
    2*(((N:ℤ)+(t:ℤ)^2-measured+t)/(2*t))=S := by
  obtain ⟨b,eb⟩ := even
  have eq : (C:ℤ)+t*(S:ℤ)=(N:ℤ)+(t:ℤ)^2 := by exact_mod_cast count
  have s : (S:ℤ)=2*(b:ℤ) := by exact_mod_cast (by omega : S=2*b)
  have den : 0<2*(t:ℤ) := by positivity
  obtain ⟨l,h⟩ := abs_lt.mp error
  rw [s] at eq ⊢
  have bot := (Int.le_ediv_iff_mul_le den).mpr (show (b:ℤ)*(2*t)≤N+(t:ℤ)^2-measured+t by
    nlinarith only [eq,h])
  have top := (Int.ediv_lt_iff_lt_mul den).mpr (show (N:ℤ)+(t:ℤ)^2-measured+t<(b+1)*(2*t) by
    nlinarith only [eq,l])
  omega

/-- Twice the selected width is the least even integer at or above the square root. -/
noncomputable def halfRoot (N : ℕ) := (ceilSqrt N+1)/2

theorem halfRoot_bounds {p q : ℕ} (pp : 0<p) (po : Odd p) (qo : Odd q)
    (order : p<q) (balanced : q≤2*p) :
    p<2*halfRoot (p*q) ∧ 2*halfRoot (p*q)<q ∧ halfRoot (p*q)≤p := by
  obtain ⟨x,px⟩ := po
  obtain ⟨y,qy⟩ := qo
  have lo : p<ceilSqrt (p*q) := by
    by_contra! h
    have bad := ceilSqrt_le_iff.mp h
    have two := Nat.mul_lt_mul_of_pos_left order pp
    nlinarith only [bad,two]
  have hi : ceilSqrt (p*q)≤2*y := by
    apply ceilSqrt_le_iff.mpr
    have s : p+2≤q := by omega
    have a := Nat.mul_le_mul_right q s
    rw [qy] at *
    nlinarith only [a]
  unfold halfRoot
  omega

/-- A uniformly translated block at the public width returns a proper factor on
strictly more than half of all starts. This charges the product of t consecutive terms. -/
theorem more_than_half {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (po : Odd p) (qo : Odd q)
    (lt : p<q) (balanced : q≤2*p) : p*q<2*(wins (p*q) (halfRoot (p*q))).card := by
  let t := halfRoot (p*q)
  obtain ⟨lo,hi,fit⟩ := halfRoot_bounds pp.pos po qo lt balanced
  change p<2*t at lo
  change 2*t<q at hi
  rw [win_count pp qp lt fit]
  change p*q<2*(t*(p+q-2*t))
  have pos := Nat.mul_pos (Nat.sub_pos_of_lt lo) (Nat.sub_pos_of_lt hi)
  zify [lo.le,hi.le,show 2*t≤p+q by omega] at pos ⊢
  nlinarith only [pos]

/-- For the usual common width [B,2B), the single deterministic block from B through
floor(sqrt N) has at most halfRoot N terms and its product gcd is always the smaller prime. -/
theorem deterministic {p q B : ℕ} (pp : p.Prime) (qp : q.Prime) (po : Odd p) (qo : Odd q)
    (lt : p<q) (bp : 0<B) (low : B≤p) (high : q<2*B) :
    let width := (p*q).sqrt+1-B
    width≤halfRoot (p*q) ∧ (block (B-1) width).gcd (p*q)=p := by
  let w := (p*q).sqrt+1-B
  change w≤_ ∧ _
  have lowroot : p≤(p*q).sqrt := Nat.le_sqrt'.mpr (by simpa [pow_two] using Nat.mul_le_mul_left p lt.le)
  have him : (p*q).sqrt<q := Nat.sqrt_lt'.mpr (by simpa [pow_two] using Nat.mul_lt_mul_of_pos_right lt qp.pos)
  obtain ⟨_,cut,_⟩ := halfRoot_bounds pp.pos po qo lt (by omega)
  have rc : (p*q).sqrt≤ceilSqrt (p*q) := by
    have a := Nat.sqrt_le' (p*q)
    have b := ceilSqrt_le_iff.mp (le_refl (ceilSqrt (p*q)))
    exact (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp (a.trans b)
  have le : (p*q).sqrt≤2*halfRoot (p*q) := by unfold halfRoot; omega
  have access : p∣block (B-1) w := by
    rw [block,pp.prime.dvd_finset_prod_iff]
    refine ⟨p-B,mem_range.mpr (by dsimp only [w]; omega),?_⟩
    rw [show B-1+(p-B)+1=p by omega]
  have miss : ¬q∣block (B-1) w := by
    rw [block,qp.prime.dvd_finset_prod_iff]
    rintro ⟨i,ii,qd⟩
    have small := mem_range.mp ii
    dsimp only [w] at small
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) qd
  refine ⟨by dsimp only [w]; omega,?_⟩
  exact (Nat.gcd_comm (block (B-1) w) (p*q)).trans
    ((congrArg (fun a : ℕ => a.gcd (block (B-1) w)) (Nat.mul_comm p q)).trans
      (Nat.gcd_mul_of_coprime_of_dvd (qp.coprime_iff_not_dvd.mpr miss) access))

/-- A literal budget of t terms also limits the fraction of uniform starts that split.
With B≤p≤q the fraction is at most 2t/B; for positive t the inequality is strict. -/
theorem trial_budget {p q t B : ℕ} (pp : p.Prime) (qp : q.Prime) (lt : p<q) (low : B≤p)
    (bp : 0<B) (tp : 0<t) (fit : t≤p) :
    B*(wins (p*q) t).card<2*t*(p*q) := by
  rw [win_count pp qp lt fit]
  have sum : B*(p+q)≤2*(p*q) := by
    have l := Nat.mul_le_mul_right q low
    have r := Nat.mul_le_mul_left p (low.trans lt.le)
    nlinarith only [l,r]
  have drop := Nat.mul_lt_mul_of_pos_left
    (show p+q-2*t<p+q by omega) (Nat.mul_pos bp tp)
  have cap := Nat.mul_le_mul_right t sum
  nlinarith only [drop,cap]

/-- Even 2^40 consecutive terms on one uniformly chosen starting residue split on
fewer than one in 2^982 starts for any fixed pair of 1024-bit primes. -/
theorem trillion_trial {p q t : ℕ} (pp : p.Prime) (qp : q.Prime) (lt : p<q)
    (low : 2^1023≤p) (tp : 0<t) (budget : t≤2^40) :
    2^982*(wins (p*q) t).card<p*q := by
  have ub := trial_budget pp qp lt low (by decide) tp (by omega)
  have cap := Nat.mul_le_mul_right (p*q) (Nat.mul_le_mul_left 2 budget)
  have scale : (2:ℕ)^1023=(2*2^40)*2^982 := by decide +kernel
  rw [scale] at ub
  have bound := ub.trans_le cap
  rw [Nat.mul_assoc] at bound
  exact Nat.lt_of_mul_lt_mul_left bound

/-- At 1024-bit balanced prime widths, each half-probability experiment uses more
than 2^1022 terms in the literal block product. Faster factorial algorithms can evaluate
products without taking one step per term. -/
theorem full_width {p q : ℕ} (pp : p.Prime) (po : Odd p) (qo : Odd q)
    (lt : p<q) (low : 2^1023≤p) (high : q<2^1024) :
    2^1022<halfRoot (p*q) := by
  have bounds := halfRoot_bounds pp.pos po qo lt (by omega)
  omega

/-- Of the 143 six-term blocks, 35 are coprime to 143 and 72 produce a proper gcd.
With the stated four-bit width, the deterministic block from 8 through 11 gives 11. -/
theorem example143 :
    halfRoot 143=6 ∧ (clean 143 6).card=35 ∧ (wins 143 6).card=72 ∧
    (whole 143 6).card=36 ∧ (block 7 4).gcd 143=11 := by decide +kernel

end PrimeFactors.UnitRunCounts
