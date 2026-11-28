import PrimeFactors.FractionalNonunitPrefix
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Finset.Sigma

/-! An exact reweighting of a prefix nonunit count. Multipliers supported on
primes of a public wheel preserve the gcd with a product coprime to the wheel.
Each positive position occurs once in the resulting partition. -/

namespace PrimeFactors.FractionalPrefixWheel

open Finset FractionalNonunitPrefix

/-- All prime factors of the positive multiplier divide W. -/
def Smooth (W s : ℕ) : Prop := ∀ r ∈ s.primeFactors, r ∣ W

noncomputable instance (W s : ℕ) : Decidable (Smooth W s) :=
  inferInstanceAs (Decidable (∀ r ∈ s.primeFactors, r ∣ W))

/-- Positive potential cores up to L. -/
noncomputable def cores (W L : ℕ) : Finset ℕ := (Ioc 0 L).filter W.Coprime

/-- Positive W-smooth multipliers through B. -/
noncomputable def multipliers (W B : ℕ) : Finset ℕ := (Ioc 0 B).filter (Smooth W)

/-- Number of prefix entries represented by one core. -/
noncomputable def weight (W L c : ℕ) : ℕ := (multipliers W (L/c)).card

private theorem smooth_coprime {s W n : ℕ} (sp : 0<s) (hs : Smooth W s)
    (wn : W.Coprime n) : s.Coprime n := by
  by_contra bad
  obtain ⟨r,hr,rs,rn⟩ := Nat.Prime.not_coprime_iff_dvd.mp bad
  exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨r,hr,hs r (Nat.mem_primeFactors.mpr ⟨hr,rs,sp.ne'⟩),rn⟩) wn

/-- A positive position decomposes into a W-smooth multiplier and a core
coprime to W, by removing a shared prime until none remains. -/
theorem decompose (W : ℕ) {t : ℕ} (tp : 0<t) :
    ∃ s c : ℕ, 0<s ∧ 0<c ∧ Smooth W s ∧ W.Coprime c ∧ s*c=t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases done : W.Coprime t
    · exact ⟨1,t,by decide,tp,by simp [Smooth],done,one_mul t⟩
    obtain ⟨r,prime,rw',rt⟩ := Nat.Prime.not_coprime_iff_dvd.mp done
    obtain ⟨u,form⟩ := rt
    have up : 0<u := by by_contra! small; simp [show u=0 by omega] at form; omega
    have small : u<t := by rw [form]; exact lt_mul_of_one_lt_left up prime.one_lt
    obtain ⟨s,c,sp,cp,smooth,cop,prod⟩ := ih u small up
    refine ⟨r*s,c,Nat.mul_pos prime.pos sp,cp,?_,cop,?_⟩
    · intro k hk
      obtain ⟨kp,div,_⟩ := Nat.mem_primeFactors.mp hk
      rcases kp.dvd_mul.mp div with kr|ks
      · exact (Nat.dvd_prime prime |>.mp kr).elim (fun e => False.elim (kp.ne_one e)) (fun e => e ▸ rw')
      · exact smooth k (Nat.mem_primeFactors.mpr ⟨kp,ks,sp.ne'⟩)
    · rw [Nat.mul_assoc,prod,←form]

/-- Two such decompositions of the same integer have the same multiplier
and core. -/
theorem unique {W s c s' c' : ℕ} (sp : 0<s) (sp' : 0<s') (cp : 0<c)
    (hs : Smooth W s) (hs' : Smooth W s') (hc : W.Coprime c) (hc' : W.Coprime c')
    (eqn : s*c=s'*c') : s=s' ∧ c=c' := by
  have cd : c ∣ s'*c' := eqn ▸ dvd_mul_left c s
  have cd' : c' ∣ s*c := eqn.symm ▸ dvd_mul_left c' s'
  have ec := Nat.dvd_antisymm ((smooth_coprime sp' hs' hc).symm.dvd_mul_left.mp cd)
    ((smooth_coprime sp hs hc').symm.dvd_mul_left.mp cd')
  subst c'
  exact ⟨Nat.eq_of_mul_eq_mul_right cp eqn,rfl⟩

/-- Every represented position has the same product gcd as its core. -/
theorem gcd_core {W s c n : ℕ} (sp : 0<s) (hs : Smooth W s) (wn : W.Coprime n) :
    (s*c).gcd n = c.gcd n := by
  rw [Nat.gcd_comm (s*c) n,Nat.gcd_comm c n]
  exact (smooth_coprime sp hs wn).gcd_mul_left_cancel_right c

/-- A core contributes the number of smooth multipliers that still fit in
the prefix. This count requires just one product-coprimality verdict per core. -/
theorem count {W n : ℕ} (wn : W.Coprime n) (L : ℕ) :
    (nonunits n L).card = ∑ c ∈ cores W L, if ¬c.Coprime n then weight W L c else 0 := by
  let bad := (cores W L).filter fun c => ¬c.Coprime n
  let pairs := bad.sigma fun c => multipliers W (L/c)
  have rows (c : ℕ) : c∈bad ↔ 0<c ∧ c≤L ∧ W.Coprime c ∧ ¬c.Coprime n := by
    simp only [bad,cores,mem_filter,mem_Ioc]; tauto
  have parts (s c : ℕ) : s∈multipliers W (L/c) ↔ 0<s ∧ s≤L/c ∧ Smooth W s := by
    simp only [multipliers,mem_filter,mem_Ioc]; tauto
  have eqn : pairs.card = (nonunits n L).card := by
    apply card_bij (fun a _ => a.2*a.1)
    · intro a ha
      obtain ⟨hc,hs⟩ := mem_sigma.mp ha
      obtain ⟨cp,_,cop,badN⟩ := (rows _).mp hc
      obtain ⟨sp,sl,smooth⟩ := (parts ..).mp hs
      have same := gcd_core (c:=a.1) sp smooth wn
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.mul_pos sp cp,(Nat.le_div_iff_mul_le cp).mp sl⟩,fun h => badN (same.symm.trans h)⟩
    · rintro ⟨c,s⟩ hz ⟨c',s'⟩ hz' prod
      obtain ⟨hc,hs⟩ := mem_sigma.mp hz
      obtain ⟨hc',hs'⟩ := mem_sigma.mp hz'
      obtain ⟨cp,_,cop,_⟩ := (rows _).mp hc
      obtain ⟨_,_,cop',_⟩ := (rows _).mp hc'
      obtain ⟨sp,_,smooth⟩ := (parts ..).mp hs
      obtain ⟨sp',_,smooth'⟩ := (parts ..).mp hs'
      obtain ⟨rfl,rfl⟩ := unique sp sp' cp smooth smooth' cop cop' prod
      rfl
    · intro t ht
      obtain ⟨lim,badN⟩ := mem_filter.mp ht
      obtain ⟨tp,tl⟩ := mem_Ioc.mp lim
      obtain ⟨s,c,sp,cp,smooth,cop,rfl⟩ := decompose W tp
      have cL := (Nat.le_mul_of_pos_left c sp).trans tl
      have coreBad : ¬c.Coprime n := fun h => badN (Nat.coprime_mul_iff_left.mpr ⟨smooth_coprime sp smooth wn,h⟩)
      exact ⟨⟨c,s⟩,mem_sigma.mpr ⟨(rows _).mpr ⟨cp,cL,cop,coreBad⟩,
        (parts ..).mpr ⟨sp,(Nat.le_div_iff_mul_le cp).mpr tl,smooth⟩⟩,rfl⟩
  rw [←eqn]
  change (bad.sigma (fun c => multipliers W (L/c))).card=_
  rw [card_sigma]
  simp only [bad,sum_filter,weight]

/-- Core 1 has known gcd one, so its product gcd can be skipped. -/
theorem count_skip_one {W n : ℕ} (wn : W.Coprime n) (L : ℕ) :
    (nonunits n L).card =
      ∑ c ∈ (cores W L).erase 1, if ¬c.Coprime n then weight W L c else 0 := by
  rw [count wn L]
  by_cases has : 1∈cores W L
  · have eqn := sum_erase_add (cores W L) (fun c => if ¬c.Coprime n then weight W L c else 0) has
    simpa using eqn.symm
  · rw [erase_eq_of_not_mem has]

private theorem core_step (W L : ℕ) : (cores W (L+W)).card = (cores W L).card+W.totient := by
  let B := (Ioc L (L+W)).filter W.Coprime
  have split : cores W (L+W) = cores W L ∪ B := by
    rw [cores, cores, ← filter_union, Ioc_union_Ioc_eq_Ioc (Nat.zero_le L) (Nat.le_add_right L W)]
  have separate : Disjoint (cores W L) B := by
    apply disjoint_left.mpr
    intro z left right
    exact (not_lt.mpr ((mem_Ioc.mp (mem_filter.mp left).1).2)) ((mem_Ioc.mp (mem_filter.mp right).1).1)
  have block : Ioc L (L+W) = Ico (L+1) (L+1+W) := by
    ext z
    simp only [mem_Ioc,mem_Ico]
    omega
  have size : B.card=W.totient := by
    dsimp only [B]
    rw [block,Nat.filter_coprime_Ico_eq_totient]
  rw [split,card_union_of_disjoint separate,size]

/-- The exact number of cores, including 1, is a whole-period totient count
and the count in the final incomplete block. -/
theorem core_work (W L : ℕ) : (cores W L).card = (L/W)*W.totient+(cores W (L%W)).card := by
  have calc_blocks (k r : ℕ) : (cores W (r+k*W)).card = k*W.totient+(cores W r).card := by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.succ_mul,←Nat.add_assoc,core_step,ih,Nat.succ_mul]; omega
  simpa only [Nat.mul_comm (L/W) W, Nat.mod_add_div] using calc_blocks (L/W) (L%W)

theorem work_skip_one (W : ℕ) {L : ℕ} (pos : 0<L) :
    ((cores W L).erase 1).card = (L/W)*W.totient+(cores W (L%W)).card-1 := by
  have one : 1∈cores W L := mem_filter.mpr ⟨mem_Ioc.mpr ⟨by decide,pos⟩, Nat.coprime_one_right W⟩
  rw [card_erase_of_mem one,core_work]

/-- The wheel preserves the first nonunit of a semiprime in ascending order. -/
theorem first_bad_core {W p q L : ℕ} (hp : p.Prime) (hq : q.Prime) (order : p<q)
    (wn : W.Coprime (p*q)) :
    (∃ c∈cores W L, ¬c.Coprime (p*q)) ↔ p≤L := by
  constructor
  · rintro ⟨c,hc,bad⟩
    exact (first hp hq order).mp ⟨c,mem_filter.mpr ⟨(mem_filter.mp hc).1,bad⟩⟩
  · intro lim
    have wp := wn.of_dvd_right (dvd_mul_right p q)
    exact ⟨p,mem_filter.mpr ⟨mem_Ioc.mpr ⟨hp.pos,lim⟩,wp⟩,
      Nat.Prime.not_coprime_iff_dvd.mpr ⟨p,hp,dvd_rfl,dvd_mul_right p q⟩⟩

private theorem full_weight {W L c : ℕ} (all : ∀ s ∈ Ioc 0 (L/c), s∣W) :
    weight W L c = L/c := by
  have ok : ∀ s ∈ Ioc 0 (L/c), Smooth W s :=
    fun s hs r hr => (Nat.dvd_of_mem_primeFactors hr).trans (all s hs)
  rw [weight,multipliers,filter_eq_self.mpr ok,Nat.card_Ioc,Nat.sub_zero]

/-- On whole periods 6 keeps two of every six positive positions. The
wheel 30 keeps eight of every thirty. -/
theorem full_blocks (k : ℕ) :
    (cores 6 (6*k)).card=2*k ∧ (cores 30 (30*k)).card=8*k := by
  have w6 : Nat.totient 6=2 := by decide
  have w30 : Nat.totient 30=8 := by decide
  rw [core_work 6 (6*k),core_work 30 (30*k),w6,w30]
  simp [cores,Nat.mul_comm]

set_option exponentiation.threshold 4096 in
/-- A prefix longer than 2²⁰⁴², as in the full-width constant-correction
readout, still has more than 2²⁰⁴⁰ nontrivial wheel-30 cores. This bound is
for a full scan through the cores. -/
theorem wheel30_long {L : ℕ} (long : 2^2042<L) :
    2^2040 < ((cores 30 L).erase 1).card := by
  have blocks : 2^2037+1 ≤ L/30 := (Nat.le_div_iff_mul_le (by decide)).mpr
    ((by decide +kernel : (2^2037+1)*30 ≤ 2^2042).trans long.le)
  have cells := Nat.mul_le_mul_right 8 blocks
  have places : 2^2040+1 < (2^2037+1)*8 := by decide +kernel
  rw [work_skip_one 30 (by omega),show Nat.totient 30=8 by decide]
  omega

/-- The cut at 2183/24 is 90. Testing the 23 nontrivial wheel-30 cores
recovers three prefix nonunits from two contributing cores of weights 2 and 1. -/
theorem example_2183 :
    2183/24=90 ∧ (cores 6 90).card=30 ∧ (cores 30 90).card=24 ∧
    ((cores 30 90).erase 1).card=23 ∧
    ((cores 30 90).filter (fun c => ¬c.Coprime 2183))={37,59} ∧
    weight 30 90 37=2 ∧ weight 30 90 59=1 ∧ (nonunits 2183 90).card=3 := by
  refine ⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    full_weight (by decide +kernel),full_weight (by decide +kernel),?_⟩
  rw [FractionalNonunitPrefix.example_positions]
  decide

end PrimeFactors.FractionalPrefixWheel
