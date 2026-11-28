import PrimeFactors.CircleMarkSharedOccurrence
import PrimeFactors.NormBatchGCD

/-! Changing the public Jacobi score with the single coordinate 1 means that
a unit residue is one at one of the primes. The two resulting lines meet at
the public residue 1. Everywhere else on them a single gcd gives a prime. -/
namespace PrimeFactors.CircleMarkSingletonChanges

open Finset CircleMarkSharedScores CircleMarkSharedOccurrence CircleMarkTargetFrequency
open scoped Classical

noncomputable abbrev changes (n : ℕ) [NeZero n] := changed n {{1}}

def probe (n : ℕ) (t : ZMod n) : ℕ := n.gcd ((t.val : ℤ)-1).natAbs

/-- Exactly the units that are one at one of the two primes change. -/
theorem mem_changes {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (t : ZMod (p*q)) :
    t∈changes (p*q) ↔ (t.val:ZMod p)≠0 ∧ (t.val:ZMod q)≠0 ∧
      ((t.val:ZMod p)=1 ∨ (t.val:ZMod q)=1) := by
  have one (r : ℕ) [Fact r.Prime] : covered r {1} = {1} := by simp [covered]
  rw [changes,changed_iff]
  have union : ({{1}} : Finset (Finset ℕ)).biUnion id = {1} := by simp
  simp only [union,score_eq_of_covered,one,mem_singleton]
  by_cases hit : (t.val:ZMod p)=1 ∨ (t.val:ZMod q)=1
  · rw [if_pos hit,ExtensionTrace.jacobi_crt,ne_comm]
    simp only [Int.cast_natCast,ne_eq,mul_eq_zero,quadraticChar_eq_zero_iff,not_or,hit,and_true]
  · rw [if_neg hit]
    simp only [hit,and_false,not_true_eq_false,ne_eq,eq_self]

private theorem coordinate_dvd {r n : ℕ} (t : ZMod n) :
    r ∣ ((t.val : ℤ)-1).natAbs ↔ (t.val : ZMod r)=1 := by
  rw [←Int.natCast_dvd,←ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_sub,Int.cast_natCast,Int.cast_one,sub_eq_zero]

private theorem both {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (t : ZMod (p*q)) :
    (t.val:ZMod p)=1 ∧ (t.val:ZMod q)=1 ↔ t=1 := by
  let e := ZMod.chineseRemainder ((Nat.coprime_primes hp.out hq.out).mpr diff)
  have co : e t = (t.val : ℕ) := by rw [←map_natCast e,ZMod.natCast_zmod_val]
  rw [←e.injective.eq_iff,co,map_one]
  constructor
  · rintro ⟨a,b⟩
    exact Prod.ext a b
  · intro h
    exact ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩

private theorem probe_one {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] :
    probe (p*q) 1 = p*q := by
  have large : 1<p*q := one_lt_mul_of_lt_of_le hp.out.one_lt hq.out.one_lt.le
  have val : (1:ZMod (p*q)).val=1 := by
    simpa only [Nat.cast_one] using (ZMod.val_natCast_of_lt large)
  simp [probe,val]

/-- Every changed residue has a prescribed gcd, with the sole trivial gcd
at the public overlap t=1. -/
theorem probe_eq {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (diff : p≠q)
    {t : ZMod (p*q)} (change : t∈changes (p*q)) :
    probe (p*q) t = if t=1 then p*q else if (t.val:ZMod p)=1 then p else q := by
  obtain ⟨_,_,hit⟩ := (mem_changes t).mp change
  split_ifs with trivial first
  · subst t
    exact probe_one
  · have other : (t.val:ZMod q)≠1 := fun h => trivial ((both diff t).mp ⟨first,h⟩)
    exact (Nat.gcd_comm ..).trans (NormBatchGCD.one_batch hq.out ((coordinate_dvd t).mpr first)
      (fun dv => other ((coordinate_dvd t).mp dv)))
  · have second := hit.resolve_left first
    rw [probe,Nat.gcd_comm]
    refine (congrArg (Nat.gcd ((t.val:ℤ)-1).natAbs) (Nat.mul_comm p q)).trans ?_
    exact NormBatchGCD.one_batch hp.out ((coordinate_dvd t).mpr second)
      (fun dv => first ((coordinate_dvd t).mp dv))

/-- Every changed residue other than 1 yields a proper divisor immediately. -/
theorem proper {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (diff : p≠q)
    {t : ZMod (p*q)} (change : t∈changes (p*q)) (nontrivial : t≠1) :
    (probe (p*q) t=p ∨ probe (p*q) t=q) ∧ 1<probe (p*q) t ∧ probe (p*q) t<p*q := by
  rw [probe_eq diff change,if_neg nontrivial]
  split_ifs
  · exact ⟨Or.inl rfl,hp.out.one_lt,lt_mul_of_one_lt_right hp.out.pos hq.out.one_lt⟩
  · exact ⟨Or.inr rfl,hq.out.one_lt,lt_mul_of_one_lt_left hq.out.pos hp.out.one_lt⟩

private theorem one_changed {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] :
    (1:ZMod (p*q))∈changes (p*q) := by
  rw [mem_changes]
  have large : 1<p*q := one_lt_mul_of_lt_of_le hp.out.one_lt hq.out.one_lt.le
  have val : (1:ZMod (p*q)).val=1 := by
    simpa only [Nat.cast_one] using (ZMod.val_natCast_of_lt large)
  simp [val]

/-- The complete set of trivial changed residues is the singleton {1}. -/
theorem trivial_set {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q) :
    (changes (p*q)).filter (fun t => probe (p*q) t=p*q) = {1} := by
  ext t
  rw [mem_filter,mem_singleton]
  constructor
  · rintro ⟨changed,eqn⟩
    by_contra ne
    exact (proper diff changed ne).2.2.ne eqn
  · rintro rfl
    exact ⟨one_changed,probe_one⟩

private theorem first_iff {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (t : ZMod (p*q)) :
    t∈changes (p*q) ∧ probe (p*q) t=p ↔
      (t.val:ZMod p)=1 ∧ (t.val:ZMod q)≠0 ∧ (t.val:ZMod q)≠1 := by
  have below := lt_mul_of_one_lt_right hp.out.pos hq.out.one_lt
  constructor
  · rintro ⟨hit,found⟩
    obtain ⟨_,unit,line⟩ := (mem_changes t).mp hit
    rw [probe_eq diff hit] at found
    split_ifs at found with one atP
    · omega
    · exact ⟨atP,unit,fun eqn => one ((both diff t).mp ⟨atP,eqn⟩)⟩
    · omega
  · rintro ⟨atP,unit,other⟩
    have hit := (mem_changes t).mpr ⟨atP ▸ one_ne_zero,unit,Or.inl atP⟩
    have notOne : t≠1 := fun one => other (((both diff t).mpr one).2)
    exact ⟨hit,by rw [probe_eq diff hit,if_neg notOne,if_pos atP]⟩

private theorem second_iff {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (t : ZMod (p*q)) :
    t∈changes (p*q) ∧ probe (p*q) t=q ↔
      ((t.val:ZMod p)≠0 ∧ (t.val:ZMod p)≠1) ∧ (t.val:ZMod q)=1 := by
  have below := lt_mul_of_one_lt_left hq.out.pos hp.out.one_lt
  constructor
  · rintro ⟨hit,found⟩
    obtain ⟨unit,_,line⟩ := (mem_changes t).mp hit
    rw [probe_eq diff hit] at found
    split_ifs at found with one atP
    · omega
    · omega
    · exact ⟨⟨unit,atP⟩,line.resolve_left atP⟩
  · rintro ⟨⟨unit,other⟩,atQ⟩
    have hit := (mem_changes t).mpr ⟨unit,atQ ▸ one_ne_zero,Or.inr atQ⟩
    have notOne : t≠1 := fun one => other (((both diff t).mpr one).1)
    exact ⟨hit,by rw [probe_eq diff hit,if_neg notOne,if_neg other]⟩

private theorem count_rectangle {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (S : Finset (ZMod (p*q))) (A : Finset (ZMod p)) (B : Finset (ZMod q))
    (rectangle : ∀t, t∈S ↔ (t.val:ZMod p)∈A ∧ (t.val:ZMod q)∈B) :
    S.card=A.card*B.card := by
  let e := ZMod.chineseRemainder ((Nat.coprime_primes hp.out hq.out).mpr diff)
  have mapped : S.map e.toEquiv.toEmbedding=A×ˢB := by
    ext z
    obtain ⟨t,rfl⟩ := e.surjective z
    have co : e t = (t.val : ℕ) := by rw [←map_natCast e,ZMod.natCast_zmod_val]
    rw [mem_map_equiv]
    change e.symm (e t) ∈ S ↔ _
    rw [e.symm_apply_apply,co,mem_product]
    exact rectangle t
  rw [←card_product,mapped.symm,card_map]

/-- Of the changed scores, exactly q−2 recover p and exactly p−2 recover q. -/
theorem counts {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (diff : p≠q) :
    ((changes (p*q)).filter (fun t => probe (p*q) t=p)).card=q-2 ∧
    ((changes (p*q)).filter (fun t => probe (p*q) t=q)).card=p-2 := by
  let others (r : ℕ) [Fact r.Prime] : Finset (ZMod r) := (univ.erase 0).erase 1
  have size (r : ℕ) [Fact r.Prime] : (others r).card=r-2 := by
    simp [others,card_erase_of_mem]
    omega
  constructor
  · rw [count_rectangle diff _ {1} (others q) (fun t => ?_),card_singleton,one_mul,size]
    simpa only [mem_filter,others,mem_singleton,mem_erase,mem_univ,and_true,and_comm
      (a:=(t.val:ZMod q)≠1)] using first_iff diff t
  · rw [count_rectangle diff _ (others p) {1} (fun t => ?_),card_singleton,mul_one,size]
    simpa only [mem_filter,others,mem_singleton,mem_erase,mem_univ,and_true,and_comm
      (a:=(t.val:ZMod p)≠1)] using second_iff diff t

/-- In increasing representative order, the first changed residue after 1
is p+1 and its public gcd already gives p. -/
theorem first_after_one {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) :
    let a : ZMod (p*q) := ((p+1:ℕ) : ZMod (p*q))
    a.val=p+1 ∧ a∈changes (p*q) ∧ probe (p*q) a=p ∧
      ∀t∈changes (p*q), 1<t.val → p+1≤t.val := by
  let a : ZMod (p*q) := ((p+1:ℕ) : ZMod (p*q))
  have room : p+1<q := by
    obtain ⟨i,hi⟩ := hp.out.odd_of_ne_two op
    obtain ⟨j,hj⟩ := hq.out.odd_of_ne_two oq
    omega
  have val : a.val=p+1 := ZMod.val_natCast_of_lt (room.trans (lt_mul_of_one_lt_left hq.out.pos hp.out.one_lt))
  have atP : (a.val:ZMod p)=1 := by rw [val,Nat.cast_add_one,ZMod.natCast_self,zero_add]
  have qval : (a.val:ZMod q).val=p+1 := by rw [val,ZMod.val_natCast_of_lt room]
  have nonzero : (a.val:ZMod q)≠0 := by intro h; rw [h,ZMod.val_zero] at qval; omega
  have notOne : (a.val:ZMod q)≠1 := by
    intro h
    have one : (1:ZMod q).val=1 := by simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt hq.out.one_lt
    rw [h,one] at qval
    have := hp.out.two_le
    omega
  have found := (first_iff order.ne a).mpr ⟨atP,nonzero,notOne⟩
  refine ⟨val,found.1,found.2,?_⟩
  intro t ht large
  have pred : ((t.val:ℤ)-1).natAbs=t.val-1 := by
    rw [show ((t.val:ℤ)-1)=((t.val-1:ℕ):ℤ) by rw [Nat.cast_sub (by omega : 1≤t.val),Nat.cast_one],
      Int.natAbs_natCast]
  rcases ((mem_changes t).mp ht).2.2 with h|h
  · have divides := (coordinate_dvd t).mpr h
    rw [pred] at divides
    have := Nat.le_of_dvd (by omega : 0<t.val-1) divides
    omega
  · have divides := (coordinate_dvd t).mpr h
    rw [pred] at divides
    have := Nat.le_of_dvd (by omega : 0<t.val-1) divides
    omega

/-- At 2183 the sole trivial change is joined by 57 witnesses for 37 and 35 for 59. -/
theorem example_2183 :
    ((changes 2183).filter (fun t => probe 2183 t=2183)).card=1 ∧
    ((changes 2183).filter (fun t => probe 2183 t=37)).card=57 ∧
    ((changes 2183).filter (fun t => probe 2183 t=59)).card=35 := by
  letI : Fact (Nat.Prime 37) := ⟨by decide⟩
  letI : Fact (Nat.Prime 59) := ⟨by decide⟩
  have diff : 37≠59 := by decide
  have trivial := congrArg Finset.card (trivial_set diff)
  have nontrivial := counts diff
  norm_num only [card_singleton,Nat.reduceMul,Nat.reduceSub] at trivial nontrivial
  exact ⟨trivial,nontrivial⟩

end PrimeFactors.CircleMarkSingletonChanges
