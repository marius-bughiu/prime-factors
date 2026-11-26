import PrimeFactors.FixedDivisorSignatures
import PrimeFactors.Subgroup
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-! A negative Jacobi symbol selects a separating gcd product using only the
public modulus and its factor interval. The size of the selected product is
a separate cost. -/
namespace PrimeFactors.CharacterDivisorColumn

open Finset

noncomputable def odds (B : ℕ) := (Ico B (2*B)).filter fun a => a%2=1

noncomputable def entries (B : ℕ) (d ε : ℤ) := (odds B).filter fun a => jacobiSym d a=ε

noncomputable def product (B : ℕ) (d ε : ℤ) : ℕ := ∏ a ∈ entries B d ε, a

theorem prime_dvd_iff {p B : ℕ} (pp : p.Prime) (pl : B≤p) (ph : p<2*B)
    (po : p%2=1) (d ε : ℤ) : p ∣ product B d ε ↔ jacobiSym d p=ε := by
  have mem : p ∈ odds B := mem_filter.mpr ⟨mem_Ico.mpr ⟨pl,ph⟩,po⟩
  have unique (a : ℕ) (ha : a∈odds B) (dvd : p∣a) : a=p := by
    obtain ⟨lo,hi⟩ := mem_Ico.mp (mem_filter.mp ha).1
    exact Nat.eq_of_dvd_of_lt_two_mul (by omega) dvd (by omega)
  simpa only [FixedDivisorSignatures.column, decide_eq_true_eq, product, entries] using
    FixedDivisorSignatures.column_dvd pp mem unique (fun a => decide (jacobiSym d a=ε))

/-- Each of the two signs selects exactly one of the primes. The certificate
of opposite local signs is tested modulo the public product. -/
theorem split {p q B : ℕ} (pp : p.Prime) (qp : q.Prime) (pl : B≤p) (ph : p<2*B)
    (ql : B≤q) (qh : q<2*B) (po : p%2=1) (qo : q%2=1) {d ε : ℤ}
    (select : jacobiSym d (p*q)=-1) (sign : ε=1 ∨ ε= -1) :
    (product B d ε).gcd (p*q)=p ∨ (product B d ε).gcd (p*q)=q := by
  apply FixedDivisorSignatures.separates pp qp
  rw [prime_dvd_iff pp pl ph po,prime_dvd_iff qp ql qh qo]
  rw [jacobiSym.mul_right' _ pp.ne_zero qp.ne_zero] at select
  rcases jacobiSym.trichotomy d p with hp|hp|hp <;>
    rcases jacobiSym.trichotomy d q with hq|hq|hq <;> rcases sign with rfl|rfl <;>
    simp_all

/-- Odd denominators bearing the same residue modulo 4|d| have the same
Jacobi symbol, permitting arithmetic-progression products and exact counts. -/
theorem periodic {a b : ℕ} (oa : Odd a) (ob : Odd b) (d : ℤ)
    (same : a % (4*d.natAbs) = b % (4*d.natAbs)) : jacobiSym d a=jacobiSym d b := by
  rw [jacobiSym.mod_right d oa,jacobiSym.mod_right d ob,same]

/-- The cheaper sign uses at most half of the odd denominators, even when
some candidates have symbol zero. -/
theorem cheaper (B : ℕ) (d : ℤ) : ∃ ε : ℤ, (ε=1 ∨ ε= -1) ∧
    2*(entries B d ε).card ≤ (odds B).card := by
  let P := entries B d 1
  let M := entries B d (-1)
  have disj : Disjoint P M := by
    apply disjoint_left.mpr
    intro a ha hm
    have hp := (mem_filter.mp ha).2
    have hn := (mem_filter.mp hm).2
    omega
  have sub : P ∪ M ⊆ odds B := union_subset (filter_subset ..) (filter_subset ..)
  have cap := card_le_card sub
  rw [card_union_of_disjoint disj] at cap
  by_cases le : P.card ≤ M.card
  · exact ⟨1,Or.inl rfl,by change 2*P.card ≤ _; omega⟩
  · exact ⟨-1,Or.inr rfl,by change 2*M.card ≤ _; omega⟩

theorem odd_size (b : ℕ) : (odds (2*b)).card ≤ b := by
  let S := odds (2*b)
  have into (a : ℕ) (ha : a∈S) : a/2 ∈ Ico b (2*b) := by
    obtain ⟨lo,hi⟩ := mem_Ico.mp (mem_filter.mp ha).1
    exact mem_Ico.mpr ⟨by omega,by omega⟩
  have inj (a : ℕ) (ha : a∈S) (c : ℕ) (hc : c∈S) (eq : a/2=c/2) : a=c := by
    have ao := (mem_filter.mp ha).2
    have co := (mem_filter.mp hc).2
    omega
  exact (card_le_card_of_injOn (fun a : ℕ => a/2) into inj).trans (by simp; omega)

/-- Any sign present in the interval occurs in at least one residue per
complete period, even when the interval starts halfway through a period. -/
theorem period_count {B a : ℕ} {d ε : ℤ} (da : 0<d.natAbs) (mem : a∈entries B d ε) :
    B/(4*d.natAbs) ≤ (entries B d ε).card := by
  obtain ⟨oddset,sig⟩ := mem_filter.mp mem
  obtain ⟨bounds,ao⟩ := mem_filter.mp oddset
  have al := (mem_Ico.mp bounds).1
  let T := 4*d.natAbs
  have tp : 0<T := Nat.mul_pos (by decide) da
  let f (j : ℕ) := B + (a-B)%T + j*T
  have residue (j : ℕ) : Nat.ModEq T (f j) a := by
    change (B+(a-B)%T+j*T)%T=a%T
    rw [Nat.add_mul_mod_self_right, Nat.add_mod_mod, Nat.add_sub_of_le al]
  have inside (j : ℕ) (hj : j∈range (B/T)) : f j∈entries B d ε := by
    have h := Nat.mul_le_mul_right T (Nat.succ_le_of_lt (mem_range.mp hj))
    have upper := h.trans (Nat.div_mul_le_self ..)
    rw [Nat.succ_mul] at upper
    have front := Nat.mod_lt (a-B) tp
    have iv : f j∈Ico B (2*B) := mem_Ico.mpr (by dsimp [f]; omega)
    have div : 2∣T := dvd_mul_of_dvd_left (by decide : 2∣4) _
    have odd : f j%2=1 := (show f j%2=a%2 from (residue j).of_dvd div).trans ao
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨iv,odd⟩,
      (periodic (Nat.odd_iff.mpr odd) (Nat.odd_iff.mpr ao) d (residue j)).trans sig⟩
  have inj (j : ℕ) (_ : j∈range (B/T)) (k : ℕ) (_ : k∈range (B/T)) (eq : f j=f k) : j=k :=
    Nat.eq_of_mul_eq_mul_right tp (Nat.add_left_cancel eq)
  simpa only [card_range,T] using card_le_card_of_injOn f inside inj

/-- If a selector has |d| at most 2,016,400, the guaranteed splitting
column in the full target interval still contains at least 2^1000 entries.
The smaller of the two signs obeys the same lower bound. -/
theorem target_lower {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (pl : 2^1023≤p) (ph : p<2*2^1023) (ql : 2^1023≤q) (qh : q<2*2^1023)
    (po : p%2=1) (qo : q%2=1) {d ε : ℤ} (select : jacobiSym d (p*q)= -1)
    (sign : ε=1 ∨ ε= -1) (da : 0<d.natAbs) (cap : d.natAbs≤2016400) :
    2^1000 ≤ (entries (2^1023) d ε).card := by
  have div := split pp qp pl ph ql qh po qo select sign
  have mem : (entries (2^1023) d ε).Nonempty := by
    by_contra! nil
    have one : product (2^1023) d ε=1 := by rw [product,not_nonempty_iff_eq_empty.mp nil,prod_empty]
    rw [one,Nat.gcd_one_left] at div
    have := pp.one_lt
    have := qp.one_lt
    omega
  obtain ⟨a,hm⟩ := mem
  have tp := Nat.mul_pos (by decide : 0<4) da
  apply le_trans _ (period_count da hm)
  apply (Nat.le_div_iff_mul_le tp).mpr
  exact (Nat.mul_le_mul_left (2^1000) (Nat.mul_le_mul_left 4 cap)).trans (by decide +kernel)

/-- Public entry-count upper bound for the cheaper of the two splitting
products on the full 1024-bit factor interval. -/
theorem target_cheaper (d : ℤ) : ∃ ε : ℤ, (ε=1 ∨ ε= -1) ∧
    (entries (2^1023) d ε).card ≤ 2^1021 := by
  obtain ⟨ε,sign,small⟩ := cheaper (2^1023) d
  have size := odd_size (2^1022)
  rw [show 2*2^1022=2^1023 by decide +kernel] at size
  have cap := small.trans size
  rw [show (2:ℕ)^1022=2*2^1021 by decide +kernel] at cap
  exact ⟨ε,sign,Nat.le_of_mul_le_mul_left cap (by decide)⟩

/-- Existence with a bounded representative. CRT is used only to prove
existence; a public trial d is screened by jacobiSym d (p*q). -/
theorem selector {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (diff : p≠q) (qo : q≠2) :
    ∃ d : ℕ, d<p*q ∧ jacobiSym d (p*q)= -1 := by
  letI : Fact p.Prime := ⟨pp⟩
  letI : Fact q.Prime := ⟨qp⟩
  letI : NeZero (p*q) := ⟨Nat.mul_ne_zero pp.ne_zero qp.ne_zero⟩
  have cop := (Nat.coprime_primes pp qp).mpr diff
  obtain ⟨y,neg⟩ := quadraticChar_exists_neg_one (F := ZMod q) (by rwa [ZMod.ringChar_zmod_n])
  let e := ZMod.chineseRemainder cop
  let z := e.symm (1,y)
  have crt : e (z.val : ZMod (p*q)) = (1,y) := by rw [ZMod.natCast_zmod_val]; exact e.apply_symm_apply _
  rw [map_natCast] at crt
  have left : (z.val : ZMod p)=1 := congrArg Prod.fst crt
  have right : (z.val : ZMod q)=y := congrArg Prod.snd crt
  refine ⟨z.val,z.val_lt,?_⟩
  rw [jacobiSym.mul_right' _ pp.ne_zero qp.ne_zero,←jacobiSym.legendreSym.to_jacobiSym p,
    ←jacobiSym.legendreSym.to_jacobiSym q]
  change quadraticChar (ZMod p) (((z.val:ℤ):ZMod p)) * quadraticChar (ZMod q) (((z.val:ℤ):ZMod q))= -1
  rw [Int.cast_natCast,Int.cast_natCast,left,right,map_one,neg,one_mul]

private noncomputable def charVal (n : ℕ) (u : (ZMod n)ˣ) : ℤ :=
  jacobiSym ((u : ZMod n).val : ℤ) n

private theorem char_mul {n : ℕ} (u v : (ZMod n)ˣ) :
    charVal n (u*v)=charVal n u*charVal n v := by
  unfold charVal
  rw [Units.val_mul,ZMod.val_mul,Int.natCast_mod,← jacobiSym.mod_left,
    Nat.cast_mul,jacobiSym.mul_left]

private theorem char_one (n : ℕ) [Fact (1<n)] : charVal n 1=1 := by
  simp [charVal,ZMod.val_one]

private theorem alternatives {n : ℕ} (u : (ZMod n)ˣ) : charVal n u=1 ∨ charVal n u= -1 :=
  jacobiSym.eq_one_or_neg_one (by rw [Int.gcd_natCast_natCast]; exact ZMod.val_coe_unit_coprime u)

private theorem char_base {n a : ℕ} (ha : a.Coprime n) :
    charVal n (ZMod.unitOfCoprime a ha)=jacobiSym a n := by
  rw [charVal,ZMod.coe_unitOfCoprime,ZMod.val_natCast,Int.natCast_mod,←jacobiSym.mod_left]

private theorem unit_selector {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (diff : p≠q) (qo : q≠2) :
    ∃ u : (ZMod (p*q))ˣ, charVal (p*q) u= -1 := by
  obtain ⟨d,_,hd⟩ := selector pp qp diff qo
  have cop : d.Coprime (p*q) := by
    by_contra bad
    have hz := jacobiSym.eq_zero_iff.mpr (And.intro (Nat.mul_ne_zero pp.ne_zero qp.ne_zero)
      (show (d:ℤ).gcd (p*q : ℕ) ≠ 1 by simpa only [Int.gcd_natCast_natCast] using bad))
    omega
  exact ⟨ZMod.unitOfCoprime d cop,(char_base cop).trans hd⟩

/-- Negative-symbol selectors occupy exactly half the units. A fresh uniform
unit therefore passes the public check with probability 1/2 on each trial. -/
theorem half_units {p q : ℕ} [NeZero (p*q)] (pp : p.Prime) (qp : q.Prime) (diff : p≠q)
    (qo : q≠2) :
    2*(univ.filter (fun u : (ZMod (p*q))ˣ => jacobiSym ((u:ZMod (p*q)).val : ℤ) (p*q)= -1)).card =
      Fintype.card (ZMod (p*q))ˣ := by
  classical
  let n := p*q
  haveI : Fact (1<n) := ⟨by dsimp [n]; nlinarith [pp.one_lt,qp.one_lt]⟩
  obtain ⟨v,neg⟩ := unit_selector pp qp diff qo
  let C (ε : ℤ) := univ.filter fun u : (ZMod n)ˣ => charVal n u=ε
  have inv : charVal n v⁻¹= -1 := by
    have both := char_mul v v⁻¹
    rw [mul_inv_cancel,char_one,neg,neg_one_mul] at both
    exact neg_eq_iff_eq_neg.mp both.symm
  have eq : (C 1).card=(C (-1)).card := by
    apply card_nbij' (v*·) (v⁻¹*·)
    · intro u hu
      have := (mem_filter.mp hu).2
      exact mem_filter.mpr ⟨mem_univ _,by rw [char_mul,neg,this]; decide⟩
    · intro u hu
      have := (mem_filter.mp hu).2
      exact mem_filter.mpr ⟨mem_univ _,by rw [char_mul,inv,this]; decide⟩
    · intro u _; simp
    · intro u _; simp
  have flip : (univ.filter (fun u : (ZMod n)ˣ => ¬charVal n u=1))=C (-1) := by
    ext u
    simp only [C,mem_filter,mem_univ,true_and]
    rcases alternatives u with h|h <;> simp [h]
  have both := filter_card_add_filter_neg_card_eq_card (s:=(univ : Finset (ZMod n)ˣ))
    (fun u => charVal n u=1)
  rw [flip,card_univ] at both
  change (C 1).card + (C (-1)).card = _ at both
  change 2*(C (-1)).card = _
  rw [eq] at both
  simpa only [two_mul] using both

private noncomputable def positiveKernel (n : ℕ) [Fact (1<n)] : Subgroup (ZMod n)ˣ where
  carrier := {u | charVal n u=1}
  one_mem' := char_one n
  mul_mem' := fun a b => by rw [Set.mem_setOf_eq] at *; rw [char_mul,a,b,one_mul]
  inv_mem' := by
    intro u hu
    have both := char_mul u u⁻¹
    change charVal n u=1 at hu
    rw [mul_inv_cancel,char_one,hu,one_mul] at both
    exact both.symm

/-- Exact finite interface for a conditional least-prime-outside-a-subgroup
estimate. The subgroup hypothesis is used only for the prime selector size. -/
theorem bounded_prime {p q bound : ℕ} (pp : p.Prime) (qp : q.Prime) (diff : p≠q) (qo : q≠2)
    (small : SmallPrimeOutside (p*q) bound) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ≤bound ∧ jacobiSym ℓ (p*q)= -1 := by
  haveI : Fact (1<p*q) := ⟨by nlinarith [pp.one_lt,qp.one_lt]⟩
  obtain ⟨v,neg⟩ := unit_selector pp qp diff qo
  have proper : positiveKernel (p*q) ≠ ⊤ := by
    intro all
    have mem : v∈positiveKernel (p*q) := all ▸ Subgroup.mem_top _
    change charVal (p*q) v=1 at mem
    omega
  obtain ⟨ℓ,pr,budget,unit,out⟩ := small _ proper
  refine ⟨ℓ,pr,budget,?_⟩
  change ¬charVal (p*q) (ZMod.unitOfCoprime ℓ unit)=1 at out
  exact (char_base unit).symm.trans ((alternatives _).resolve_left out)

theorem example_entries : entries 16 2 1={17,23,25,31} ∧ entries 16 2 (-1)={19,21,27,29} := by
  have eq (ε : ℤ) : entries 16 2 ε=(Ico 16 32).filter (fun a : ℕ => a%2=1 ∧ ZMod.χ₈ a=ε) := by
    ext a
    simp only [entries,odds,mem_filter]
    by_cases odd : a%2=1
    · simp [odd,jacobiSym.at_two (Nat.odd_iff.mpr odd)]
    · simp [odd]
  rw [eq,eq]
  decide +kernel

/-- The first positive candidate after 1 is already a selector. For the
positive sign the four integers are 17, 23, 25, 31 and their gcd with
323 recovers 17. The opposite column returns 19. -/
theorem example_323 : jacobiSym 2 323= -1 ∧
    (product 16 2 1).gcd 323=17 ∧ (product 16 2 (-1)).gcd 323=19 := by
  have pp : Nat.Prime 17 := by decide
  have qp : Nat.Prime 19 := by decide
  have eval17 : jacobiSym 2 17=1 := by rw [jacobiSym.at_two (by decide)]; decide +kernel
  have eval19 : jacobiSym 2 19= -1 := by rw [jacobiSym.at_two (by decide)]; decide +kernel
  have choose : jacobiSym 2 (17*19)= -1 := by
    rw [jacobiSym.mul_right' _ pp.ne_zero qp.ne_zero,eval17,eval19]; decide
  have which (ε : ℤ) (sign : ε=1 ∨ ε= -1) := split (B:=16) pp qp
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) choose sign
  refine ⟨choose,?_,?_⟩
  · refine (which 1 (.inl rfl)).resolve_right ?_
    intro wrong
    have h := (prime_dvd_iff pp (by decide : 16≤17) (by decide) (by decide) 2 1).mpr eval17
    have both := Nat.dvd_gcd h (show 17∣17*19 from dvd_mul_right ..)
    rw [wrong] at both
    exact (by decide : ¬17∣19) both
  · refine (which (-1) (.inr rfl)).resolve_left ?_
    intro wrong
    have h := (prime_dvd_iff qp (by decide : 16≤19) (by decide) (by decide) 2 (-1)).mpr eval19
    have both := Nat.dvd_gcd h (show 19∣17*19 from dvd_mul_left ..)
    rw [wrong] at both
    exact (by decide : ¬19∣17) both

end PrimeFactors.CharacterDivisorColumn
