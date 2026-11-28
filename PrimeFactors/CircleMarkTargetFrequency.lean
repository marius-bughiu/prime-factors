import PrimeFactors.CircleBranchCount
import PrimeFactors.PrimePowerCount
import PrimeFactors.SumGuessIncidence

/-! A uniformly chosen negative-Jacobi target at a fixed product of two odd
primes, tested at a predetermined finite set of integer coordinates. -/

namespace PrimeFactors.CircleMarkTargetFrequency

open Finset
open scoped Classical
open private PrimeFactors.SumGuessIncidence.half_inj from PrimeFactors.SumGuessIncidence

/-- Residue classes passing the public Jacobi test. A negative symbol implies
the target is a unit. Each class has equal weight. -/
noncomputable def targets (n : ℕ) [NeZero n] : Finset (ZMod n) :=
  univ.filter fun t => jacobiSym t.val n = -1

theorem target_unit {n : ℕ} [hn : NeZero n] {t : ZMod n} (h : t∈targets n) : IsUnit t := by
  have neg := (mem_filter.mp h).2
  rw [←ZMod.natCast_zmod_val t,ZMod.isUnit_iff_coprime]
  by_contra bad
  have zero := jacobiSym.eq_zero_iff.mpr ⟨hn.out,show (t.val : ℤ).gcd (n:ℕ)≠1 by
    simpa only [Int.gcd_natCast_natCast] using bad⟩
  omega

/-- Targets for which some tested coordinate gives a public mark. -/
noncomputable def hits (n : ℕ) [NeZero n] (C : Finset ℕ) : Finset (ZMod n) :=
  (targets n).filter fun t => ∃ x ∈ C, (x : ZMod n) ∈ CircleBranchCount.marked n t.val

/-- Distinct nonzero target residues actually tested at one prime. -/
noncomputable def covered (p : ℕ) (C : Finset ℕ) : Finset (ZMod p) :=
  (C.image fun x : ℕ => (x : ZMod p)^2).erase 0

private noncomputable def squares (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  univ.filter IsSquare

private noncomputable abbrev plus (p : ℕ) [Fact p.Prime] := (squares p).erase 0
private noncomputable abbrev minus (p : ℕ) [Fact p.Prime] := (squares p)ᶜ

private theorem local_cards (p : ℕ) [hp : Fact p.Prime] (op : p≠2) :
    (plus p).card=(p-1)/2 ∧ (minus p).card=(p-1)/2 := by
  have h := card_primePower_squares (p:=p) op 1
  rw [pow_one,Nat.card_eq_fintype_card,Fintype.card_subtype] at h
  change (squares p).card = (p-1)/2+1 at h
  have zero : (0 : ZMod p) ∈ squares p := by simp [squares]
  obtain ⟨j,hj⟩ := hp.out.odd_of_ne_two op
  simp only [plus,card_erase_of_mem zero,minus,card_compl,ZMod.card,h]
  omega

private theorem covered_sub (p : ℕ) [Fact p.Prime] (C : Finset ℕ) : covered p C ⊆ plus p := by
  intro a ha
  obtain ⟨nz,hm⟩ := mem_erase.mp ha
  obtain ⟨x,_,rfl⟩ := mem_image.mp hm
  exact mem_erase.mpr ⟨nz,mem_filter.mpr ⟨mem_univ _,IsSquare.sq _⟩⟩

private noncomputable def rectangles {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (A : Finset (ZMod p)) (B : Finset (ZMod q)) :=
  (A ×ˢ minus q) ∪ (minus p ×ˢ B)

private theorem rect_count {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (op : p≠2) (oq : q≠2)
    (A : Finset (ZMod p)) (B : Finset (ZMod q)) (sub : A⊆plus p) :
    (rectangles A B).card = A.card*((q-1)/2) + ((p-1)/2)*B.card := by
  have dj : Disjoint (A ×ˢ minus q) (minus p ×ˢ B) := by
    apply disjoint_left.mpr
    intro z l r
    exact (mem_compl.mp (mem_product.mp r).1) (mem_of_mem_erase (sub (mem_product.mp l).1))
  rw [rectangles,card_union_of_disjoint dj,card_product,card_product,(local_cards p op).2,(local_cards q oq).2]

private theorem sign_cases {p : ℕ} [Fact p.Prime] (a : ZMod p) :
    (a∈plus p ↔ quadraticChar (ZMod p) a=1) ∧
    (a∈minus p ↔ quadraticChar (ZMod p) a= -1) := by
  simp only [plus,minus,squares,mem_erase,mem_filter,mem_univ,true_and,mem_compl,
    quadraticChar_neg_one_iff_not_isSquare,iff_self,and_true]
  by_cases nz : a=0
  · simp [nz,quadraticChar_zero]
  · rw [and_iff_right nz,quadraticChar_one_iff_isSquare nz]

private theorem target_rect {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (cop : p.Coprime q) (t : ZMod (p*q)) :
    t∈targets (p*q) ↔ ZMod.chineseRemainder cop t ∈ rectangles (plus p) (plus q) := by
  let e := ZMod.chineseRemainder cop
  have coord : e t=((t.val : ZMod p),(t.val : ZMod q)) := by
    have h := map_natCast e t.val
    rw [ZMod.natCast_zmod_val] at h
    exact h
  have j : jacobiSym t.val (p*q) = quadraticChar (ZMod p) (t.val : ZMod p) *
      quadraticChar (ZMod q) (t.val : ZMod q) := by
    rw [jacobiSym.mul_right' _ hp.out.ne_zero hq.out.ne_zero,
      ←jacobiSym.legendreSym.to_jacobiSym p,←jacobiSym.legendreSym.to_jacobiSym q]
    simp [legendreSym]
  change t∈targets (p*q) ↔ e t∈_
  rw [coord]
  simp only [targets,mem_filter,mem_univ,true_and,rectangles,mem_union,mem_product,j,
    (sign_cases _).1,(sign_cases _).2]
  constructor
  · intro hz
    have P : (t.val : ZMod p)≠0 := by intro h; simp [h,quadraticChar_zero] at hz
    have Q : (t.val : ZMod q)≠0 := by intro h; simp [h,quadraticChar_zero] at hz
    rcases quadraticChar_dichotomy P with h|h <;> rcases quadraticChar_dichotomy Q with g|g <;> simp_all
  · rintro (⟨h,g⟩|⟨h,g⟩) <;> rw [h,g] <;> norm_num

private theorem marked_at {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (t : ZMod (p*q)) (x : ℕ) :
    (x : ZMod (p*q))∈CircleBranchCount.marked (p*q) t.val ↔
      (ZMod.chineseRemainder cop t).1=(x:ZMod p)^2 ∨
      (ZMod.chineseRemainder cop t).2=(x:ZMod q)^2 := by
  let e := ZMod.chineseRemainder cop
  simp only [CircleBranchCount.marked,mem_filter,mem_univ,true_and,Int.cast_natCast,ZMod.natCast_zmod_val]
  rw [←isUnit_map_iff e,map_sub,map_pow,map_natCast,Prod.isUnit_iff]
  change ¬(IsUnit ((e t).1-(x:ZMod p)^2) ∧ IsUnit ((e t).2-(x:ZMod q)^2)) ↔ _
  simp only [isUnit_iff_ne_zero,ne_eq,sub_eq_zero]
  tauto

private theorem target_hits {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (C : Finset ℕ) (t : ZMod (p*q)) :
    t∈hits (p*q) C ↔ ZMod.chineseRemainder cop t∈rectangles (covered p C) (covered q C) := by
  let e := ZMod.chineseRemainder cop
  have avoid {r : ℕ} [Fact r.Prime] {a : ZMod r} (h : a∈minus r) (x : ℕ) : a ≠ (x:ZMod r)^2 := by
    intro eq
    apply mem_compl.mp h
    simp [squares,eq]
  have get {r : ℕ} [Fact r.Prime] {a : ZMod r} (h : a∈plus r) {x : ℕ}
      (hx : x∈C) (eq : a=(x:ZMod r)^2) : a∈covered r C :=
    mem_erase.mpr ⟨(mem_erase.mp h).1,mem_image.mpr ⟨x,hx,eq.symm⟩⟩
  simp only [hits,mem_filter,target_rect cop,rectangles,mem_union,mem_product,marked_at cop]
  constructor
  · rintro ⟨h, x,hx,hp|hq⟩
    · rcases h with ⟨l,r⟩|⟨l,r⟩
      · exact Or.inl ⟨get l hx hp,r⟩
      · exact (avoid l x hp).elim
    · rcases h with ⟨l,r⟩|⟨l,r⟩
      · exact (avoid r x hq).elim
      · exact Or.inr ⟨l,get r hx hq⟩
  · rintro (⟨l,r⟩|⟨l,r⟩)
    · obtain ⟨x,hx,he⟩ := mem_image.mp (mem_of_mem_erase l)
      exact ⟨Or.inl ⟨covered_sub p C l,r⟩,x,hx,Or.inl he.symm⟩
    · obtain ⟨x,hx,he⟩ := mem_image.mp (mem_of_mem_erase r)
      exact ⟨Or.inr ⟨l,covered_sub q C r⟩,x,hx,Or.inr he.symm⟩

/-- The sample universe and all hits in it are counted by two disjoint CRT
rectangles. Arbitrary repetitions of a square at either prime count only once. -/
theorem counts {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) (C : Finset ℕ) :
    (targets (p*q)).card=2*((p-1)/2)*((q-1)/2) ∧
    (hits (p*q) C).card=(covered p C).card*((q-1)/2)+((p-1)/2)*(covered q C).card := by
  have cop := (Nat.coprime_primes hp.out hq.out).mpr diff
  let e := ZMod.chineseRemainder cop
  have map_eq (U : Finset (ZMod (p*q))) (V : Finset (ZMod p×ZMod q))
      (iff : ∀ t, t∈U ↔ e t∈V) : U.card=V.card := by
    have eq : U.map e.toEquiv.toEmbedding=V := by
      ext z
      obtain ⟨t,rfl⟩ := e.surjective z
      rw [mem_map_equiv]
      change e.symm (e t)∈U ↔ _
      rw [e.symm_apply_apply]
      exact iff t
    rw [←eq,card_map]
  constructor
  · rw [map_eq _ _ (target_rect cop),rect_count op oq _ _ (Subset.rfl),
      (local_cards p op).1,(local_cards q oq).1]
    ring
  · rw [map_eq _ _ (target_hits cop C),rect_count op oq _ _ (covered_sub p C)]

/-- Hit probability under a uniformly chosen Jacobi-negative target. -/
noncomputable def rate (n : ℕ) [NeZero n] (C : Finset ℕ) : ℚ :=
  ((hits n C).card : ℚ)/(targets n).card

theorem rate_eq {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) (C : Finset ℕ) :
    rate (p*q) C = ((covered p C).card : ℚ)/(p-1) + ((covered q C).card : ℚ)/(q-1) := by
  obtain ⟨total,hit⟩ := counts diff op oq C
  have half (r : ℕ) (opr : Odd r) :
      (r : ℚ)-1=2*(((r-1)/2 : ℕ) : ℚ) := by
    have rr : 1 ≤ r := by obtain ⟨k,h⟩ := opr; omega
    rw [show (r : ℚ)-1 = ((r-1 : ℕ) : ℚ) by rw [Nat.cast_sub rr,Nat.cast_one]]
    exact_mod_cast (show r-1=2*((r-1)/2) by obtain ⟨k,h⟩ := opr; omega)
  have P : 0 < (p-1)/2 := by have := hp.out.two_le; omega
  have Q : 0 < (q-1)/2 := by have := hq.out.two_le; omega
  rw [rate,total,hit,half _ (hp.out.odd_of_ne_two op),half _ (hq.out.odd_of_ne_two oq)]
  push_cast
  field_simp [show ((((p-1)/2 : ℕ) : ℚ))≠0 by exact_mod_cast P.ne',
    show ((((q-1)/2 : ℕ) : ℚ))≠0 by exact_mod_cast Q.ne']
  ring

private theorem short_cover {p L : ℕ} [hp : Fact p.Prime] (small : 2*L<p) :
    (covered p (Icc 1 L)).card=L := by
  let f (x : ℕ) := (x : ZMod p)^2
  have val (x : ℕ) (h : x∈Icc 1 L) : (x:ZMod p).val=x :=
    ZMod.val_natCast_of_lt (by have := (mem_Icc.mp h).2; omega)
  have inside (x : ℕ) (h : x∈Icc 1 L) : (x : ZMod p)∈SumGuessIncidence.halfPeriod p := by
    apply mem_filter.mpr
    exact ⟨mem_univ _,by rw [val x h]; have := (mem_Icc.mp h).2; omega⟩
  have inj : Set.InjOn f (Icc 1 L : Finset ℕ) := by
    intro a ha b hb eqn
    have eq := PrimeFactors.SumGuessIncidence.half_inj (inside a ha) (inside b hb) eqn
    simpa only [val a ha,val b hb] using congrArg ZMod.val eq
  have zero : (0 : ZMod p)∉(Icc 1 L).image f := by
    rintro h
    obtain ⟨x,hx,z⟩ := mem_image.mp h
    have z0 := (sq_eq_zero_iff.mp z : (x:ZMod p)=0)
    have := congrArg ZMod.val z0
    rw [val x hx,ZMod.val_zero] at this
    have := (mem_Icc.mp hx).1
    omega
  change (((Icc 1 L).image f).erase 0).card=L
  rw [erase_eq_of_not_mem zero,card_image_of_injOn inj,Nat.card_Icc]
  omega

private theorem cover_mono {p : ℕ} {A B : Finset ℕ} (h : A⊆B) :
    covered p A ⊆ covered p B := erase_subset_erase _ (image_subset_image h)

/-- The first L positive coordinates exhaust one new square per test at each
prime until every nonzero square there has been reached. -/
theorem prefix_cover {p : ℕ} [hp : Fact p.Prime] (op : p≠2) (L : ℕ) :
    (covered p (Icc 1 L)).card = min L ((p-1)/2) := by
  have odd := hp.out.odd_of_ne_two op
  obtain ⟨j,hj⟩ := odd
  by_cases low : L≤(p-1)/2
  · rw [min_eq_left low]
    exact short_cover (by omega)
  · rw [min_eq_right (by omega)]
    apply le_antisymm
    · exact (card_le_card (covered_sub p _)).trans_eq (local_cards p op).1
    · rw [←short_cover (p:=p) (L:=(p-1)/2) (by omega)]
      exact card_le_card (cover_mono (Icc_subset_Icc le_rfl (by omega)))

/-- Distribution function of the first marked positive coordinate. This
includes all L, also beyond the smaller prime's half period. -/
theorem first_hit {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) (L : ℕ) :
    rate (p*q) (Icc 1 L) =
      (min L ((p-1)/2) : ℕ)/(p-1 : ℚ) + (min L ((q-1)/2) : ℕ)/(q-1 : ℚ) := by
  rw [rate_eq diff op oq,prefix_cover op,prefix_cover oq]

/-- No preselected set of at most L natural coordinates has greater hit
probability than the initial positive interval, for this uniform target law. -/
theorem optimal {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) {L : ℕ} (C : Finset ℕ) (budget : C.card≤L) :
    rate (p*q) C ≤ rate (p*q) (Icc 1 L) := by
  have bound (r : ℕ) [Fact r.Prime] (o : r≠2) : (covered r C).card≤min L ((r-1)/2) := by
    apply le_min
    · exact (card_le_card (erase_subset ..)).trans (card_image_le.trans budget)
    · exact (card_le_card (covered_sub r C)).trans_eq (local_cards r o).1
  rw [rate_eq diff op oq,first_hit diff op oq]
  have P : 0 ≤ (p:ℚ)-1 := by have := hp.out.one_lt; exact sub_nonneg.mpr (by exact_mod_cast (show 1≤p by omega))
  have Q : 0 ≤ (q:ℚ)-1 := by have := hq.out.one_lt; exact sub_nonneg.mpr (by exact_mod_cast (show 1≤q by omega))
  exact add_le_add (div_le_div_of_nonneg_right (Nat.cast_le.mpr (bound p op)) P)
    (div_le_div_of_nonneg_right (Nat.cast_le.mpr (bound q oq)) Q)

/-- The selector may inspect the entire target before choosing one of K menus. -/
noncomputable def selectedRate (n K : ℕ) [NeZero n] (menus : Fin K → Finset ℕ)
    (choose : ZMod n → Fin K) : ℚ :=
  (((targets n).filter (fun t => t∈hits n (menus (choose t)))).card : ℚ)/(targets n).card

/-- Even a target-dependent selector for K fixed menus of at most L coordinates
has success probability bounded by scanning the first KL positive coordinates. -/
theorem menu_bound {p q K L : ℕ} [Fact p.Prime] [Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) (menus : Fin K → Finset ℕ)
    (budget : ∀ i,(menus i).card≤L) (choose : ZMod (p*q) → Fin K) :
    selectedRate (p*q) K menus choose ≤ rate (p*q) (Icc 1 (K*L)) := by
  let all := univ.biUnion menus
  have size : all.card≤K*L := by
    apply card_biUnion_le.trans
    exact (sum_le_sum (fun i _ => budget i)).trans_eq (by simp)
  have sub : (targets (p*q)).filter (fun t => t∈hits (p*q) (menus (choose t))) ⊆ hits (p*q) all := by
    intro t ht
    obtain ⟨target,proof⟩ := mem_filter.mp ht
    obtain ⟨x,hx,hit⟩ := (mem_filter.mp proof).2
    exact mem_filter.mpr ⟨target,x,mem_biUnion.mpr ⟨choose t,mem_univ _,hx⟩,hit⟩
  apply le_trans _ (optimal diff op oq all size)
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (card_le_card sub)) (by positivity)

set_option exponentiation.threshold 2048 in
/-- At full prime width, even 64 bits selecting among menus of 2^64
coordinates each leave the unconditional hit probability below 2^(-893). -/
theorem full_width {p q K L : ℕ} [Fact p.Prime] [Fact q.Prime]
    (diff : p≠q) (po : 2^1023≤p) (qo : 2^1023≤q)
    (kcap : K≤2^64) (lcap : L≤2^64) (menus : Fin K → Finset ℕ)
    (budget : ∀ i,(menus i).card≤L) (choose : ZMod (p*q) → Fin K) :
    selectedRate (p*q) K menus choose < 1/(2:ℚ)^893 := by
  have op : p≠2 := by intro h; rw [h] at po; norm_num at po
  have oq : q≠2 := by intro h; rw [h] at qo; norm_num at qo
  apply (menu_bound diff op oq menus budget choose).trans_lt
  rw [first_hit diff op oq]
  have coordinate {r : ℕ} (size : 2^1023≤r) :
      (min (K*L) ((r-1)/2) : ℕ)/(r-1 : ℚ) ≤ (2:ℚ)^128 / ((2:ℚ)^1023-1) := by
    apply div_le_div₀ (by positivity) _ (by norm_num) _
    · have work := (min_le_left (K*L) ((r-1)/2)).trans
          ((Nat.mul_le_mul kcap lcap).trans_eq (by decide : (2:ℕ)^64*2^64=2^128))
      exact_mod_cast work
    · exact sub_le_sub_right (by exact_mod_cast size) _
  exact (add_le_add (coordinate po) (coordinate qo)).trans_lt (by norm_num)

end PrimeFactors.CircleMarkTargetFrequency
