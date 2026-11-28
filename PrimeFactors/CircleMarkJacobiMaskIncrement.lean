import PrimeFactors.CircleMarkJacobiMask

/-! Pointwise change in the masked Jacobi symbol on adding the first coordinate
after the midpoint. The statement concerns distinct odd primes in increasing order. -/
namespace PrimeFactors.CircleMarkJacobiMaskIncrement

open Finset Polynomial CircleMarkJacobiMask CircleMarkMidcutReadout CircleMarkTargetFrequency
open scoped Classical
open private PrimeFactors.CircleMarkTargetFrequency.plus PrimeFactors.CircleMarkTargetFrequency.covered_sub
  PrimeFactors.CircleMarkTargetFrequency.local_cards PrimeFactors.CircleMarkTargetFrequency.sign_cases
  from PrimeFactors.CircleMarkTargetFrequency
open CircleMarkTargetFrequency (plus covered_sub local_cards sign_cases)

/-- Public summand for a square prefix. -/
noncomputable def term (n L : ℕ) (t : ZMod n) : ℤ :=
  jacobiSym ((t.val:ℤ)*((prefixMask L).eval (t.val:ℤ))^2) n

/-- Difference at a single residue, using only the input product. -/
noncomputable def changeAt (n : ℕ) (t : ZMod n) : ℤ :=
  term n (cutoff n+1) t - term n (cutoff n) t

noncomputable def positives (n : ℕ) [NeZero n] : Finset (ZMod n) :=
  univ.filter fun t => changeAt n t=1

private noncomputable def contribution (r L : ℕ) [Fact r.Prime] (x : ZMod r) : ℤ :=
  if x∈covered r (Icc 1 L) then 0 else quadraticChar (ZMod r) x

private theorem local_eval (r L a : ℕ) [Fact r.Prime] :
    quadraticChar (ZMod r) (((a:ℤ)*((prefixMask L).eval (a:ℤ))^2:ℤ):ZMod r)=
      contribution r L a := by
  let Q := prefixMask L
  let P := Q.map (Int.castRingHom (ZMod r))
  have eval_at : (Int.castRingHom (ZMod r)) (Q.eval (a:ℤ)) = P.eval (a:ZMod r) := by
    simpa only [P,←eval₂_eq_eval_map,Int.coe_castRingHom,Int.cast_natCast] using
      (eval₂_at_apply (p:=Q) (Int.castRingHom (ZMod r)) (a:ℤ)).symm
  change quadraticChar (ZMod r) (((a:ℤ)*(Q.eval (a:ℤ))^2:ℤ):ZMod r)=_
  simp only [Int.coe_castRingHom] at eval_at
  rw [Int.cast_mul,Int.cast_pow,Int.cast_natCast,eval_at]
  by_cases az : (a:ZMod r)=0
  · simp [az,contribution,covered,quadraticChar_zero]
  have roots : (a:ZMod r)∈rootSet r Q ↔ P.eval (a:ZMod r)=0 := by
    simp only [CircleMarkJacobiMask.rootSet,mem_filter,mem_univ,true_and,P]
  change (a:ZMod r)∈rootSet r (squareMask (Icc 1 L)) ↔ _ at roots
  rw [rootSet_squareMask] at roots
  have cover : (a:ZMod r)∈covered r (Icc 1 L) ↔ P.eval (a:ZMod r)=0 := by
    rw [covered,mem_erase]; exact (and_iff_right az).trans roots
  by_cases hit : (a:ZMod r)∈covered r (Icc 1 L)
  · rw [contribution,if_pos hit,cover.mp hit,zero_pow (by decide : 2≠0),mul_zero,quadraticChar_zero]
  · have nz := (not_congr cover).mp hit
    rw [contribution,if_neg hit,map_mul,quadraticChar_sq_one' nz,mul_one]

private theorem separated {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (L : ℕ) (t : ZMod (p*q)) :
    term (p*q) L t = contribution p L t.val * contribution q L t.val := by
  rw [term,ExtensionTrace.jacobi_crt,local_eval,local_eval]

private theorem saturated {r L : ℕ} [Fact r.Prime] (odd : r≠2) (bound : (r-1)/2≤L) (x : ZMod r) :
    contribution r L x = if quadraticChar (ZMod r) x= -1 then -1 else 0 := by
  have full : covered r (Icc 1 L)=plus r := eq_of_subset_of_card_le (covered_sub r _) (by
    rw [(local_cards r odd).1,prefix_cover odd,min_eq_right bound])
  simp only [contribution,full,(sign_cases x).1]
  by_cases z : x=0
  · simp [z,quadraticChar_zero]
  · rcases quadraticChar_dichotomy z with h|h <;> simp [h]

/-- The public midpoint is strictly below the last distinct square at q,
including when the two factors are adjacent odd primes. -/
theorem room {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) : cutoff (p*q)+1≤(q-1)/2 := by
  obtain ⟨a,ha⟩ := hp.out.odd_of_ne_two op
  obtain ⟨b,hb⟩ := hq.out.odd_of_ne_two oq
  have gap : p+2≤q := by omega
  have ml := Nat.mul_le_mul_right q gap
  have short : (p*q).sqrt < q-1 := by
    apply Nat.sqrt_lt'.mpr
    have diff : q-1+1=q := by omega
    nlinarith only [ml,diff,congrArg (fun x : ℕ => x^2) diff]
  unfold cutoff
  omega

private theorem added {r L : ℕ} [Fact r.Prime] (odd : r≠2) (space : L+1≤(r-1)/2) :
    let z := ((L+1:ℕ):ZMod r)^2
    covered r (Icc 1 (L+1)) = insert z (covered r (Icc 1 L)) ∧
      z∉covered r (Icc 1 L) ∧ quadraticChar (ZMod r) z=1 := by
  let z := ((L+1:ℕ):ZMod r)^2
  have lt : L+1<r := by omega
  have nz : ((L+1:ℕ):ZMod r)≠0 := by
    intro eqn
    have h := congrArg ZMod.val eqn
    rw [ZMod.val_natCast_of_lt lt,ZMod.val_zero] at h
    omega
  have zs : z≠0 := pow_ne_zero _ nz
  have interval : Icc 1 (L+1)=insert (L+1) (Icc 1 L) := by ext x; simp only [mem_Icc,mem_insert]; omega
  have eqn : covered r (Icc 1 (L+1))=insert z (covered r (Icc 1 L)) := by
    simp only [covered,interval,image_insert,erase_insert_of_ne zs,z]
  refine ⟨eqn,?_,(quadraticChar_one_iff_isSquare zs).mpr (IsSquare.sq _)⟩
  intro seen
  have count := congrArg Finset.card (eqn.trans (insert_eq_of_mem seen))
  rw [prefix_cover odd,prefix_cover odd,min_eq_left space,min_eq_left (by omega : L≤(r-1)/2)] at count
  omega

/-- The increment is one exactly on a single residue modulo q paired with
a nonsquare modulo p. All other residues contribute zero. -/
theorem pointwise {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) (t : ZMod (p*q)) :
    changeAt (p*q) t =
      if (t.val:ZMod q)=((cutoff (p*q)+1:ℕ):ZMod q)^2 ∧
          quadraticChar (ZMod p) (t.val:ZMod p)= -1 then 1 else 0 := by
  let k := cutoff (p*q)
  let z := ((k+1:ℕ):ZMod q)^2
  have bound := (between order).1
  obtain ⟨next,unused,one⟩ := added oq (room order op oq)
  change covered q (Icc 1 (k+1))=insert z (covered q (Icc 1 k)) at next
  change z∉covered q (Icc 1 k) at unused
  change quadraticChar (ZMod q) z=1 at one
  change term (p*q) (k+1) t - term (p*q) k t = if (t.val:ZMod q)=z ∧ _ then 1 else 0
  rw [separated,separated,saturated op (bound.trans (Nat.le_succ k)),saturated op bound]
  simp only [contribution,next,mem_insert]
  by_cases qt : (t.val:ZMod q)=z
  · rw [qt]
    by_cases pt : quadraticChar (ZMod p) (t.val:ZMod p)= -1 <;>
      simp only [pt,unused,one,true_and,and_false,and_true,true_or,if_true,if_false,
        eq_self,mul_zero,mul_one,sub_self,zero_sub,neg_neg]
  · simp only [qt,false_or,false_and,if_false,sub_self]

/-- Exactly half the nonzero residues of the smaller prime contribute one,
each appearing once with the new square at q. -/
theorem positive_count {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) : (positives (p*q)).card=(p-1)/2 := by
  have indicator (t : ZMod (p*q)) : changeAt (p*q) t = if changeAt (p*q) t=1 then 1 else 0 := by
    rw [pointwise order op oq]; split <;> decide
  have count : ((positives (p*q)).card:ℤ) = ∑ t : ZMod (p*q), changeAt (p*q) t := by
    calc _ = ∑ t : ZMod (p*q), if changeAt (p*q) t=1 then (1:ℤ) else 0 := (sum_boole ..).symm
         _ = _ := sum_congr rfl (fun t _ => (indicator t).symm)
  have span := (between order).1
  have qspace := room order op oq
  simp only [changeAt,sum_sub_distrib] at count
  change _ = globalSum (p*q) (prefixMask (cutoff (p*q)+1))-globalSum (p*q) (prefixMask (cutoff (p*q))) at count
  rw [prefix_sum order.ne op oq,prefix_sum order.ne op oq,
    min_eq_right (span.trans (Nat.le_succ _)),min_eq_left qspace,
    min_eq_right span,min_eq_left (between order).2] at count
  rw [Nat.cast_add,Nat.cast_one] at count
  exact_mod_cast (show ((positives (p*q)).card:ℤ)=(((p-1)/2:ℕ):ℤ) by linarith only [count])

/-- The change is never negative. -/
theorem nonnegative {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (order : p<q) (op : p≠2) (oq : q≠2) (t : ZMod (p*q)) :
    0≤changeAt (p*q) t := by rw [pointwise order op oq]; split <;> decide

/-- At 35 the midpoint is 2 and the new square is 2 modulo 7.
Among the five residues on this line, exactly 2 and 23 are nonsquares modulo 5. -/
theorem control : positives 35={2,23} := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have chi (a : ZMod 5) (h : a=2 ∨ a=3) : quadraticChar (ZMod 5) a= -1 := by
    apply quadraticChar_neg_one_iff_not_isSquare.mpr
    rintro ⟨s,eqn⟩
    rcases h with rfl|rfl <;> fin_cases s <;> revert eqn <;> decide
  have witness (t : ZMod (5*7)) (qres : (t.val:ZMod 7)=(3:ZMod 7)^2)
      (pres : (t.val:ZMod 5)=2 ∨ (t.val:ZMod 5)=3) : t∈positives (5*7) := by
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rw [pointwise (by decide : 5<7) (by decide) (by decide),
      if_pos ⟨by simpa only [show cutoff (5*7)+1=3 by decide +kernel] using qres,chi _ pres⟩]
  have sub : ({2,23} : Finset (ZMod (5*7)))⊆positives (5*7) :=
    insert_subset (witness 2 (by decide) (by decide)) (singleton_subset_iff.mpr (witness 23 (by decide) (by decide)))
  apply (eq_of_subset_of_card_le sub _).symm
  rw [positive_count (by decide : 5<7) (by decide) (by decide)]
  decide

end PrimeFactors.CircleMarkJacobiMaskIncrement
