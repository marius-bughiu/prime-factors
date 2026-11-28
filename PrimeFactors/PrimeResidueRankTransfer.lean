import PrimeFactors.CoprimeGuessTables
import PrimeFactors.ThresholdPairCount
import PrimeFactors.ResiduePairWeights

/-! Comparison of one specified sum-label order on two finite populations:
sorted pairs of distinct primes in a product-size region, and uniform ordered
pairs of residues with product one. The transfer hypotheses bound the actual
counts in the ordered residue cells. -/
namespace PrimeFactors.PrimeResidueRankTransfer

open Finset ThresholdPairCount PrimeSquareSumWeights CoprimeGuessTables
open scoped Classical

variable {m : ℕ} [NeZero m]

noncomputable def tail (B z : ℕ) (a : ZMod m) :=
  ResiduePairMultiplicity.primes m (z+1) (B+1) a.val

theorem mem_tail {a : ZMod m} {p B z : ℕ} :
    p∈tail B z a ↔ z<p ∧ p≤B ∧ p.Prime ∧ (p:ZMod m)=a := by
  have cast : p%m=a.val ↔ (p:ZMod m)=a := by
    rw [←ZMod.val_natCast]
    exact ⟨fun h => ZMod.val_injective m h,congrArg ZMod.val⟩
  simp only [tail,ResiduePairMultiplicity.mem_primes,Nat.lt_succ_iff,Nat.succ_le_iff,cast]

noncomputable def cell (X B K : ℕ) (v : ZMod m × ZMod m) :=
  (distinctRegion K (tail B X v.1) (tail B X v.2)).card

private noncomputable def pool (X B : ℕ) := (Ioc X B).filter Nat.Prime
private def coords (z : ℕ×ℕ) : ZMod m × ZMod m := (z.1,z.2)

private noncomputable def ordered (m X B K : ℕ) [NeZero m] :=
  (distinctRegion K (pool X B) (pool X B)).filter fun z =>
    (coords (m:=m) z).1*(coords (m:=m) z).2=1

/-- Canonical prime pairs with both factors in (X,B], product strictly
above K, and product residue one. Each product has one ordered-as-written pair. -/
noncomputable def population (m X B K : ℕ) [NeZero m] :=
  (ordered m X B K).filter fun z => z.1<z.2

private theorem mem_ordered {X B K p q : ℕ} :
    (p,q)∈ordered m X B K ↔
      (X<p ∧ p≤B ∧ p.Prime) ∧ (X<q ∧ q≤B ∧ q.Prime) ∧ K<p*q ∧ p≠q ∧ ((p*q:ℕ):ZMod m)=1 := by
  simp only [ordered,pool,distinctRegion,region,mem_product,mem_filter,mem_Ioc,coords,Nat.cast_mul]
  tauto

theorem mem_population {X B K p q : ℕ} :
    (p,q)∈population m X B K ↔ X<p ∧ p<q ∧ q≤B ∧ p.Prime ∧ q.Prime ∧
      K<p*q ∧ ((p*q:ℕ):ZMod m)=1 := by
  rw [population,mem_filter,mem_ordered]
  constructor
  · rintro ⟨⟨⟨l,_,P⟩,⟨_,u,Q⟩,big,_,res⟩,lt⟩
    exact ⟨l,lt,u,P,Q,big,res⟩
  · rintro ⟨l,lt,u,P,Q,big,res⟩
    exact ⟨⟨⟨l,lt.le.trans u,P⟩,⟨l.trans lt,u,Q⟩,big,lt.ne,res⟩,lt⟩

private theorem fiber (X B K : ℕ) (v : ZMod m × ZMod m) (prod : v.1*v.2=1) :
    ((ordered m X B K).filter (fun z => coords z=v)).card=cell X B K v := by
  obtain ⟨a,b⟩ := v
  apply congrArg Finset.card
  ext ⟨p,q⟩
  simp only [mem_filter,mem_ordered,coords,Prod.mk.injEq,distinctRegion,region,mem_product,mem_tail,
    Nat.cast_mul] at *
  constructor
  · tauto
  · rintro ⟨⟨⟨⟨l,u,P,pa⟩,⟨l',u',Q,qb⟩⟩,big⟩,ne⟩
    exact ⟨⟨⟨l,u,P⟩,⟨l',u',Q⟩,big,ne,by simpa only [pa,qb] using prod⟩,pa,qb⟩

private theorem ordered_twice (X B K : ℕ) (rank : ZMod m → ℕ) :
    (∑ z∈ordered m X B K,rank ((z.1+z.2:ℕ):ZMod m)) =
    2*(∑ z∈population m X B K,rank ((z.1+z.2:ℕ):ZMod m)) := by
  let S := ordered m X B K
  let cost (z : ℕ×ℕ) := rank ((z.1+z.2:ℕ):ZMod m)
  let lt (z : ℕ×ℕ) := z.1<z.2
  have swap {z : ℕ×ℕ} (ok : z∈S) : z.swap∈S := by
    obtain ⟨p,q,big,ne,res⟩ := mem_ordered.mp ok
    exact mem_ordered.mpr ⟨q,p,by simpa only [Nat.mul_comm] using big,ne.symm,
      by simpa only [Nat.mul_comm] using res⟩
  have eq : (∑ z∈S.filter lt,cost z)=∑ z∈S.filter (fun z => ¬lt z),cost z := by
    apply sum_nbij' Prod.swap Prod.swap
    · intro z hz
      obtain ⟨ok,l⟩ := mem_filter.mp hz
      exact mem_filter.mpr ⟨swap ok,not_lt_of_ge l.le⟩
    · intro z hz
      obtain ⟨ok,l⟩ := mem_filter.mp hz
      exact mem_filter.mpr ⟨swap ok,lt_of_le_of_ne (le_of_not_gt l) (mem_ordered.mp ok).2.2.2.1.symm⟩
    · intro _ _; rfl
    · intro _ _; rfl
    · intro z _
      simp [cost,add_comm]
  have parts := sum_filter_add_sum_filter_not S lt cost
  change (∑ z∈S,cost z)=2*∑ z∈S.filter lt,cost z
  rw [←parts,←eq,two_mul]

/-- Twice the rank sum on canonical actual prime pairs equals the sum
over ordered residue cells, weighted by their actual prime pair counts. -/
theorem twice_score (X B K : ℕ) (rank : ZMod m → ℕ) :
    2*(∑ z∈population m X B K,rank ((z.1+z.2:ℕ):ZMod m)) =
    ∑ v : Pairs 1 m, cell X B K v.val * rank (sumOf v) := by
  let S := ordered m X B K
  let C := (univ : Finset (ZMod m × ZMod m)).filter fun v => v.1*v.2=1
  have memC (v : ZMod m × ZMod m) : v∈C ↔ v.1*v.2=1 := by simp [C]
  have maps (z) (hz : z∈S) : coords z∈C := memC _ |>.mpr (mem_filter.mp hz).2
  rw [←ordered_twice]
  have grouped := sum_fiberwise_of_maps_to' maps (fun v => rank (v.1+v.2))
  simp only [sum_const,nsmul_eq_mul] at grouped
  calc
    _ = ∑ v∈C, (S.filter (fun z => coords z=v)).card*rank (v.1+v.2) := by
      simpa only [S,coords,Nat.cast_add] using grouped.symm
    _ = ∑ v∈C, cell X B K v*rank (v.1+v.2) :=
      sum_congr rfl (fun v hv => by rw [show (S.filter (fun z => coords z=v)).card=cell X B K v
        from fiber X B K v ((memC _).mp hv)])
    _ = _ := sum_subtype C (fun v => by simpa only [Nat.cast_one] using memC v)
      (fun v => cell X B K v*rank (v.1+v.2))

noncomputable def primeMean (X B K : ℕ) (rank : ZMod m → ℕ) : ℝ :=
  (∑ z∈population m X B K,rank ((z.1+z.2:ℕ):ZMod m):ℕ)/(population m X B K).card

noncomputable def residueMean (rank : ZMod m → ℕ) : ℝ :=
  (∑ v : Pairs 1 m, rank (sumOf v):ℕ)/(Fintype.card (Pairs 1 m))

/-- If all ordered product-one residue cells have actual counts between
positive l and u, the same sum-label rank has actual mean within the factors
l/u and u/l of its mean on uniform ordered product-one residue pairs. -/
theorem mean_bounds (X B K : ℕ) (rank : ZMod m → ℕ) {l u : ℕ} (positive : 0<l)
    (cells : ∀ v : Pairs 1 m, l≤cell X B K v.val ∧ cell X B K v.val≤u) :
    (l:ℝ)/u*residueMean rank≤primeMean X B K rank ∧
      primeMean X B K rank≤(u:ℝ)/l*residueMean rank := by
  let S := population m X B K
  let A := ∑ z∈S,rank ((z.1+z.2:ℕ):ZMod m)
  let C := Fintype.card (Pairs 1 m)
  let T := ∑ v : Pairs 1 m,rank (sumOf v)
  have work (r : ZMod m→ℕ) :
      l*(∑ v : Pairs 1 m,r (sumOf v))≤2*(∑ z∈S,r ((z.1+z.2:ℕ):ZMod m)) ∧
      2*(∑ z∈S,r ((z.1+z.2:ℕ):ZMod m))≤u*∑ v : Pairs 1 m,r (sumOf v) := by
    rw [show S=population m X B K from rfl,twice_score,mul_sum,mul_sum]
    exact ⟨sum_le_sum (fun v _ => Nat.mul_le_mul_right _ (cells v).1),
      sum_le_sum (fun v _ => Nat.mul_le_mul_right _ (cells v).2)⟩
  obtain ⟨wl,wu⟩ := work rank
  obtain ⟨cl,cu⟩ : l*C≤2*S.card ∧ 2*S.card≤u*C := by simpa [C] using work (fun _ => 1)
  let one : Pairs 1 m := ⟨(1,1),by norm_num⟩
  haveI : Nonempty (Pairs 1 m) := ⟨one⟩
  have cpos : 0<C := Fintype.card_pos
  have spos : 0<S.card := by have := Nat.mul_pos positive cpos; omega
  have upos : 0<u := positive.trans_le ((cells one).1.trans (cells one).2)
  change l*T≤2*A at wl
  change 2*A≤u*T at wu
  have low : l*T*S.card≤A*(u*C) := by
    nlinarith only [Nat.mul_le_mul_right S.card wl,Nat.mul_le_mul_right A cu]
  have high : A*(l*C)≤u*T*S.card := by
    nlinarith only [Nat.mul_le_mul_right S.card wu,Nat.mul_le_mul_right A cl]
  change (l:ℝ)/u*((T:ℝ)/C) ≤ (A:ℝ)/S.card ∧ (A:ℝ)/S.card ≤ (u:ℝ)/l*((T:ℝ)/C)
  rw [div_mul_div_comm,div_mul_div_comm]
  constructor
  · exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by exact_mod_cast low)
  · exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by exact_mod_cast high)

/-- Extend the one-based rank of any ordering to all residues. The value
outside the attained support never contributes to either population. -/
noncomputable def rankOf (e : Fin (Fintype.card (Labels m 1)) ≃ Labels m 1) (s : ZMod m) : ℕ :=
  if h : AdmissibleSum (1:ZMod m) s then (e.symm ⟨s,by simpa using h⟩).val+1 else 0

private theorem by_label (f : ZMod m → ℕ) :
    (∑ v : Pairs 1 m,f (sumOf v))=∑ s : Labels m 1,weight 1 s.val*f s.val := by
  let label (v : Pairs 1 m) : Labels m 1 := ⟨sumOf v,v.val.1,v.val.2,v.property,rfl⟩
  have fiber_size (s : Labels m 1) :
      (univ.filter (fun v : Pairs 1 m => label v=s)).card=weight 1 s.val := by
    rw [weight,Nat.card_eq_fintype_card,Fintype.card_subtype]
    apply congrArg Finset.card
    ext v
    simp only [mem_filter,mem_univ,true_and,Subtype.ext_iff,label]
  have grouped := sum_fiberwise_of_maps_to' (s:=univ)
    (fun v _ => mem_univ (label v)) (fun s : Labels m 1 => f s.val)
  simpa only [sum_const,nsmul_eq_mul,fiber_size,label] using grouped.symm

/-- The comparison's finite residue-pair mean agrees with the inclusive
mean rank defined using the actual multiplicities of attained sum labels. -/
theorem residueMean_rankOf (e : Fin (Fintype.card (Labels m 1)) ≃ Labels m 1) :
    residueMean (rankOf e) =
      IndependentGuessRanks.meanRank (fun s : Labels m 1 => (weight 1 s.val:ℝ)) e := by
  have ranks : (∑ v : Pairs 1 m,rankOf e (sumOf v))=
      ∑ i,(i.val+1)*weight 1 (e i).val := by
    rw [by_label,←e.sum_comp (fun s : Labels m 1 => weight 1 s.val*rankOf e s.val)]
    apply sum_congr rfl
    intro i _
    have pass : AdmissibleSum (1:ZMod m) (e i).val := by simpa using (e i).property
    simp [rankOf,pass,Nat.mul_comm]
  have mass : Fintype.card (Pairs 1 m)=∑ s : Labels m 1,weight 1 s.val := by
    simpa using by_label (m:=m) (fun _ => 1)
  unfold residueMean IndependentGuessRanks.meanRank IndependentGuessRanks.total
  rw [ranks,mass]
  push_cast
  rfl

/-- At dyadic endpoints and widths of at least three bits, equality with
either fixed power of two cannot occur for the primes or for their odd
product. This gives the conventional inclusive lower width conditions. -/
theorem mem_full_width {b p q : ℕ} (width : 3≤b) :
    (p,q)∈population m (2^(b-1)) (2^b) (2^(2*b-1)) ↔
    2^(b-1)≤p ∧ p<q ∧ q<2^b ∧ p.Prime ∧ q.Prime ∧
      2^(2*b-1)≤p*q ∧ ((p*q:ℕ):ZMod m)=1 := by
  rw [mem_population]
  constructor
  · rintro ⟨low,order,high,P,Q,prod,res⟩
    have ne : q≠2^b := fun eq =>
      (Nat.Prime.not_prime_pow (by omega : 2≤b) (x:=2)) (eq ▸ Q)
    exact ⟨low.le,order,high.lt_of_ne ne,P,Q,prod.le,res⟩
  · rintro ⟨low,order,high,P,Q,prod,res⟩
    have ne : (2:ℕ)^(b-1)≠p := fun eq =>
      (Nat.Prime.not_prime_pow (by omega : 2≤b-1) (x:=2)) (eq.symm ▸ P)
    have small : 2<(2:ℕ)^(b-1) :=
      lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) (by omega))
    have odd := (P.odd_of_ne_two (small.trans_le low).ne').mul
      (Q.odd_of_ne_two ((small.trans_le low).trans order).ne')
    have even : Even ((2:ℕ)^(2*b-1)) := Even.pow_of_ne_zero (by decide) (by omega)
    have diff : (2:ℕ)^(2*b-1)≠p*q := fun eq => (Nat.not_even_iff_odd.mpr odd) (eq ▸ even)
    exact ⟨low.lt_of_ne ne,order,high.le,P,Q,prod.lt_of_ne diff,res⟩

end PrimeFactors.PrimeResidueRankTransfer
