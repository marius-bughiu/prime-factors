import PrimeFactors.TraceProgression

/-! A weighted probe is represented by consecutive unit-price tickets.
A balanced binary tree finds any ticket in logarithmic depth. Each sparse
budget witness checks at most two geometric boundaries and subtracts their
indices to bound the total covered price. -/

namespace PrimeFactors.SparseTraceDual

open TraceCoverCertificate Finset

/-- A split stores the absolute ticket index of its first right descendant.
The pivot separates the ratios in the two subtrees. -/
inductive Tree where
  | leaf (p : Point)
  | split (index : ℕ) (pivot : Point) (lo hi : Tree)

noncomputable def read (tree : Tree) (i : ℕ) : Point :=
  match tree with
  | .leaf p => p
  | .split k _ l r => if i<k then read l i else read r i

private noncomputable def sortedCore (tree : Tree) (L R : Point) : Bool :=
  match tree with
  | .leaf p => positive p && before L p && before p R
  | .split _ p l r =>
    positive p && before L p && before p R && sortedCore l L p && sortedCore r p R

noncomputable def ordered (tree : Tree) (L R : Point) : Bool :=
  positive L && positive R && sortedCore tree L R

private theorem le_iff {p q : Point} (hp : 0<p.den) (hq : 0<q.den) :
    before p q ↔ p.value≤q.value := by
  simp only [before,decide_eq_true_eq,Point.value,div_le_div_iff₀
    (show (0:ℚ)<p.den by exact_mod_cast hp) (show (0:ℚ)<q.den by exact_mod_cast hq)]
  exact_mod_cast Iff.rfl

private theorem tree_spec {tree : Tree} {L R : Point} (pl : 0<L.den) (pr : 0<R.den)
    (checked : sortedCore tree L R) :
    (∀ i, 0<(read tree i).den ∧ L.value≤(read tree i).value ∧ (read tree i).value≤R.value) ∧
    Monotone (fun i => (read tree i).value) := by
  induction tree generalizing L R with
  | leaf p =>
    simp only [sortedCore,Bool.and_eq_true,positive,decide_eq_true_eq] at checked
    obtain ⟨⟨⟨_,pd⟩,l⟩,r⟩ := checked
    exact ⟨fun _ => ⟨pd,(le_iff pl pd).mp l,(le_iff pd pr).mp r⟩,fun _ _ _ => le_rfl⟩
  | split k p l r il ir =>
    simp only [sortedCore,Bool.and_eq_true,positive,decide_eq_true_eq] at checked
    obtain ⟨⟨⟨⟨⟨_,pd⟩,lo⟩,hi⟩,lchk⟩,rchk⟩ := checked
    have lower := (le_iff pl pd).mp lo
    have upper := (le_iff pd pr).mp hi
    obtain ⟨lb,lm⟩ := il pl pd lchk
    obtain ⟨rb,rm⟩ := ir pd pr rchk
    constructor
    · intro i
      by_cases h : i<k
      · simpa only [read,if_pos h] using
          (show 0<(read l i).den ∧ L.value≤(read l i).value ∧ (read l i).value≤R.value from
          ⟨(lb i).1,(lb i).2.1,(lb i).2.2.trans upper⟩)
      · simpa only [read,if_neg h] using
          (show 0<(read r i).den ∧ L.value≤(read r i).value ∧ (read r i).value≤R.value from
          ⟨(rb i).1,lower.trans (rb i).2.1,(rb i).2.2⟩)
    · intro x y hxy
      by_cases h : y<k
      · simpa only [read,if_pos h,if_pos (lt_of_le_of_lt hxy h)] using lm hxy
      · by_cases hx : x<k
        · simpa only [read,if_neg h,if_pos hx] using (lb x).2.2.trans (rb y).2.1
        · simpa only [read,if_neg h,if_neg hx] using rm hxy

/-- With no left (respectively right) neighbor, that boundary is automatically
valid. The far side of each failed neighbor lies beyond the slope minimizer. -/
private noncomputable def bounds (n m W : ℕ) (tree : Tree) (s : Slope) (g lo hi : ℕ) : Bool :=
  (lo==0 || (before (read tree (lo-1)) ⟨s.a,s.b⟩ && !covers n m s g (read tree (lo-1)))) &&
  (W≤hi || (before ⟨s.a,s.b⟩ (read tree hi) && !covers n m s g (read tree hi)))

private noncomputable def chain (n m W : ℕ) (tree : Tree) (s : Slope) (cap : ℕ) :
    List (ℕ×ℕ) → Bool
  | [] => cap==0
  | (lo,hi)::rest => decide (0<cap ∧ lo≤hi ∧ hi≤W ∧ hi-lo<cap) &&
      bounds n m W tree s (cap-1) lo hi && chain n m W tree s (hi-lo) rest

noncomputable def rowCheck (n m W : ℕ) (tree : Tree) (s : Slope) (bands : List (ℕ×ℕ)) : Bool :=
  decide (0<s.a ∧ 0<s.b) && chain n m W tree s W bands

private noncomputable def hit (n m W : ℕ) (tree : Tree) (s : Slope) (g : ℕ) : Finset ℕ :=
  (range W).filter fun i => covers n m s g (read tree i)

private theorem covers_mono {n m g h : ℕ} {s : Slope} {r : Point} (gh : g≤h)
    (ok : covers n m s g r) : covers n m s h r := by
  simp only [covers,decide_eq_true_eq] at ok ⊢
  have inc : cutoff m s g≤cutoff m s h := Nat.add_le_add_left (Nat.mul_le_mul_left _ gh) _
  exact ok.trans_le (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left inc 2))

private theorem hit_mono {n m W g h : ℕ} {tree : Tree} {s : Slope} (gh : g≤h) :
    hit n m W tree s g ⊆ hit n m W tree s h := by
  intro i hi
  obtain ⟨mem,c⟩ := mem_filter.mp hi
  exact mem_filter.mpr ⟨mem,covers_mono gh c⟩

private theorem bound_inside {n m W g lo hi : ℕ} {tree : Tree} {s : Slope} {L R : Point}
    (sort : ordered tree L R) (sa : 0<s.a) (sb : 0<s.b)
    (witness : bounds n m W tree s g lo hi) : hit n m W tree s g ⊆ Ico lo hi := by
  simp only [ordered,Bool.and_eq_true,positive,decide_eq_true_eq] at sort
  obtain ⟨⟨⟨_,lp⟩,⟨_,rp⟩⟩,checked⟩ := sort
  obtain ⟨spec,mono⟩ := tree_spec lp rp checked
  simp only [bounds,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq,
    Bool.not_eq_true'] at witness
  intro i hi'
  obtain ⟨idx,ok⟩ := mem_filter.mp hi'
  have iw := mem_range.mp idx
  apply mem_Ico.mpr
  constructor
  · by_contra! low
    obtain bypass|⟨side,fail⟩ := witness.1
    · omega
    have b := (le_iff (spec i).1 (spec (lo-1)).1).mpr (mono (show i≤lo-1 by omega))
    have yes := of_left sa sb (spec i).1 (spec (lo-1)).1 b side ok
    simp [fail] at yes
  · by_contra! high
    obtain bypass|⟨side,fail⟩ := witness.2
    · omega
    have b := (le_iff (spec hi).1 (spec i).1).mpr (mono high)
    have yes := of_right sa sb (spec hi).1 (spec i).1 b side ok
    simp [fail] at yes

private theorem chain_sound {n m W cap : ℕ} {tree : Tree} {s : Slope} {L R : Point}
    (sort : ordered tree L R) (sa : 0<s.a) (sb : 0<s.b) (steps : List (ℕ×ℕ))
    (accepted : chain n m W tree s cap steps) : ∀ g<cap, (hit n m W tree s g).card≤g := by
  induction steps generalizing cap with
  | nil => simp only [chain,beq_iff_eq] at accepted; omega
  | cons entry rest ih =>
    obtain ⟨lo,hi⟩ := entry
    simp only [chain,Bool.and_eq_true,decide_eq_true_eq] at accepted
    obtain ⟨⟨⟨_,_,_,_⟩,witness⟩,more⟩ := accepted
    intro g h
    by_cases cheaper : g<hi-lo
    · exact ih more g cheaper
    · have subset := (hit_mono (show g≤cap-1 by omega)).trans (bound_inside sort sa sb witness)
      have count := card_le_card subset
      rw [Nat.card_Ico] at count
      omega

private theorem row_sound {n m W g : ℕ} {tree : Tree} {s : Slope} {L R : Point}
    (sort : ordered tree L R) {steps : List (ℕ×ℕ)} (accepted : rowCheck n m W tree s steps) :
    (hit n m W tree s g).card≤g := by
  simp only [rowCheck,Bool.and_eq_true,decide_eq_true_eq] at accepted
  by_cases h : g<W
  · exact chain_sound sort accepted.1.1 accepted.1.2 _ accepted.2 g h
  · have z := card_le_card (filter_subset (fun i => covers n m s g (read tree i)) (range W))
    simp only [card_range] at z
    exact z.trans (by omega)

noncomputable def batchCheck (n m W : ℕ) (tree : Tree) (rows : List (Slope × List (ℕ×ℕ))) : Bool :=
  rows.all fun e => rowCheck n m W tree e.1 e.2

theorem batchCheck_append (n m W : ℕ) (tree : Tree) (x y : List (Slope × List (ℕ×ℕ))) :
    batchCheck n m W tree (x++y)=(batchCheck n m W tree x && batchCheck n m W tree y) := by
  simp [batchCheck]

theorem rows_sound {n m W : ℕ} {tree : Tree} {rows : List (Slope × List (ℕ×ℕ))}
    (accepted : batchCheck n m W tree rows) :
    ∀ s∈rows.map Prod.fst, ∃ steps, rowCheck n m W tree s steps := by
  intro s hs
  obtain ⟨⟨s',steps⟩,mem,rfl⟩ := List.mem_map.mp hs
  exact ⟨steps,List.all_eq_true.mp accepted _ mem⟩

private noncomputable def visited (n m W : ℕ) (tree : Tree) : List (Slope×ℕ) → Finset ℕ
  | [] => ∅
  | (s,g)::rest => hit n m W tree s g ∪ visited n m W tree rest

private theorem hit_visited {n m W : ℕ} {tree : Tree} {schedule : List (Slope×ℕ)}
    {e : Slope×ℕ} (mem : e∈schedule) : hit n m W tree e.1 e.2 ⊆ visited n m W tree schedule := by
  induction schedule with
  | nil => simp at mem
  | cons row tail ih =>
    rcases List.mem_cons.mp mem with rfl|rest
    · exact subset_union_left
    · exact (ih rest).trans subset_union_right

private theorem visited_price {n m W : ℕ} {tree : Tree} {schedule : List (Slope×ℕ)}
    (bounds : ∀ e∈schedule, (hit n m W tree e.1 e.2).card≤e.2) :
    (visited n m W tree schedule).card≤cost schedule := by
  induction schedule with
  | nil => exact le_rfl
  | cons row tail ih =>
    obtain ⟨s,g⟩ := row
    change (hit n m W tree s g ∪ visited n m W tree tail).card ≤ g+cost tail
    have first := bounds (s,g) (List.mem_cons_self)
    have tailBound := ih fun e he => bounds e (List.mem_cons_of_mem _ he)
    exact (card_union_le (hit n m W tree s g) (visited n m W tree tail)).trans
      (Nat.add_le_add first tailBound)

/-- Every one of the W tickets lies at a ratio in the balanced region.
Even repeated slope entries in an alternative must collectively pay at least W. -/
theorem lower_sound {n m W : ℕ} {tree : Tree} {catalogue : List Slope}
    {schedule : List (Slope×ℕ)} {left right : Point}
    (sort : ordered tree left right)
    (checked : ∀ s∈catalogue, ∃ steps, rowCheck n m W tree s steps)
    (inside : ∀ e∈schedule, e.1∈catalogue) (cov : CoversRange n m schedule left right) :
    W≤cost schedule := by
  have data := sort
  simp only [ordered,Bool.and_eq_true,positive,decide_eq_true_eq] at data
  obtain ⟨⟨⟨_,lp⟩,⟨_,rp⟩⟩,core⟩ := data
  have spec := (tree_spec lp rp core).1
  have all : range W ⊆ visited n m W tree schedule := by
    intro i hi
    obtain ⟨d,lo,up⟩ := spec i
    obtain ⟨e,mem,ok⟩ := cov (read tree i) d ((le_iff lp d).mpr lo) ((le_iff d rp).mpr up)
    exact hit_visited mem (mem_filter.mpr ⟨hi,ok⟩)
  rw [←card_range W]
  apply (card_le_card all).trans
  apply visited_price
  intro e he
  obtain ⟨steps,proof⟩ := checked _ (inside _ he)
  exact row_sound sort proof

/-- Direct certificate entry point for a catalogue accompanied by the
sparse chains. The generated slopes and bounds may all depend on the input. -/
theorem lower_of_batch {n m W : ℕ} {tree : Tree} {rows : List (Slope × List (ℕ×ℕ))}
    {schedule : List (Slope×ℕ)} {left right : Point}
    (proof : batchCheck n m W tree rows) (sort : ordered tree left right)
    (allowed : admissible (rows.map Prod.fst) schedule) (cov : CoversRange n m schedule left right) :
    W≤cost schedule := by
  exact lower_sound sort (rows_sound proof) (fun _ he => catalogue_member allowed he) cov

end PrimeFactors.SparseTraceDual
