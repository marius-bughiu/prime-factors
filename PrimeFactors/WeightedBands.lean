import PrimeFactors.Multiplier
import Mathlib.Order.Interval.Finset.Nat

namespace PrimeFactors

/-- The weighted trace for a relaxed factor pair `(x,N/x)`. -/
noncomputable def weightedBandTrace (N a b x : ℝ) := a*x+b*N/x

private theorem card_le_real_diameter (s : Finset ℕ) {D : ℝ} (nonneg : 0 ≤ D)
    (diam : ∀ x ∈ s, ∀ y ∈ s, x ≤ y → (y : ℝ)-x ≤ D) : (s.card : ℝ) ≤ D+1 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp; linarith
  let u := s.min' hs
  let v := s.max' hs
  have hu : u ∈ s := s.min'_mem hs
  have hv : v ∈ s := s.max'_mem hs
  have uv : u ≤ v := s.le_max' u hu
  have bound := Finset.card_le_card (show s ⊆ Finset.Icc u v from fun i hi =>
    Finset.mem_Icc.mpr ⟨s.min'_le i hi,s.le_max' i hi⟩)
  rw [Nat.card_Icc] at bound
  have exactBound : (s.card : ℝ)+u ≤ v+1 := by exact_mod_cast (show s.card+u ≤ v+1 by omega)
  linarith [diam u hu v hv uv]

private theorem labels_card {s : Finset ℕ} {labels : Finset ℤ} {f : ℕ → ℤ} {D : ℝ}
    (nonneg : 0 ≤ D) (maps : Set.MapsTo f s labels)
    (diam : ∀ x ∈ s, ∀ y ∈ s, x ≤ y → f x=f y → (y : ℝ)-x ≤ D) :
    (s.card : ℝ) ≤ labels.card*(D+1) := by
  rw [Finset.card_eq_sum_card_fiberwise maps,Nat.cast_sum]
  calc _ ≤ ∑ _j ∈ labels, (D+1) := by
         apply Finset.sum_le_sum
         intro j _
         apply card_le_real_diameter _ nonneg
         intro x hx y hy hxy
         obtain ⟨mx,fx⟩ := Finset.mem_filter.mp hx
         obtain ⟨my,fy⟩ := Finset.mem_filter.mp hy
         exact diam x mx y my hxy (fx.trans fy.symm)
       _ = _ := by simp; ring

/-- For points beyond distance D from the stationary point on either branch,
the diameter of one rounded trace level is at most X/(aD). -/
theorem weightedBand_level_diameter {N a b r X D x y : ℝ} (ha : 0<a) (hr : 0≤r)
    (center : a*r^2=b*N) (width : 0<D) (lo : 0<x) (order : x≤y) (upper : y≤X)
    (branch : y≤r-D ∨ r+D≤x)
    (level : ⌊weightedBandTrace N a b x⌋=⌊weightedBandTrace N a b y⌋) :
    y-x ≤ X/(a*D) := by
  let F := weightedBandTrace N a b
  have ypos := lo.trans_le order
  have same (u v : ℝ) (eq : ⌊F u⌋=⌊F v⌋) : F u-F v < 1 := by
    have low := Int.floor_le (F v)
    have high := Int.lt_floor_add_one (F u)
    rw [eq] at high
    linarith
  apply (le_div_iff₀ (mul_pos ha width)).mpr
  have leftId : x*(F x-F y)-a*(y-x)*(r-x)=a*(y-x)*r*(r-y)/y := by
    dsimp [F,weightedBandTrace]
    rw [← center]
    field_simp
    ring
  have rightId : y*(F y-F x)-a*(y-x)*(y-r)=a*(y-x)*r*(x-r)/x := by
    dsimp [F,weightedBandTrace]
    rw [← center]
    field_simp
    ring
  have gap := sub_nonneg.mpr order
  rcases branch with left | right
  · have ry : 0 ≤ r-y := by linarith
    have pos : 0≤a*(y-x)*r*(r-y)/y := by positivity
    have compare := mul_le_mul_of_nonneg_left (show D ≤ r-x by linarith) (mul_nonneg ha.le gap)
    nlinarith only [leftId,pos,compare,mul_lt_mul_of_pos_left (same x y level) lo,order,upper]
  · have xr : 0 ≤ x-r := by linarith
    have pos : 0≤a*(y-x)*r*(x-r)/x := by positivity
    have compare := mul_le_mul_of_nonneg_left (show D ≤ y-r by linarith) (mul_nonneg ha.le gap)
    nlinarith only [rightId,pos,compare,mul_lt_mul_of_pos_left (same y x level.symm) ypos,upper]

/-- Any finite portfolio of rounded labels on a single slope covers at most
this many integer factor candidates, regardless of the positions of the labels. -/
theorem weightedBand_single_count {N a b r X D : ℝ} (ha : 0<a) (hr : 0≤r)
    (center : a*r^2=b*N) (hX : 0<X) (hD : 0<D) (s : Finset ℕ) (labels : Finset ℤ)
    (inside : ∀ x ∈ s, 0<(x : ℝ) ∧ (x : ℝ)≤X)
    (covered : ∀ x ∈ s, ⌊weightedBandTrace N a b x⌋ ∈ labels) :
    (s.card : ℝ) ≤ 2*D+1+2*labels.card*(1+X/(a*D)) := by
  classical
  let near := s.filter fun x : ℕ => r-D<(x : ℝ) ∧ (x : ℝ)<r+D
  let left := s.filter fun x : ℕ => (x : ℝ)≤r-D
  let right := s.filter fun x : ℕ => r+D≤(x : ℝ)
  have nearCard : (near.card : ℝ) ≤ 2*D+1 := by
    apply card_le_real_diameter _ (by positivity)
    intro x hx y hy _
    obtain ⟨_,lx,_⟩ := Finset.mem_filter.mp hx
    obtain ⟨_,_,ry⟩ := Finset.mem_filter.mp hy
    linarith
  have side (t : Finset ℕ) (mem : t ⊆ s)
      (oneSide : ∀ x ∈ t, ∀ y ∈ t, (y : ℝ)≤r-D ∨ r+D≤(x : ℝ)) :
      (t.card : ℝ) ≤ labels.card*(X/(a*D)+1) := by
    apply labels_card (by positivity) (fun x hx => covered x (mem hx))
    intro x hx y hy ord eq
    exact weightedBand_level_diameter ha hr center hD (inside x (mem hx)).1
      (by exact_mod_cast ord) (inside y (mem hy)).2 (oneSide x hx y hy) eq
  have lc := side left (Finset.filter_subset _ _) (fun _ _ _ hy => Or.inl (Finset.mem_filter.mp hy).2)
  have rc := side right (Finset.filter_subset _ _) (fun _ hx _ _ => Or.inr (Finset.mem_filter.mp hx).2)
  have all : s ⊆ near ∪ (left ∪ right) := by
    intro x hx
    simp only [near,left,right,Finset.mem_union,Finset.mem_filter,hx,true_and]
    by_cases h : (x : ℝ) ≤ r-D
    · exact Or.inr (Or.inl h)
    · by_cases j : r+D ≤ (x : ℝ)
      · exact Or.inr (Or.inr j)
      · exact Or.inl ⟨lt_of_not_ge h,lt_of_not_ge j⟩
  have count : s.card ≤ near.card + (left.card+right.card) :=
    (Finset.card_le_card all).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left (Finset.card_union_le _ _) _))
  have realCount : (s.card : ℝ) ≤ near.card + (left.card+right.card : ℝ) := by exact_mod_cast count
  linarith

/-- Optimizing the cut around the stationary point leaves only a square-root
dependence on the number of distinct labels at this slope. -/
theorem weightedBand_single_optimized {N a b X : ℝ} (ha : 0<a) (hb : 0≤b*N)
    (hX : 0<X) (s : Finset ℕ) (labels : Finset ℤ) (nonempty : labels.Nonempty)
    (inside : ∀ x ∈ s, 0<(x : ℝ) ∧ (x : ℝ)≤X)
    (covered : ∀ x ∈ s, ⌊weightedBandTrace N a b x⌋ ∈ labels) :
    (s.card : ℝ) ≤ 1+2*labels.card+4*Real.sqrt (X*labels.card/a) := by
  let r := Real.sqrt (b*N/a)
  let D := Real.sqrt (X*labels.card/a)
  have hL : (0 : ℝ)<labels.card := by exact_mod_cast Finset.card_pos.mpr nonempty
  have hd : 0<D := by dsimp [D]; positivity
  have center : a*r^2=b*N := by
    dsimp [r]
    rw [Real.sq_sqrt (div_nonneg hb ha.le)]
    field_simp
  have opt : (labels.card : ℝ)*(X/(a*D))=D := by
    rw [← mul_div_assoc,div_eq_iff (mul_pos ha hd).ne']
    have sq : D^2=X*labels.card/a := Real.sq_sqrt (by positivity)
    have h := (eq_div_iff ha.ne').mp sq
    nlinarith only [h]
  have bound := weightedBand_single_count ha (Real.sqrt_nonneg _) center hX hd s labels inside covered
  change (s.card : ℝ) ≤ 1+2*labels.card+4*D
  nlinarith only [bound,opt]

/-- Distinct positive weight pairs with b ≤ 2a have bounded reciprocal
mass even when selected from the public product and allocated unevenly. -/
theorem weightedBand_reciprocal_cap (P : Finset (ℕ × ℕ)) {B : ℕ} (hB : 0<B)
    (regular : ∀ w ∈ P, 0<w.1 ∧ 0<w.2 ∧ w.2≤2*w.1) :
    (∑ w ∈ P, (1 : ℝ)/w.1) ≤ 2*B+P.card/B := by
  classical
  let low := P.filter (fun w : ℕ × ℕ => w.1≤B)
  let high := P.filter (fun w : ℕ × ℕ => ¬w.1≤B)
  let rows := Finset.Icc 1 B
  have keys : Set.MapsTo (Prod.fst : ℕ × ℕ → ℕ) (↑low : Set (ℕ × ℕ)) (↑rows : Set ℕ) := by
    intro w hw
    change w ∈ P.filter (fun v : ℕ × ℕ => v.1≤B) at hw
    obtain ⟨mem, bound⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_Icc.mpr ⟨(regular w mem).1,bound⟩
  have first (i : ℕ) (hi : i∈rows) :
      (∑ w ∈ low.filter (fun w : ℕ × ℕ => w.1=i), (1 : ℝ)/w.1) ≤ 2 := by
    let row := low.filter (fun w : ℕ × ℕ => w.1=i)
    have key {w : ℕ × ℕ} (hw : w ∈ row) := (Finset.mem_filter.mp hw).2
    have card : row.card ≤ (Finset.Icc 1 (2*i)).card := by
      apply Finset.card_le_card_of_injOn Prod.snd
      · intro w hw
        obtain ⟨_,pos,bound⟩ := regular w (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
        exact Finset.mem_Icc.mpr ⟨pos,key hw ▸ bound⟩
      · intro x hx y hy eq
        exact Prod.ext ((key hx).trans (key hy).symm) eq
    have upper : (row.card : ℝ) ≤ 2*i := by
      rw [Nat.card_Icc] at card
      exact_mod_cast (show row.card ≤ 2*i by omega)
    have pos : (0 : ℝ) < i := by exact_mod_cast (Finset.mem_Icc.mp hi).1
    calc _ = ∑ _w ∈ row, (1 : ℝ)/i := Finset.sum_congr rfl (fun _ hw => by rw [key hw])
         _ = row.card/i := by simp [div_eq_mul_inv]
         _ ≤ _ := (div_le_iff₀ pos).mpr upper
  have loCap : (∑ w ∈ low, (1 : ℝ)/w.1) ≤ 2*B := by
    rw [← Finset.sum_fiberwise_of_maps_to keys]
    calc _ ≤ ∑ _i ∈ rows, (2 : ℝ) := Finset.sum_le_sum first
         _ = _ := by simp [rows,Nat.card_Icc]; ring
  have hiCap : (∑ w ∈ high, (1 : ℝ)/w.1) ≤ P.card/B := by
    calc _ ≤ ∑ _w ∈ high, (1 : ℝ)/B := by
           apply Finset.sum_le_sum
           intro w hw
           apply one_div_le_one_div_of_le (by exact_mod_cast hB)
           exact_mod_cast (lt_of_not_ge (Finset.mem_filter.mp hw).2).le
         _ = high.card/B := by simp [div_eq_mul_inv]
         _ ≤ _ := by
           apply div_le_div_of_nonneg_right _ (by positivity)
           exact_mod_cast Finset.card_filter_le P _
  have split := Finset.sum_filter_add_sum_filter_not P (fun w : ℕ × ℕ => w.1≤B)
    (fun w => (1 : ℝ)/w.1)
  exact split ▸ add_le_add loCap hiCap

/-- When b exceeds a by at least one, the labels distinguish every integer
candidate below the square root of N. -/
theorem weightedBand_far_injective {N a b X : ℝ} (ha : 0≤a) (far : a+1≤b)
    (product : X^2=N) {x y : ℕ} (lo : 0<(x : ℝ)) (ordered : x<y) (upper : (y : ℝ)≤X) :
    ⌊weightedBandTrace N a b y⌋ < ⌊weightedBandTrace N a b x⌋ := by
  have ord : (x : ℝ)+1≤y := by exact_mod_cast ordered
  have yPos : (0 : ℝ) < y := by linarith
  let F := weightedBandTrace N a b
  have id : (F x-F y)*(x*y)=(y-x)*(b*N-a*(x*y)) := by
    dsimp [F,weightedBandTrace]
    field_simp
    ring
  have xy : (x*y : ℝ) ≤ N := by
    rw [← product,pow_two]
    gcongr <;> linarith
  have gap : F y+1≤F x := by
    have m₁ := mul_le_mul_of_nonneg_left xy (show 0 ≤ b by linarith)
    have m₂ := mul_le_mul_of_nonneg_right far (mul_nonneg lo.le yPos.le)
    have m₃ := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ y-x by linarith)
      (show 0≤b*N-a*(x*y) by nlinarith only [m₁,m₂, mul_nonneg lo.le yPos.le])
    apply le_of_mul_le_mul_right _ (mul_pos lo yPos)
    nlinarith only [id,m₁,m₂,m₃]
  have := Int.floor_mono gap
  rw [Int.floor_add_one] at this
  change ⌊F y⌋ < ⌊F x⌋
  omega

/-- Simultaneous coverage for a finite collection of weights. A separate
set of arbitrary integer labels may be assigned to each weight. -/
theorem weightedBand_portfolio_count (P : Finset (ℕ × ℕ)) (labels : ℕ × ℕ → Finset ℤ)
    (points : ℕ × ℕ → Finset ℕ) {N X : ℝ} (pos : 0≤N) (hX : 0<X) {B : ℕ} (hB : 0<B)
    (regular : ∀ w ∈ P, 0<w.1 ∧ 0<w.2 ∧ w.2≤2*w.1)
    (nonempty : ∀ w ∈ P, (labels w).Nonempty)
    (inside : ∀ w ∈ P, ∀ x ∈ points w, 0<(x : ℝ) ∧ (x : ℝ)≤X)
    (covered : ∀ w ∈ P, ∀ x ∈ points w, ⌊weightedBandTrace N w.1 w.2 x⌋ ∈ labels w) :
    let L : ℝ := ∑ w ∈ P, ((labels w).card : ℝ)
    ((P.biUnion points).card : ℝ) ≤ P.card+2*L+4*Real.sqrt (X*L*(2*B+P.card/B)) := by
  let l (w : ℕ × ℕ) : ℝ := (labels w).card
  let z (w : ℕ × ℕ) := Real.sqrt (X*l w/w.1)
  have term (w : ℕ × ℕ) (hw : w ∈ P) :
      ((points w).card : ℝ) ≤ 1+2*l w+4*z w :=
    weightedBand_single_optimized (by exact_mod_cast (regular w hw).1)
      (mul_nonneg (Nat.cast_nonneg _) pos) hX _ _ (nonempty w hw) (inside w hw) (covered w hw)
  have sumBound := Finset.sum_le_sum term
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.sum_mul,← Finset.mul_sum,
    nsmul_eq_mul,mul_one] at sumBound
  have cs := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul P (f := fun w => X*l w)
    (g := fun w => (1 : ℝ)/w.1) (r := z) (fun w _ => mul_nonneg hX.le (Nat.cast_nonneg _))
    (fun _ _ => by positivity) (fun w _ => by
      dsimp [z]
      rw [Real.sq_sqrt (div_nonneg (mul_nonneg hX.le (Nat.cast_nonneg _)) (Nat.cast_nonneg _))]
      ring)
  rw [← Finset.mul_sum] at cs
  have recip := weightedBand_reciprocal_cap P hB regular
  have rad := cs.trans (mul_le_mul_of_nonneg_left recip
    (mul_nonneg hX.le (Finset.sum_nonneg fun w _ => Nat.cast_nonneg (labels w).card)))
  have zCap := Real.le_sqrt_of_sq_le rad
  have card : ((P.biUnion points).card : ℝ) ≤ ∑ w ∈ P, ((points w).card : ℝ) := by
    exact_mod_cast Finset.card_biUnion_le
  exact card.trans (sumBound.trans (by dsimp only [l] at *; linarith))

/-- A sparse shared baby table can hit the true factor without covering the
whole relaxed interval. This fixture exhibits the distinction explicitly. -/
theorem weightedBand_sparse_example :
    let N := 15049
    let giants : List (ℕ × ℕ × ℕ) := [(1,1,246),(3,2,601),(2,1,347),(4,3,850)]
    let babies : List ℕ := [0,3,7,10]
    let hit (x : ℕ) := giants.any fun (a,b,c) =>
      babies.any fun j => (a*x*x+b*N)/x == c+j
    ((List.range 30).filter fun i => hit (93+i)).length=24 ∧ hit 101=true ∧ N=101*149 := by
  decide +kernel

end PrimeFactors
