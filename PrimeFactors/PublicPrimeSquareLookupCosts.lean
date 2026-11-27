import PrimeFactors.PublicPrimeSquareCounts

/-! Scalar lookup counts when the seven prime tables are replaced by seven
prime-square tables. Each candidate is already in the sole modulo-four class.
Both comparisons use the same full public interval and charge one lookup per
position reaching each successive table. -/
namespace PrimeFactors.PublicPrimeSquareLookupCosts

open ChebyshevQuarticScale (fresh crossed)
open PublicWheelWidthControls (width tests period_bounds)
open PublicWheelLookupCosts (work prefixes ByPassingFraction)
open LocalSumMenu (count)

def freshOrder : List ℕ := [9,25,49,121,169,289,361]
def crossedOrder : List ℕ := [9,25,49,361,121,169,289]

/-- Space for one bit per residue in each of the seven tables. The byte
counts round each table separately. Object headers and the mod-four rule are excluded. -/
theorem table_sizes :
    PublicWheelLookupCosts.ascending.sum = 75 ∧ PublicPrimeSquareCounts.squares.sum = 1023 ∧
    (PublicWheelLookupCosts.ascending.map (fun p => (p+7)/8)).sum = 13 ∧
    (PublicPrimeSquareCounts.squares.map (fun m => (m+7)/8)).sum = 134 := by decide

theorem same_square_tests :
    freshOrder.Perm PublicPrimeSquareCounts.squares ∧ crossedOrder.Perm PublicPrimeSquareCounts.squares ∧
    4*freshOrder.prod = PublicPrimeSquareCounts.modulus ∧ 4*crossedOrder.prod = PublicPrimeSquareCounts.modulus ∧
    (prefixes 4 freshOrder).Forall₂ Nat.Coprime freshOrder ∧
    (prefixes 4 crossedOrder).Forall₂ Nat.Coprime crossedOrder := by
  refine ⟨List.isPerm_iff.mp (by decide), List.isPerm_iff.mp (by decide), ?_⟩
  decide

private theorem crt_count {a b : ℕ} (cop : a.Coprime b) (n : ℕ) :
    count n (a*b) = count n a * count n b := card_admissibleSum_crt cop n

private theorem parts {n a b c d e f g : ℕ}
    (cert : PublicPrimeSquareCounts.squares.map (count n) = [a,b,c,d,e,f,g]) :
    count n 9=a ∧ count n 25=b ∧ count n 49=c ∧ count n 121=d ∧ count n 169=e ∧
    count n 289=f ∧ count n 361=g := by
  simpa only [PublicPrimeSquareCounts.squares, List.map_cons, List.map_nil, List.cons.injEq,
    and_true] using cert

theorem fresh_stages : ByPassingFraction fresh freshOrder ∧
    (prefixes 4 freshOrder).map (count fresh) = [1,2,14,294,16170,1261260,171531360] := by
  obtain ⟨a,b,c,d,e,f,g⟩ := parts PublicPrimeSquareCounts.fresh_components
  have four : count fresh 4=1 := IntervalWheelResidues.count_four (by decide +kernel)
  simp (disch := decide) only [ByPassingFraction, freshOrder, prefixes, List.map_cons, List.map_nil,
    List.pairwise_cons, List.forall_mem_cons, List.not_mem_nil, false_implies, forall_const, crt_count,
    four, a,b,c,d,e,f,g]
  decide +kernel

theorem crossed_stages : ByPassingFraction crossed crossedOrder ∧
    (prefixes 4 crossedOrder).map (count crossed) = [1,2,14,224,34496,1897280,147987840] := by
  obtain ⟨a,b,c,d,e,f,g⟩ := parts PublicPrimeSquareCounts.crossed_components
  have four : count crossed 4=1 := IntervalWheelResidues.count_four (by decide +kernel)
  simp (disch := decide) only [ByPassingFraction, crossedOrder, prefixes, List.map_cons, List.map_nil,
    List.pairwise_cons, List.forall_mem_cons, List.not_mem_nil, false_implies, forall_const, crt_count,
    four, a,b,c,d,e,f,g]
  decide +kernel

/-- Multiply the class count in each prefix modulus by a number of repeats. -/
noncomputable def repeatedWork (n : ℕ) (order : List ℕ) (repeatCount : ℕ → ℕ) :=
  let ms := prefixes 4 order
  (List.zipWith (·*·) (ms.map repeatCount) (ms.map (count n))).sum

theorem complete_period :
    repeatedWork fresh freshOrder (PublicPrimeSquareCounts.modulus / ·) = 31317251690725 ∧
    repeatedWork crossed crossedOrder (PublicPrimeSquareCounts.modulus / ·) = 31028596880281 := by
  simp only [repeatedWork, fresh_stages.2, crossed_stages.2]
  decide +kernel

/-- The published interval bounds apply to each proper prefix. This allows
the final incomplete period to contribute anywhere from zero to all prefix classes. -/
theorem finite_bounds {n lo hi : ℕ} (order : List ℕ) (pos : ∀ m ∈ prefixes 4 order, 0<m)
    (bounds : lo ≤ width n ∧ width n ≤ hi) :
    repeatedWork n order (lo/·) ≤ work n order ∧
    work n order ≤ repeatedWork n order (fun m => hi/m+1) := by
  unfold repeatedWork work
  generalize hp : prefixes 4 order = ms at *
  clear hp
  induction ms with
  | nil => simp
  | cons m ms ih =>
    obtain ⟨rest₁,rest₂⟩ := ih (fun p h => pos p (List.mem_cons_of_mem _ h))
    obtain ⟨low,high⟩ := period_bounds n m (pos m (by simp))
    have l := (Nat.mul_le_mul_right (count n m) (Nat.div_le_div_right bounds.1)).trans low
    have h := high.trans (Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.div_le_div_right bounds.2)))
    exact ⟨Nat.add_le_add l rest₁, Nat.add_le_add h rest₂⟩

/-- Bounds for the actual intervals, in units of 10^300 scalar lookups. -/
theorem fresh_absolute :
    851322*10^300 ≤ work fresh freshOrder ∧ work fresh freshOrder ≤ 851323*10^300 := by
  have w : 2557561*10^300 ≤ width fresh ∧ width fresh ≤ 2557562*10^300 :=
    PublicWheelLookupCosts.width_between (by decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨l,h⟩ := finite_bounds freshOrder (by simp [prefixes, freshOrder]) w
  simp only [repeatedWork, fresh_stages.2] at l h
  exact ⟨le_trans (by decide +kernel) l, le_trans h (by decide +kernel)⟩

theorem crossed_absolute :
    3670759*10^300 ≤ work crossed crossedOrder ∧ work crossed crossedOrder ≤ 3670760*10^300 := by
  have w : 11130366*10^300 ≤ width crossed ∧ width crossed ≤ 11130367*10^300 :=
    PublicWheelLookupCosts.width_between (by decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨l,h⟩ := finite_bounds crossedOrder (by simp [prefixes, crossedOrder]) w
  simp only [repeatedWork, crossed_stages.2] at l h
  exact ⟨le_trans (by decide +kernel) l, le_trans h (by decide +kernel)⟩

/-- Saving relative to the previously verified sorted first-power tests,
measured in parts per million of that earlier lookup count. -/
def saving (n : ℕ) (old new : List ℕ) (lo hi : ℕ) : Prop :=
  let base := work n old
  let saved := base-work n new
  lo*base ≤ 1000000*saved ∧ 1000000*saved ≤ hi*base

theorem fresh_saving : saving fresh PublicWheelLookupCosts.freshOrder freshOrder 255195 255197 := by
  obtain ⟨a,b⟩ := PublicWheelLookupCosts.fresh_absolute.2
  obtain ⟨c,d⟩ := fresh_absolute
  unfold saving
  omega

theorem crossed_saving : saving crossed PublicWheelLookupCosts.crossedOrder crossedOrder 291721 291723 := by
  obtain ⟨a,b⟩ := PublicWheelLookupCosts.crossed_absolute.2
  obtain ⟨c,d⟩ := crossed_absolute
  unfold saving
  omega

end PrimeFactors.PublicPrimeSquareLookupCosts
