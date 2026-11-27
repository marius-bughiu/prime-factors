import PrimeFactors.PublicWheelWidthControls

/-! Scalar lookups on the two published intervals. Passing the mod-four
test is the starting condition. Each odd-prime lookup is charged once for
every position still present before that prime. -/
namespace PrimeFactors.PublicWheelLookupCosts

open ChebyshevQuarticScale (fresh crossed)
open PublicWheelWidthControls (width tests)
open IntervalWheelResidues (modulus)
open LocalSumMenu (count)

def ascending : List ℕ := [3, 5, 7, 11, 13, 17, 19]
def freshOrder : List ℕ := [7, 11, 13, 17, 19, 5, 3]
def crossedOrder : List ℕ := [11, 13, 17, 19, 7, 5, 3]

/-- The moduli for survivors arriving at each lookup. The final survivors
are excluded from this list because there is no eighth odd-prime lookup. -/
def prefixes (m : ℕ) : List ℕ → List ℕ
  | [] => []
  | p :: rest => m :: prefixes (m*p) rest

/-- CRT makes the next prefix equivalent to the preceding prefix and the
single prime test, so its cardinality measures the next stage's input. -/
theorem extend_prefix {m p : ℕ} (cop : m.Coprime p) (n s : ℕ) :
    AdmissibleSum (n : ZMod (m*p)) (s : ZMod (m*p)) ↔
    AdmissibleSum (n : ZMod m) (s : ZMod m) ∧ AdmissibleSum (n : ZMod p) (s : ZMod p) := by
  simpa only [map_natCast, Prod.fst_natCast, Prod.snd_natCast] using
    admissibleSum_crt_iff cop (n : ZMod (m*p)) (s : ZMod (m*p))

/-- For odd products the first prefix means exactly the ordinary mod-four starting class. -/
theorem first_prefix {n : ℕ} (odd : n%2=1) (s : ℕ) :
    AdmissibleSum (n : ZMod 4) (s : ZMod 4) ↔ s%4=(n+1)%4 := by
  have four : ∀ x y : ZMod 4, x.val%2=1 → (AdmissibleSum x y ↔ y = x+1) := by
    unfold AdmissibleSum
    decide +kernel
  have h : (n : ZMod 4).val%2=1 := by
    rwa [ZMod.val_natCast, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 4)]
  calc
    _ ↔ (s : ZMod 4) = (n : ZMod 4)+1 := four _ _ h
    _ ↔ (s : ZMod 4) = ((n+1 : ℕ) : ZMod 4) := by push_cast; rfl
    _ ↔ (s : ZMod 4).val = ((n+1 : ℕ) : ZMod 4).val :=
      ⟨congrArg ZMod.val, fun h => ZMod.val_injective 4 h⟩
    _ ↔ _ := by simp only [ZMod.val_natCast]

/-- Every individual lookup in these orders satisfies the CRT extension hypothesis. -/
theorem coprime_steps :
    (prefixes 4 ascending).Forall₂ Nat.Coprime ascending ∧
    (prefixes 4 freshOrder).Forall₂ Nat.Coprime freshOrder ∧
    (prefixes 4 crossedOrder).Forall₂ Nat.Coprime crossedOrder := by
  decide +kernel

/-- These are full-interval stage cardinalities, including a possible partial period. -/
noncomputable def work (n : ℕ) (order : List ℕ) := ((prefixes 4 order).map (tests n)).sum

/-- Every surviving class modulo a prefix m repeats exactly modulus/m
times per joint wheel period. -/
noncomputable def periodicWork (n : ℕ) (order : List ℕ) :=
  ((prefixes 4 order).map fun m => (modulus/m)*count n m).sum

private theorem stage_bounds {n m : ℕ} (dvd : m ∣ modulus) :
    width n/modulus*((modulus/m)*count n m) ≤ tests n m ∧
    tests n m ≤ (width n/modulus+1)*((modulus/m)*count n m) := by
  have pos : 0 < m := Nat.pos_of_dvd_of_pos dvd (by decide)
  have copies : 0 < modulus/m := Nat.div_pos (Nat.le_of_dvd (by decide) dvd) pos
  have split : width n/m/(modulus/m) = width n/modulus := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_div_cancel' dvd]
  have lo := Nat.div_mul_le_self (width n/m) (modulus/m)
  have hi := Nat.lt_mul_div_succ (width n/m) copies
  rw [split] at lo hi
  obtain ⟨small, large⟩ := PublicWheelWidthControls.period_bounds n m pos
  constructor
  · rw [← Nat.mul_assoc]
    exact (Nat.mul_le_mul_right _ lo).trans small
  · rw [← Nat.mul_assoc, Nat.mul_comm (width n/modulus+1)]
    exact large.trans (Nat.mul_le_mul_right _ hi)

/-- Any ordering whose prefix moduli divide the joint period has at most
one full period of rounding error in its scalar lookup count. -/
theorem finite_bounds (n : ℕ) (order : List ℕ) (dvd : ∀ m ∈ prefixes 4 order, m ∣ modulus) :
    width n/modulus * periodicWork n order ≤ work n order ∧
    work n order ≤ (width n/modulus+1) * periodicWork n order := by
  unfold periodicWork work
  generalize hp : prefixes 4 order = ps at *
  clear hp
  induction ps with
  | nil => simp
  | cons m ps ih =>
    obtain ⟨small, large⟩ := stage_bounds (n:=n) (dvd m (by simp))
    obtain ⟨rest₁, rest₂⟩ := ih (fun p hp => dvd p (List.mem_cons_of_mem _ hp))
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    exact ⟨Nat.add_le_add small rest₁, Nat.add_le_add large rest₂⟩

private theorem crt_count {a b : ℕ} (cop : a.Coprime b) (n : ℕ) :
    count n (a*b) = count n a * count n b := card_admissibleSum_crt cop n

private theorem valid_orders :
    (∀ m ∈ prefixes 4 ascending, m ∣ modulus) ∧
    (∀ m ∈ prefixes 4 freshOrder, m ∣ modulus) ∧
    (∀ m ∈ prefixes 4 crossedOrder, m ∣ modulus) := by
  simp [prefixes, ascending, freshOrder, crossedOrder, modulus]

/-- Both alternative orders test the same set of primes and give the same
final modulus, so the existing wheel survivor certificates apply verbatim. -/
theorem same_tests :
    freshOrder.Perm ascending ∧ crossedOrder.Perm ascending ∧
    4*freshOrder.prod = modulus ∧ 4*crossedOrder.prod = modulus ∧ 4*ascending.prod = modulus := by
  refine ⟨List.isPerm_iff.mp (by decide), List.isPerm_iff.mp (by decide), ?_⟩
  decide

def ByPassingFraction (n : ℕ) (order : List ℕ) : Prop :=
  order.Pairwise fun a b => count n a * b < count n b * a

private theorem components_eq {n a b c d e f g h : ℕ}
    (cert : IntervalWheelControls.components.map (count n) = [a,b,c,d,e,f,g,h]) :
    count n 4=a ∧ count n 3=b ∧ count n 5=c ∧ count n 7=d ∧ count n 11=e ∧
    count n 13=f ∧ count n 17=g ∧ count n 19=h := by
  simpa only [IntervalWheelControls.components, List.map_cons, List.map_nil,
    List.cons.injEq, and_true] using cert

theorem fresh_period :
    ByPassingFraction fresh freshOrder ∧
    periodicWork fresh ascending = 11488825 ∧ periodicWork fresh freshOrder = 8669895 := by
  obtain ⟨a,b,c,d,e,f,g,h⟩ := components_eq IntervalWheelControls.fresh_components
  simp (disch := decide) only [ByPassingFraction, ascending, freshOrder, periodicWork,
    prefixes, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.pairwise_cons, List.forall_mem_cons, List.not_mem_nil, false_implies,
    forall_const, crt_count, a,b,c,d,e,f,g,h]
  decide +kernel

theorem crossed_period :
    ByPassingFraction crossed crossedOrder ∧
    periodicWork crossed ascending = 11977429 ∧ periodicWork crossed crossedOrder = 9032970 := by
  obtain ⟨a,b,c,d,e,f,g,h⟩ := components_eq IntervalWheelControls.crossed_components
  simp (disch := decide) only [ByPassingFraction, ascending, crossedOrder, periodicWork,
    prefixes, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.pairwise_cons, List.forall_mem_cons, List.not_mem_nil, false_implies,
    forall_const, crt_count, a,b,c,d,e,f,g,h]
  decide +kernel

private theorem many_periods {n : ℕ} (enough : 2^1015 ≤ PublicWheelWidthControls.raw n) :
    1000000000 ≤ width n/modulus := by
  apply (Nat.le_div_iff_mul_le (by decide)).mpr
  refine (show 1000000000*modulus ≤ 2^1015 by decide +kernel).trans (enough.trans ?_)
  simpa [PublicWheelWidthControls.raw] using Finset.card_filter_le
    (Finset.range (width n)) (fun i => (PublicWheelWidthControls.start n+i)%4=(n+1)%4)

/-- Finite-interval saving in parts per million of the ascending lookup count. -/
def saving (n : ℕ) (order : List ℕ) (lo hi : ℕ) : Prop :=
  let base := work n ascending
  let saved := base-work n order
  lo*base ≤ 1000000*saved ∧ 1000000*saved ≤ hi*base

theorem fresh_saving : saving fresh freshOrder 245362 245363 := by
  have blocks := many_periods PublicWheelWidthControls.fresh_comparison.1
  obtain ⟨a,b⟩ := finite_bounds fresh ascending valid_orders.1
  obtain ⟨c,d⟩ := finite_bounds fresh freshOrder valid_orders.2.1
  rw [fresh_period.2.1] at a b
  rw [fresh_period.2.2] at c d
  unfold saving
  omega

theorem crossed_saving : saving crossed crossedOrder 245833 245834 := by
  have blocks := many_periods ((show 2^1015 ≤ 2^1017 by decide +kernel).trans
    PublicWheelWidthControls.crossed_comparison.1)
  obtain ⟨a,b⟩ := finite_bounds crossed ascending valid_orders.1
  obtain ⟨c,d⟩ := finite_bounds crossed crossedOrder valid_orders.2.2
  rw [crossed_period.2.1] at a b
  rw [crossed_period.2.2] at c d
  unfold saving
  omega

/-- Bound the existing public width by comparing the squared lower endpoint
to the same product on both sides. This uses no residue or candidate enumeration. -/
private theorem width_between {n lo hi : ℕ}
    (room : lo ≤ PublicWheelWidthControls.stop n+1)
    (upperRoot : 4*n ≤ (PublicWheelWidthControls.stop n+1-lo)^2)
    (lowerRoot : (PublicWheelWidthControls.stop n+1-hi)^2 < 4*n) :
    lo ≤ width n ∧ width n ≤ hi := by
  have left : PublicWheelWidthControls.start n ≤ PublicWheelWidthControls.stop n+1-lo :=
    ceilSqrt_le_iff.mpr upperRoot
  have right : PublicWheelWidthControls.stop n+1-hi < PublicWheelWidthControls.start n := by
    apply Nat.lt_of_not_ge
    intro bad
    exact (not_le_of_gt lowerRoot) (ceilSqrt_le_iff.mp bad)
  unfold width
  omega

private theorem absolute_bounds {n lo hi wl wh jobs : ℕ} {order : List ℕ}
    (valid : ∀ m ∈ prefixes 4 order, m ∣ modulus)
    (period : periodicWork n order = jobs) (witness : wl ≤ width n ∧ width n ≤ wh)
    (lower : lo ≤ wl/modulus * jobs) (upper : (wh/modulus+1)*jobs ≤ hi) :
    lo ≤ work n order ∧ work n order ≤ hi := by
  obtain ⟨low, high⟩ := finite_bounds n order valid
  rw [period] at low high
  exact ⟨lower.trans ((Nat.mul_le_mul_right _ (Nat.div_le_div_right witness.1)).trans low),
    high.trans ((Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.div_le_div_right witness.2))).trans upper)⟩

/-- Rounded integer counts over the actual public intervals, in units of 10^300 lookups. -/
theorem fresh_absolute :
    (1514655*10^300 ≤ work fresh ascending ∧ work fresh ascending ≤ 1514656*10^300) ∧
    (1143015*10^300 ≤ work fresh freshOrder ∧ work fresh freshOrder ≤ 1143016*10^300) := by
  have w : 2557561*10^300 ≤ width fresh ∧ width fresh ≤ 2557562*10^300 :=
    width_between (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact ⟨absolute_bounds valid_orders.1 fresh_period.2.1 w (by decide +kernel) (by decide +kernel),
    absolute_bounds valid_orders.2.1 fresh_period.2.2 w (by decide +kernel) (by decide +kernel)⟩

theorem crossed_absolute :
    (6872032*10^300 ≤ work crossed ascending ∧ work crossed ascending ≤ 6872034*10^300) ∧
    (5182653*10^300 ≤ work crossed crossedOrder ∧ work crossed crossedOrder ≤ 5182654*10^300) := by
  have w : 11130366*10^300 ≤ width crossed ∧ width crossed ≤ 11130367*10^300 :=
    width_between (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact ⟨absolute_bounds valid_orders.1 crossed_period.2.1 w (by decide +kernel) (by decide +kernel),
    absolute_bounds valid_orders.2.2 crossed_period.2.2 w (by decide +kernel) (by decide +kernel)⟩

end PrimeFactors.PublicWheelLookupCosts
