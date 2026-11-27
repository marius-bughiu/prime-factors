import PrimeFactors.SquareDivisorCluePopulation
import PrimeFactors.SquareClueFactorWidth

/-! Count sums passing all four supplied clues and both endpoint constraints
for factors of exactly 1,024 bits. Near the top of the product box the true
width window can be arbitrarily narrow, so that corner is counted separately. -/
namespace PrimeFactors.SquareClueEndpointPopulation

open Finset FourNeighborScaleFrequency MixedPrefixSample
set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
attribute [local irreducible] eligible primes ordered X

private abbrev H : ℕ := 2^1024
private abbrev Q : ℕ := 2^1024-1

private theorem endpoint_succ : Q+1=H := by decide +kernel

noncomputable def corner (M : ℕ) : Finset (ℕ×ℕ) :=
  eligible.filter (fun z => Q < z.1+4*M)

private theorem facts {p q : ℕ} (ok : (p,q)∈eligible) :
    Odd p ∧ Odd q ∧ p<q ∧ q≤Q ∧ 2^2047≤p*q := by
  rw [eligible,sample,mem_filter] at ok
  obtain ⟨pm,qm,_,full,_⟩ := mem_ordered.mp ok.1
  rw [primes,mem_filter,mem_Ico] at pm qm
  have pl : X≤p := pm.1.1
  have ql : X≤q := qm.1.1
  have top : q<2*X := qm.1.2
  have big : 2<X := by unfold X; decide +kernel
  have exactTop : 2*X=H := by unfold X; decide +kernel
  have endSize := endpoint_succ
  have exactLow : 2*X^2=2^2047 := by unfold X; decide +kernel
  exact ⟨pm.2.odd_of_ne_two (by omega),qm.2.odd_of_ne_two (by omega),ok.2,by omega,exactLow ▸ full⟩

/-- Both primes in a corner pair lie in the last 4M integers. -/
theorem corner_count (M : ℕ) : (corner M).card≤(4*M)^2 := by
  let I := Ico (H-4*M) H
  have sub : corner M ⊆ I ×ˢ I := by
    rintro ⟨p,q⟩ hz
    obtain ⟨ok,high⟩ := mem_filter.mp hz
    obtain ⟨_,_,lt,top,_⟩ := facts ok
    change Q < p+4*M at high
    have endSize := endpoint_succ
    exact mem_product.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,mem_Ico.mpr ⟨by omega,by omega⟩⟩
  have len : I.card ≤ 4*M := by dsimp only [I]; rw [Nat.card_Ico]; omega
  exact (card_le_card sub).trans ((card_product ..).le.trans ((Nat.mul_le_mul len len).trans_eq (pow_two _).symm))

private theorem combined {L M e E : ℕ} (next : E=e+1)
    (scale : 2^E*(allSigns L).card < eligible.card)
    (edge : 21000000*(2^E*(4*M)^2) < 2^2046) :
    2^e*(allSigns L ∪ corner M).card < eligible.card := by
  subst E
  have cornerBound : 2^(e+1)*(corner M).card < eligible.card :=
    Nat.lt_of_mul_lt_mul_left ((Nat.mul_le_mul_left 21000000 (Nat.mul_le_mul_left _ (corner_count M))).trans_lt
      (edge.trans ChebyshevPrimeSample.eligible_count))
  have unionBound := Nat.mul_le_mul_left (2^e) (card_union_le (allSigns L) (corner M))
  rw [pow_succ] at scale cornerBound
  rw [Nat.mul_add] at unionBound
  rw [Nat.mul_right_comm (2^e) 2] at scale cornerBound
  omega

/-- The public upper bound tests both factor endpoints through sumCap. -/
noncomputable def survivors (p q : ℕ) (r : Bool → Bool → ℕ) :=
  (FourSquareDivisorClues.survivors (p*q) (p+q) (q-p) r).filter
    (· ≤ ProductDeficitBand.sumCap (p*q) X)

/-- For an eligible product, imposing sumCap on a surviving sum keeps exactly
the sums whose ordered real roots both meet the announced factor endpoints. -/
theorem mem_survivors_real_roots {p q s : ℕ} {x y : ℝ} (ok : (p,q)∈eligible)
    (r : Bool → Bool → ℕ) (order : x≤y) (product : x*y=((p*q:ℕ):ℝ)) (sum : x+y=(s:ℝ)) :
    s∈survivors p q r ↔ s∈FourSquareDivisorClues.survivors (p*q) (p+q) (q-p) r ∧
      (X:ℝ)≤x ∧ y≤((2*X-1:ℕ):ℝ) := by
  obtain ⟨_,_,ord,top,full⟩ := facts ok
  have high : q≤2*X-1 := top.trans_eq (by unfold X; decide +kernel)
  have lower : X^2≤p*q := (by unfold X; decide +kernel : X^2≤2^2047).trans full
  have upper : p*q≤(2*X-1)^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul (ord.le.trans high) high
  rw [survivors,mem_filter,SquareClueFactorWidth.sumCap_iff_real_roots
    (by unfold X; decide +kernel : 0<X) lower upper order product sum]

private theorem count {p q M L k W C : ℕ} (ok : (p,q)∈eligible)
    (typical : (p,q) ∉ allSigns L ∪ corner M) (r : Bool → Bool → ℕ)
    (positive : ∀ a b, 0<r a b) (given : ∀ a b, (r a b)^2 ∣ neighbor a p*neighbor b q)
    (rootBudget : H*H ≤ L*(2^k)^2) (widthBudget : Q*W≤M^2) (basic : W≤2^1020)
    (periodBudget : C*(2^k)^8 ≤ 64*W) : C≤(survivors p q r).card := by
  obtain ⟨op,oq,ord,top,full⟩ := facts ok
  have margin : p+4*M≤Q := by
    by_contra! high
    exact typical (mem_union_right _ (mem_filter.mpr ⟨ok,high⟩))
  have small (a b : Bool) (y : ℕ) (yd : y^2∣neighbor a p*neighbor b q) : y<2^k := by
    by_contra! large
    exact typical (mem_union_left _ (large_square_divisor ok a b yd large (by positivity) rootBudget))
  have lifts := fun a b => SquareDivisorClueWindow.even_lift (positive a b)
    (SquareDivisorClueWindow.four_dvd_neighbors a b op oq) (given a b)
  choose Y pos lift four div using lifts
  have disc : (q-p)^2+4*(p*q)=(p+q)^2 := by
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le ord.le
    rw [hd,Nat.add_sub_cancel_left]; ring
  have upper := SquareClueFactorWidth.upper_endpoint (by decide +kernel : 0<Q) top margin widthBudget
    (le_refl ((4*(p*q)).sqrt+W))
  have lower := SquareClueFactorWidth.both_endpoints (by unfold X; decide +kernel : 0<X)
    (by unfold X; decide +kernel : X≤Q) ((by unfold X; decide +kernel : X*Q≤2^2047).trans full) upper
  have defQ : 2*X-1=Q := by unfold X; decide +kernel
  apply FourSquareDivisorClues.count_below_from_lifts full (op.add_odd oq) disc pos lift four
    (fun a b => small a b _ (div a b)) periodBudget basic
  simpa only [ProductDeficitBand.sumCap,defQ,le_min_iff] using And.intro lower upper

attribute [local irreducible] allSigns corner

private theorem edge64 : 21000000*(2^13*(4*2^1002)^2) < 2^2046 := by decide +kernel

private theorem edge96 : 21000000*(2^45*(4*2^986)^2) < 2^2046 := by decide +kernel

theorem exceptions_64 : 2^12*(allSigns (2^1920) ∪ corner (2^1002)).card < eligible.card :=
  combined (L:=2^1920) (M:=2^1002) (e:=12) (E:=13) rfl root64_exceptions edge64

theorem exceptions_96 : 2^44*(allSigns (2^1856) ∪ corner (2^986)).card < eligible.card :=
  combined (L:=2^1856) (M:=2^986) (e:=44) (E:=45) rfl root96_exceptions edge96

theorem four_64 {p q : ℕ} (ok : (p,q)∈eligible)
    (typical : (p,q) ∉ allSigns (2^1920) ∪ corner (2^1002)) (r : Bool → Bool → ℕ)
    (positive : ∀ a b, 0<r a b) (given : ∀ a b, (r a b)^2 ∣ neighbor a p*neighbor b q) :
    2^474≤(survivors p q r).card :=
  count (k:=64) (W:=2^980) ok typical r positive given (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem four_96 {p q : ℕ} (ok : (p,q)∈eligible)
    (typical : (p,q) ∉ allSigns (2^1856) ∪ corner (2^986)) (r : Bool → Bool → ℕ)
    (positive : ∀ a b, 0<r a b) (given : ∀ a b, (r a b)^2 ∣ neighbor a p*neighbor b q) :
    2^186≤(survivors p q r).card :=
  count (k:=96) (W:=2^948) ok typical r positive given (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

end PrimeFactors.SquareClueEndpointPopulation
