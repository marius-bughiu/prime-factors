import Mathlib.Data.Int.CardIntervalMod
import PrimeFactors.IntervalWheelControls
import PrimeFactors.ProductDeficitBand

/-! Counts of candidate sums in the entire product-and-width interval.
The wheel uses the public product and the two advertised factor widths. -/
namespace PrimeFactors.PublicWheelWidthControls

open ChebyshevQuarticScale (fresh crossed)
open Finset LocalSumMenu

def start (n : ℕ) : ℕ := ceilSqrt (4*n)

def stop (n : ℕ) : ℕ := ProductDeficitBand.sumCap n (2^1023)

/-- Both endpoints are included when the interval is nonempty. -/
def width (n : ℕ) : ℕ := stop n + 1 - start n

/-- The ordinary sum scan tests every member of the product's mod-four class. -/
noncomputable def raw (n : ℕ) : ℕ :=
  ((range (width n)).filter fun i => (start n+i)%4=(n+1)%4).card

/-- Offset of the first mod-four sum from the lower endpoint. -/
def offset (n : ℕ) : ℕ := ((n+1)%4 + 4 - start n%4)%4

theorem raw_eq (n : ℕ) :
    raw n = width n/4 + if offset n < width n%4 then 1 else 0 := by
  have eq : raw n = (width n).count (fun i => i ≡ offset n [MOD 4]) := by
    rw [raw, Nat.count_eq_card_filter_range]
    congr 1
    apply filter_congr
    intro i _
    change (start n+i)%4=(n+1)%4 ↔ i%4=offset n%4
    unfold offset
    omega
  rw [eq, Nat.count_modEq_card _ (by decide)]
  simp [offset]

/-- A square test for each sum that survives the wheel throughout the interval. -/
noncomputable def tests (n m : ℕ) : ℕ :=
  Nat.card {i : Fin (width n) // AdmissibleSum (n : ZMod m) ((start n+i.val : ℕ) : ZMod m)}

/-- Each complete period contains all admissible residues once. Its final
incomplete period can contain each admissible residue at most once. -/
theorem period_bounds (n m : ℕ) (pos : 0 < m) :
    width n/m * count n m ≤ tests n m ∧ tests n m ≤ (width n/m+1) * count n m := by
  refine ⟨periodic_interval_lower_bound pos _ _ _, ?_⟩
  letI : NeZero m := ⟨pos.ne'⟩
  let R := {r : ZMod m // AdmissibleSum (n : ZMod m) r}
  let S := {i : Fin (width n) // AdmissibleSum (n : ZMod m) ((start n+i.val : ℕ) : ZMod m)}
  let encode (x : S) : Fin (width n/m+1) × R :=
    (⟨x.val.val/m, Nat.lt_succ_of_le (Nat.div_le_div_right x.val.isLt.le)⟩, ⟨_, x.property⟩)
  have inj : Function.Injective encode := by
    intro x y h
    have div : x.val.val/m = y.val.val/m := congrArg (fun u => u.1.val) h
    have res := congrArg (fun u : Fin (width n/m+1) × R => u.2.val) h
    change ((start n+x.val.val : ℕ) : ZMod m) = ((start n+y.val.val : ℕ) : ZMod m) at res
    simp only [Nat.cast_add, add_right_inj] at res
    have rem := congrArg ZMod.val res
    simp only [ZMod.val_natCast] at rem
    have eq := congrArg₂ (fun a b : ℕ => m*a+b) div rem
    simp only [Nat.div_add_mod] at eq
    exact Subtype.ext (Fin.ext eq)
  have card := Nat.card_le_card_of_injective encode inj
  simpa only [Nat.card_prod, Nat.card_eq_fintype_card (α:=Fin _), Fintype.card_fin] using card

/-- The actual sum and both endpoints use the same 1,024-bit width assumption. -/
theorem contains_sum {p q : ℕ} (po : Odd p) (qo : Odd q)
    (pl : 2^1023 ≤ p) (ql : 2^1023 ≤ q) (pu : p < 2*2^1023) (qu : q < 2*2^1023) :
    start (p*q) ≤ p+q ∧ p+q ≤ stop (p*q) := by
  have lo : 4*(p*q) ≤ (p+q)^2 := by
    zify
    nlinarith only [sq_nonneg ((p : ℤ)-q)]
  have ev : Even ((2:ℕ)^1023) := ⟨2^1022, by rw [show 1023=1022+1 by decide, pow_succ, Nat.mul_two]⟩
  have cap := (ProductDeficitBand.contains (A:=2^1023) (by positivity) ev po qo pl ql pu qu).2
  unfold ProductDeficitBand.upper at cap
  change start (p*q) ≤ p+q ∧ p+q ≤ ProductDeficitBand.sumCap (p*q) (2^1023)
  exact ⟨ceilSqrt_le_iff.mpr lo, by omega⟩

private theorem start_certificate {n r : ℕ} (low : (r-1)^2 < 4*n) (high : 4*n ≤ r^2) :
    start n = r := by
  apply le_antisymm (ceilSqrt_le_iff.mpr high)
  by_contra! small
  have h := ceilSqrt_le_iff.mp (show ceilSqrt (4*n) ≤ r-1 from by change ceilSqrt (4*n) < r at small; omega)
  omega

/-- The two bit ranges concern the actual counts. The last two inequalities
bracket their ratio in units of one hundredth. -/
def comparison (n rawExp wheelExp ratioLo ratioHi : ℕ) : Prop :=
  2^rawExp ≤ raw n ∧ raw n < 2^(rawExp+1) ∧
  2^wheelExp ≤ tests n IntervalWheelResidues.modulus ∧
  tests n IntervalWheelResidues.modulus < 2^(wheelExp+1) ∧
  ratioLo * tests n IntervalWheelResidues.modulus ≤ 100 * raw n ∧
  100 * raw n ≤ ratioHi * tests n IntervalWheelResidues.modulus

private theorem certify {n c r rawExp wheelExp ratioLo ratioHi : ℕ}
    (counted : count n IntervalWheelResidues.modulus = c) (root : start n = r)
    (arithmetic :
      let w := stop n+1-r
      let delta := ((n+1)%4+4-r%4)%4
      let baseline := w/4 + if delta < w%4 then 1 else 0
      let k := w/IntervalWheelResidues.modulus
      2^rawExp ≤ baseline ∧ baseline < 2^(rawExp+1) ∧
      2^wheelExp ≤ k*c ∧ (k+1)*c < 2^(wheelExp+1) ∧
      ratioLo*((k+1)*c) ≤ 100*baseline ∧ 100*baseline ≤ ratioHi*(k*c)) :
    comparison n rawExp wheelExp ratioLo ratioHi := by
  obtain ⟨low, high⟩ := period_bounds n IntervalWheelResidues.modulus (by decide)
  rw [counted] at low high
  dsimp only at arithmetic
  rw [←root] at arithmetic
  simp only [show stop n+1-start n = width n from rfl,
    show ((n+1)%4+4-start n%4)%4 = offset n from rfl, ←raw_eq] at arithmetic
  obtain ⟨rlo, rhi, wlo, whi, alo, ahi⟩ := arithmetic
  exact ⟨rlo, rhi, wlo.trans low, high.trans_lt whi,
    (Nat.mul_le_mul_left _ high).trans alo, ahi.trans (Nat.mul_le_mul_left _ low)⟩

theorem fresh_comparison : comparison fresh 1015 1008 12473 12474 := by
  let r : ℕ := 316654078353932669430896568039437646948995827324355950320885992018878621339882034859352160800370012849546508284505165782514386059318538454140190240579600679710842127862944181242520006361222093577810698295926626034770148286024885798179904628489506435612856553841327654419558392803832226047978898967565521689259
  exact certify (r:=r) IntervalWheelControls.fresh_count (start_certificate (by decide +kernel)
    (by decide +kernel)) (by decide +kernel)

theorem crossed_comparison : comparison crossed 1017 1011 8419 8420 := by
  let r : ℕ := 270075823370471172539650060271098650782753831933597272358639954154419986900023521886088362615536953055795637435351919646880615106044371307907625212959861347578783586375530282566149441260866241026834381879296406989063497151609370317039875224466571605726029312917602102470016115053325769991836901677876153809229
  exact certify (r:=r) IntervalWheelControls.crossed_count (start_certificate (by decide +kernel)
    (by decide +kernel)) (by decide +kernel)

end PrimeFactors.PublicWheelWidthControls
