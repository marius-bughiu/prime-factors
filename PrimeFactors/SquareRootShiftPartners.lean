import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import PrimeFactors.MixedPrefixSample

/-! Count odd partners of a fixed prime for a polynomial tested at the public
integer square root of their product. Both factors lie in the same interval [B,2B). -/
namespace PrimeFactors.SquareRootShiftPartners

open Finset Polynomial

private theorem root_range {B p q : ℕ} (bp : B ≤ p) (pt : p < 2*B)
    (bq : B ≤ q) (qt : q < 2*B) :
    B ≤ (p*q).sqrt ∧ (p*q).sqrt < 2*B :=
  ⟨Nat.le_sqrt.mpr (Nat.mul_le_mul bp bq), Nat.sqrt_lt.mpr (Nat.mul_lt_mul_of_lt_of_lt pt qt)⟩

private theorem same_residue {B p x y : ℕ} (bp : B ≤ p)
    (bx : B ≤ x) (xt : x < 2*B) (by' : B ≤ y) (yt : y < 2*B)
    (h : (x : ZMod p) = y) : x = y := by
  have eq : ((x-B : ℕ) : ZMod p) = ((y-B : ℕ) : ZMod p) := by
    rw [Nat.cast_sub bx, Nat.cast_sub by', h]
  have rem := (ZMod.natCast_eq_natCast_iff' _ _ _).mp eq
  rw [Nat.mod_eq_of_lt (show x-B < p by omega), Nat.mod_eq_of_lt (show y-B < p by omega)] at rem
  omega

private theorem distance {B p a b : ℕ} (bp : B ≤ p) (cap : (p*a).sqrt < 2*B)
    (same : (p*a).sqrt = (p*b).sqrt) : b < a+4 := by
  have lo := Nat.sqrt_le' (p*a)
  have hi := Nat.lt_succ_sqrt' (p*b)
  rw [← same] at hi
  by_contra! far
  have sep := Nat.mul_le_mul_left p far
  nlinarith

/-- For each allowable residue of the integer square root, at most two odd
partners can give that residue, including partners larger or smaller than p. -/
theorem count {B p : ℕ} (bp : B ≤ p) (pt : p < 2*B) (S : Finset ℕ)
    (R : Finset (ZMod p)) (bounds : ∀ q ∈ S, B ≤ q ∧ q < 2*B ∧ q%2=1)
    (hit : ∀ q ∈ S, ((p*q).sqrt : ZMod p) ∈ R) : S.card ≤ 2*R.card := by
  let key (q : ℕ) : ZMod p × Fin 2 := (↑(p*q).sqrt, ⟨q/2%2, Nat.mod_lt _ (by decide)⟩)
  have inj : (S : Set ℕ).InjOn key := by
    intro a ha b hb equal
    obtain ⟨ba,atop,oa⟩ := bounds a ha
    obtain ⟨bb,btop,ob⟩ := bounds b hb
    obtain ⟨la,ua⟩ := root_range bp pt ba atop
    obtain ⟨lb,ub⟩ := root_range bp pt bb btop
    have eq := same_residue bp la ua lb ub (congrArg Prod.fst equal)
    have da := distance bp ua eq
    have db := distance bp ub eq.symm
    have tag : a/2%2=b/2%2 := congrArg (fun x : ZMod p × Fin 2 => x.2.val) equal
    omega
  have h := card_le_card_of_injOn (t:=R ×ˢ (univ : Finset (Fin 2))) key
    (fun q hq => mem_product.mpr ⟨hit q hq, mem_univ _⟩) inj
  simpa [Nat.mul_comm] using h

/-- A degree-d polynomial nonzero modulo p tested at floor(sqrt(pq))+c
can vanish for at most 2d odd partners q of the same bit length as p. -/
theorem polynomial {B p : ℕ} [Fact p.Prime] (bp : B ≤ p) (pt : p < 2*B)
    (S : Finset ℕ) (F : (ZMod p)[X]) (nz : F ≠ 0) (c : ZMod p)
    (bounds : ∀ q ∈ S, B ≤ q ∧ q < 2*B ∧ q%2=1)
    (hit : ∀ q ∈ S, F.eval (((p*q).sqrt : ZMod p)+c)=0) :
    S.card ≤ 2*F.natDegree := by
  classical
  let R := F.roots.toFinset.image (fun z => z-c)
  have lift (q : ℕ) (hq : q∈S) : ((p*q).sqrt : ZMod p) ∈ R := by
    exact mem_image.mpr ⟨_, Multiset.mem_toFinset.mpr ((mem_roots nz).mpr (hit q hq)), add_sub_cancel_right _ _⟩
  exact (count bp pt S R bounds lift).trans (Nat.mul_le_mul_left 2
    ((card_image_le).trans ((Multiset.toFinset_card_le _).trans F.card_roots')))

open MixedPrefixSample

/-- All pairs that a test with allowable square-root residues R can flag,
stored in ascending order regardless of which prime the test detects. -/
noncomputable def detected (R : (p : ℕ) → Finset (ZMod p)) : Finset (ℕ × ℕ) := by
  classical
  exact primes.biUnion fun p =>
    (((Ico X (2*X)).filter fun q => q%2=1 ∧ ((p*q).sqrt : ZMod p) ∈ R p).image
      fun q => (min p q, max p q))

attribute [local irreducible] MixedPrefixSample.X eligible

/-- A cap of 202 local square-root residues per prime gives fewer than one
successful pair in 2^990 across the ordinary full-width prime-pair sample.
The superset counted here allows even composite partners on the odd side. -/
theorem population (R : (p : ℕ) → Finset (ZMod p)) (cap : ∀ p∈primes, (R p).card≤202)
    (analytic : PrimeCountInput) :
    2^990 * (detected R ∩ eligible).card < eligible.card := by
  classical
  have primeRange : primes ⊆ Ico X (2*X) := by
    intro p hp
    exact (mem_filter.mp hp).1
  have pc : primes.card≤X := (card_le_card primeRange).trans (by simp; omega)
  let partners (p : ℕ) := (Ico X (2*X)).filter fun q => q%2=1 ∧ ((p*q).sqrt : ZMod p) ∈ R p
  let pairs (p : ℕ) := (partners p).image fun q => (min p q, max p q)
  have bound (p : ℕ) (hp : p∈primes) : (pairs p).card ≤ 404 := by
    obtain ⟨bp,pt⟩ := mem_Ico.mp (primeRange hp)
    have k := count bp pt (partners p) (R p) (fun q hq => by
      obtain ⟨link,odd,_⟩ := mem_filter.mp hq
      exact ⟨(mem_Ico.mp link).1,(mem_Ico.mp link).2,odd⟩)
      (fun _ hq => (mem_filter.mp hq).2.2)
    exact card_image_le.trans (k.trans (Nat.mul_le_mul_left 2 (cap p hp)))
  have limit : (detected R ∩ eligible).card ≤ X*404 :=
    (card_le_card inter_subset_left).trans ((card_biUnion_le_card_mul primes pairs 404 bound).trans
      (Nat.mul_le_mul_right 404 pc))
  have denom := denominator analytic
  have arithmetic : 21000000*(2^990*(X*404)) < 2^2046 := by
    unfold MixedPrefixSample.X
    decide +kernel
  have all := (Nat.mul_le_mul_left 21000000 (Nat.mul_le_mul_left (2^990) limit)).trans_lt
    (arithmetic.trans denom)
  exact Nat.lt_of_mul_lt_mul_left all

end PrimeFactors.SquareRootShiftPartners
