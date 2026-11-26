import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Log
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact bounds for resolving a bucket of matching integer positions. Combining
local gap gcds needs only a group anchor and a range of consecutive differences.
The budget concerns postprocessing after the join has found the occupied ranges. -/

namespace PrimeFactors.GeometricGapBudget
open Finset

/-- Gcd of unsigned distances from an integer anchor. -/
noncomputable def gap (a : ℤ) (S : Finset ℤ) : ℕ := S.gcd (fun x => (x-a).natAbs)

theorem dvd_gap {d : ℕ} {a : ℤ} {S : Finset ℤ} :
    d∣gap a S ↔ ∀ x∈S, a ≡ x [ZMOD (d:ℤ)] := by
  simp only [gap,Finset.dvd_gcd_iff,Int.modEq_iff_dvd,Int.natCast_dvd]

/-- Any anchor belonging to the bucket gives the same gcd of pairwise differences. -/
theorem all_pairs {d : ℕ} {a : ℤ} {S : Finset ℤ} (anchor : a∈S) :
    d∣gap a S ↔ ∀ x∈S, ∀ y∈S, (d:ℤ)∣y-x := by
  rw [dvd_gap]
  exact ⟨fun h x hx y hy => ((h x hx).symm.trans (h y hy)).dvd,
    fun h x hx => Int.modEq_iff_dvd.mpr (h a anchor x hx)⟩

/-- Annihilating gap for an arbitrary mask of coincident powers, including
signed exponents. A second distinct position makes the gcd positive. -/
theorem order_dvd_gap {G : Type*} [Group G] (g : G) (a : ℤ) (S : Finset ℤ)
    (hits : ∀ x∈S, g^x=g^a) : orderOf g ∣ gap a S := by
  apply dvd_gap.mpr
  intro x hx
  exact Int.modEq_iff_dvd.mpr (orderOf_dvd_sub_iff_zpow_eq_zpow.mpr (hits x hx))

/-- Compute with consecutive differences instead of all anchor-relative
differences. The first difference is taken relative to the supplied anchor. -/
def adjacent (a : ℤ) : List ℤ → ℕ
  | [] => 0
  | x::xs => Nat.gcd (x-a).natAbs (adjacent x xs)

theorem dvd_adjacent (d : ℕ) (a : ℤ) (xs : List ℤ) :
    d ∣ adjacent a xs ↔ ∀ x∈xs, a ≡ x [ZMOD (d:ℤ)] := by
  induction xs generalizing a with
  | nil => simp [adjacent]
  | cons x xs ih =>
    simp only [adjacent,Nat.dvd_gcd_iff,ih,←Int.natCast_dvd,←Int.modEq_iff_dvd,List.forall_mem_cons]
    exact ⟨fun ⟨ax,r⟩ => ⟨ax,fun y hy => ax.trans (r y hy)⟩,
      fun ⟨ax,r⟩ => ⟨ax,fun y hy => ax.symm.trans (r y hy)⟩⟩

theorem adjacent_eq_gap (a : ℤ) (xs : List ℤ) : adjacent a xs=gap a xs.toFinset := by
  apply Nat.dvd_antisymm
  · exact dvd_gap.mpr fun x hx => (dvd_adjacent _ _ _).mp dvd_rfl x (List.mem_toFinset.mp hx)
  · exact (dvd_adjacent _ _ _).mpr fun x hx => dvd_gap.mp dvd_rfl x (List.mem_toFinset.mpr hx)

/-- Each group contributes an anchor difference and its own internal gcd. The
groups may overlap. Every group included in the fold must contain its anchor. -/
theorem grouped {ι : Type*} [DecidableEq ι] (groups : Finset ι) (members : ι → Finset ℤ)
    (a : ℤ) (first : ι → ℤ) (inside : ∀ i∈groups, first i∈members i) :
    gap a (groups.biUnion members) =
      groups.gcd (fun i => Nat.gcd (first i-a).natAbs (gap (first i) (members i))) := by
  have both (d : ℕ) : d∣gap a (groups.biUnion members) ↔
      d∣groups.gcd (fun i => Nat.gcd (first i-a).natAbs (gap (first i) (members i))) := by
    rw [dvd_gap,Finset.dvd_gcd_iff]
    simp only [Nat.dvd_gcd_iff,dvd_gap,←Int.natCast_dvd,←Int.modEq_iff_dvd]
    constructor
    · intro all i hi
      have ax := all (first i) (mem_biUnion.mpr ⟨i,hi,inside i hi⟩)
      exact ⟨ax,fun x hx => ax.symm.trans (all x (mem_biUnion.mpr ⟨i,hi,hx⟩))⟩
    · intro all x hx
      obtain ⟨i,hi,mem⟩ := mem_biUnion.mp hx
      exact (all i hi).1.trans ((all i hi).2 x mem)
  exact Nat.dvd_antisymm ((both _).mp dvd_rfl) ((both _).mpr dvd_rfl)

/-- Range-gcd tables can be shared by every translate of a bucket. -/
theorem translate (a offset : ℤ) (S : Finset ℤ) :
    gap (offset+a) (S.image (offset+·)) = gap a S := by
  have both (d : ℕ) : d ∣ gap (offset+a) (S.image (offset+·)) ↔ d ∣ gap a S := by
    simp only [dvd_gap,Int.modEq_iff_dvd,Finset.forall_mem_image,add_sub_add_left_eq_sub]
  exact Nat.dvd_antisymm ((both _).mp dvd_rfl) ((both _).mpr dvd_rfl)

/-- Formula for the actual range summaries. Each nonempty slice consists of
a first baby value and a tail, all translated by the same giant offset. Only
the adjacent edges in that slice enter its internal range-gcd query. -/
theorem grouped_adjacent {ι : Type*} [DecidableEq ι] (groups : Finset ι) (a : ℤ)
    (offset first : ι → ℤ) (tail : ι → List ℤ) :
    let slice := fun i => ((first i :: tail i).toFinset).image (offset i + ·)
    gap a (groups.biUnion slice) =
      groups.gcd (fun i => Nat.gcd (offset i+first i-a).natAbs (adjacent (first i) (tail i))) := by
  intro slice
  rw [grouped groups slice a (fun i => offset i+first i) (by
    intro i _
    exact mem_image.mpr ⟨first i,by simp,rfl⟩)]
  apply Finset.gcd_congr rfl
  intro i _
  dsimp only [slice]
  rw [translate,←adjacent_eq_gap]
  simp [adjacent]

theorem gap_pos {S : Finset ℤ} (a : ℤ) (many : 1<S.card) : 0<gap a S := by
  by_contra! zero
  obtain ⟨x,hx,y,hy,ne⟩ := Finset.one_lt_card.mp many
  have all := dvd_gap.mp (show 0 ∣ gap a S by rw [Nat.eq_zero_of_le_zero zero])
  have ax := (all x hx).dvd
  have ay := (all y hy).dvd
  simp only [Nat.cast_zero,zero_dvd_iff,sub_eq_zero] at ax ay
  exact ne (ax.trans ay.symm)

/-- Distinct signed positions in an inclusive interval of width W that are
all congruent modulo h occupy at most floor(W/h)+1 slots. -/
theorem card_slots {S : Finset ℤ} {a L : ℤ} {h W : ℕ}
    (inside : ∀ x∈S, L≤x ∧ x≤L+W) (common : h∣gap a S) : S.card≤W/h+1 := by
  let index := fun x : ℤ => (x-L).toNat
  have base (x : ℤ) (mem : x∈S) : ((index x:ℕ):ℤ)=x-L :=
    Int.toNat_of_nonneg (sub_nonneg.mpr (inside x mem).1)
  have cap (x : ℤ) (mem : x∈S) : index x≤W := by
    change (x-L).toNat≤W
    rw [Int.toNat_le]
    linarith [(inside x mem).2]
  suffices S.card ≤ (range (W/h+1)).card by simpa using this
  apply card_le_card_of_injOn (fun x => index x/h)
  · intro x hx
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (cap x hx)))
  · intro x hx y hy equal
    have cr := (dvd_gap.mp common x hx).symm.trans (dvd_gap.mp common y hy)
    have shifted : (index x:ℕ) ≡ index y [MOD h] := by
      rw [Nat.modEq_iff_dvd,base x hx,base y hy]
      simpa only [sub_sub_sub_cancel_right] using cr.dvd
    have rem : index x%h=index y%h := shifted
    change index x/h=index y/h at equal
    have all := Nat.mod_add_div (index x) h
    rw [rem,equal,Nat.mod_add_div] at all
    have eq := congrArg (fun v : ℕ => (v:ℤ)) all
    change ((index y:ℕ):ℤ) = ((index x:ℕ):ℤ) at eq
    rw [base x hx,base y hy] at eq
    omega

/-- The number of distinct hits controls the actual common annihilator. -/
theorem packing {S : Finset ℤ} (a L : ℤ) (W : ℕ) (inside : ∀ x∈S, L≤x ∧ x≤L+W) :
    (S.card-1)*gap a S ≤ W := by
  have n := card_slots inside (dvd_refl (gap a S))
  exact (Nat.mul_le_mul_right _ (Nat.sub_le_iff_le_add.mpr n)).trans (Nat.div_mul_le_self ..)

/-- With at most K hits one may check all their sums. Above that threshold the
positive annihilator has square root at most K whenever W≤K³. -/
theorem cube_budget {S : Finset ℤ} (a L : ℤ) {W K : ℕ} (kp : 0<K) (wide : W≤K^3)
    (inside : ∀ x∈S, L≤x ∧ x≤L+W) :
    S.card≤K ∨ (0<gap a S ∧ gap a S≤K^2 ∧ (gap a S).sqrt≤K) := by
  by_cases few : S.card≤K
  · exact Or.inl few
  have pos := gap_pos a (show 1<S.card by omega)
  have bound := (Nat.mul_le_mul_right (gap a S) (show K≤S.card-1 by omega)).trans (packing a L W inside)
  have small : gap a S≤K^2 := Nat.le_of_mul_le_mul_left
    ((bound.trans wide).trans_eq (by ring : K^3=K*K^2)) kp
  exact Or.inr ⟨pos,small,by nlinarith [Nat.sqrt_le' (gap a S)]⟩

/-- Once all candidate divisors up to K have been stripped, the residual is
prime or 1. This holds throughout any trial division of h≤K². -/
theorem remaining_prime {h m K : ℕ} (hp : 0<h) (small : h≤K^2) (divides : m∣h)
    (tested : ∀ p, p.Prime → p≤K → ¬p∣m) : m=1 ∨ m.Prime := by
  by_cases one : m=1
  · exact Or.inl one
  right
  by_contra composite
  have pos := Nat.pos_of_dvd_of_pos divides hp
  have sq := (Nat.minFac_sq_le_self pos composite).trans ((Nat.le_of_dvd hp divides).trans small)
  have lim : m.minFac≤K := by nlinarith
  exact tested m.minFac (Nat.minFac_prime one) lim (Nat.minFac_dvd m)

/-- A basic loop tests 2 and then 3,5,... while the trial divisor squared
does not exceed the residual. This counts the distinct candidate tests. -/
theorem odd_trials (K i : ℕ) : 3+2*i≤K ↔ i<(K-1)/2 := by omega

/-- The total successful divisions, including repetitions, cost at most
floor(log₂ h). Each removed integer factor is at least two. -/
theorem successful_divisions {h : ℕ} (positive : 0<h) (removed : List ℕ)
    (factors : ∀ x∈removed, 2≤x) (divides : removed.prod∣h) :
    removed.length ≤ Nat.log2 h :=
  (Nat.le_log2 positive.ne').mpr
    ((List.pow_card_le_prod removed 2 factors).trans (Nat.le_of_dvd positive divides))

/-- For example, eleven signed hits in width 1000 attain both inequalities
with K=10. The anchor lies in the interior of the signed interval. -/
theorem example_tight :
    let xs : List ℤ := [-200,-100,0,100,200,300,400,500,600,700,800]
    xs.toFinset.card=11 ∧ gap 0 xs.toFinset=100 ∧ adjacent 0 xs=100 ∧
      (xs.toFinset.card-1)*gap 0 xs.toFinset=1000 ∧ (gap 0 xs.toFinset).sqrt=10 := by
  decide +kernel

/-- Two translated slices have internal gcds 24 and 36, but their first
positions differ by 42. The gcd used for order stripping is exactly 6. -/
theorem example_grouped :
    let left : List ℤ := [10,34,58]
    let baby : List ℤ := [2,38,74]
    let right := baby.toFinset.image ((50:ℤ)+·)
    adjacent 10 left=24 ∧ adjacent 2 baby=36 ∧
    gap 10 (left.toFinset∪right)=Nat.gcd 24 (Nat.gcd 42 36) ∧
    gap 10 (left.toFinset∪right)=6 := by decide +kernel

end PrimeFactors.GeometricGapBudget
