import PrimeFactors.FixedProductCluePopulation
import PrimeFactors.FactorOrbitGuessRanks

/-! Count the unordered pairs of odd residues with a prescribed product
modulo a power of two, and the minimum number of representatives needed
to meet every pair. -/
namespace PrimeFactors.DyadicFactorOrbitCount

open Finset FactorOrbitGuessRanks
open private PrimeFactors.FixedProductCluePopulation.sum_lifts from PrimeFactors.FixedProductCluePopulation
open private PrimeFactors.DyadicClueMeanPopulation.unit_odd from PrimeFactors.DyadicClueMeanPopulation
open scoped Classical

private theorem root_iff {j : ℕ} (jp : 1≤j) (u x : DyadicClueMeanPopulation.Unit j) :
    x^2=u ↔ x.val.val%2^j∈SingularDyadicClueSuffixes.menu j u.val.val := by
  have self := (SingularDyadicClueSuffixes.true_suffix (k:=j) (q:=x.val.val) jp
    (PrimeFactors.DyadicClueMeanPopulation.unit_odd x)).mpr (Nat.ModEq.refl _)
  have square := (SingularDyadicClueSuffixes.mem_menu.mp self).2
  rw [←sq] at square
  rw [SingularDyadicClueSuffixes.mem_menu,and_iff_right (Nat.mod_lt _ (by positivity))]
  have eq : x^2=u ↔ x.val.val^2 ≡ u.val.val [MOD 2^(j+1)] := by
    rw [←ZMod.natCast_eq_natCast_iff,Nat.cast_pow,ZMod.natCast_zmod_val,ZMod.natCast_zmod_val]
    rw [←Units.val_pow_eq_pow_val]
    exact ⟨congrArg Units.val, fun h => Units.ext h⟩
  rw [eq]
  exact ⟨fun hit => square.trans hit,fun hit => square.symm.trans hit⟩

/-- The involution has four fixed unit residues exactly in the square class
modulo eight. Each of the two one-bit-shorter suffixes lifts twice. -/
theorem fixed_count {k : ℕ} (hk : 4≤k) (u : (ZMod (2^k))ˣ) :
    fixed u=if u.val.val%8=1 then 4 else 0 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 1≤k)
  have jp : 3≤j := by omega
  let M := SingularDyadicClueSuffixes.menu j u.val.val
  let f (a : ℕ) := if a∈M then 1 else 0
  have sub : M ⊆ FixedProductClueTails.suffixes j := by
    intro a h
    have room := (SingularDyadicClueSuffixes.mem_menu.mp h).1
    obtain ⟨z,odd,cls,_⟩ := SingularDyadicClueSuffixes.lift jp
      (PrimeFactors.DyadicClueMeanPopulation.unit_odd u) h 1
    have par := cls.of_dvd (dvd_pow_self (2:ℤ) (by omega : j≠0))
    apply mem_filter.mpr
    refine ⟨mem_range.mpr room,?_⟩
    have : Odd (a:ℤ) := by
      obtain ⟨v,hv⟩ := odd
      change z%2=(a:ℤ)%2 at par
      exact ⟨(a:ℤ)/2,by omega⟩
    exact_mod_cast this
  have total : (∑ a∈FixedProductClueTails.suffixes j,f a)=M.card := by
    simp only [f,sum_boole,Nat.cast_id]
    exact congrArg Finset.card (filter_mem_eq_inter.trans (inter_eq_right.mpr sub))
  have roots : fixed u=∑ x : DyadicClueMeanPopulation.Unit j,f (x.val.val%2^j) := by
    simp only [f,←root_iff (by omega : 1≤j) u,sum_boole,fixed,M,Nat.cast_id]
    apply congrArg Finset.card
    ext x
    simp only [mem_filter,mem_univ,true_and]
  rw [roots,PrimeFactors.FixedProductCluePopulation.sum_lifts (by omega) f,total,
    show M.card=if u.val.val%8=1 then 2 else 0 from
      SingularDyadicClueSuffixes.card_menu jp (PrimeFactors.DyadicClueMeanPopulation.unit_odd u)]
  split <;> decide

private theorem half (L M : ℕ) (b : Prop) [Decidable b]
    (eq : 2*L=M*2+(if b then 4 else 0)) : L=M+(if b then 2 else 0) := by
  split_ifs at * <;> omega

attribute [local irreducible] Fintype.card

private theorem double_card {G : Type*} [CommGroup G] [Fintype G] (u : G) :
    2*Nat.card (Label u)=Fintype.card G+fixed u := by
  rw [Nat.card_eq_fintype_card]
  exact FactorOrbitGuessRanks.count u

/-- Each label is an unordered pair {x,u/x} of residues. -/
theorem orbit_count {k : ℕ} (hk : 4≤k) (u : (ZMod (2^k))ˣ) :
    Fintype.card (Label u)=2^(k-2)+(if u.val.val%8=1 then 2 else 0) := by
  rw [←Nat.card_eq_fintype_card]
  have h := double_card u
  rw [ZMod.card_units_eq_totient,Nat.totient_prime_pow Nat.prime_two (by omega),fixed_count hk] at h
  have twice : (2:ℕ)^(k-1)=2^(k-2)*2 := by
    conv_lhs => rw [show k-1=k-2+1 by omega,pow_succ]
  rw [twice] at h
  exact half (Nat.card (Label u)) (2^(k-2)) (u.val.val%8=1)
    (by simpa only [Nat.reduceSub,Nat.mul_one] using h)

section Cover
variable {G : Type*} [CommGroup G] [Fintype G]

/-- The list of guesses succeeds on every modular pair if each orbit
contains at least one guessed residue. -/
def Covers (u : G) (S : Finset G) := ∀ a : G, ∃ x∈S, x=a ∨ x=u/a

theorem cover_bound {u : G} {S : Finset G} (all : Covers u S) :
    Fintype.card (Label u)≤S.card := by
  have image : S.image (label u)=univ := by
    apply eq_univ_of_forall
    rintro ⟨s,a,rfl⟩
    obtain ⟨x,mem,eq⟩ := all a
    exact mem_image.mpr ⟨x,mem,(hit_iff ..).mpr eq⟩
  rw [←card_univ,←image]
  exact card_image_le

theorem attained (u : G) : ∃ S : Finset G, Covers u S ∧ S.card=Fintype.card (Label u) := by
  let rep (s : Label u) := Classical.choose s.property
  have names (s : Label u) : label u (rep s)=s := Subtype.ext (Classical.choose_spec s.property)
  refine ⟨univ.image rep,?_,?_⟩
  · intro a
    exact ⟨rep (label u a),mem_image_of_mem _ (mem_univ _),(hit_iff ..).mp (names _)⟩
  · rw [card_image_of_injective _ (Function.LeftInverse.injective names),card_univ]

private theorem cover_bound_nat {u : G} {S : Finset G} (all : Covers u S) :
    Nat.card (Label u)≤S.card := by rw [Nat.card_eq_fintype_card]; exact cover_bound all

private theorem attained_nat (u : G) :
    ∃ S : Finset G, Covers u S ∧ S.card=Nat.card (Label u) := by
  rw [Nat.card_eq_fintype_card]; exact attained u
end Cover

/-- No repetition in a list of guesses can improve its coverage. -/
theorem list_bound {k : ℕ} (hk : 4≤k) (u : (ZMod (2^k))ˣ)
    (guesses : List (ZMod (2^k))ˣ) (all : Covers u guesses.toFinset) :
    2^(k-2)+(if u.val.val%8=1 then 2 else 0)≤guesses.toFinset.card ∧
    guesses.toFinset.card≤guesses.length := by
  have h := orbit_count hk u
  rw [←Nat.card_eq_fintype_card] at h
  exact ⟨h.symm.le.trans (cover_bound_nat all),List.toFinset_card_le _⟩

/-- One representative from each orbit attains the least size. -/
theorem least_cover {k : ℕ} (hk : 4≤k) (u : (ZMod (2^k))ˣ) :
    IsLeast {r : ℕ | ∃ S : Finset (ZMod (2^k))ˣ, Covers u S ∧ S.card=r}
      (2^(k-2)+(if u.val.val%8=1 then 2 else 0)) := by
  have h : IsLeast {r : ℕ | ∃ S : Finset (ZMod (2^k))ˣ, Covers u S ∧ S.card=r}
      (Nat.card (Label u)) := by
    refine ⟨attained_nat u,?_⟩
    intro r hr
    obtain ⟨S,all,size⟩ := hr
    exact (cover_bound_nat all).trans_eq size
  have eq := orbit_count hk u
  rw [←Nat.card_eq_fintype_card] at eq
  exact eq ▸ h

end PrimeFactors.DyadicFactorOrbitCount
