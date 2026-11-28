import PrimeFactors.ResidueCount
import Mathlib.Data.Nat.ChineseRemainder

/-! Counting ordinary residue representatives of a square-root equation over
a product of distinct odd primes. A unit target either has no roots or has
two independent choices at each prime. -/
namespace PrimeFactors.RotationSquareRootCount

open Finset

noncomputable def residues (m A : ℕ) : Finset ℕ := (range m).filter fun z => z^2 ≡ A [MOD m]

theorem mem_residues {m A z : ℕ} : z∈residues m A ↔ z<m ∧ z^2 ≡ A [MOD m] := by
  simp only [residues,mem_filter,mem_range]

theorem product_count {m n : ℕ} (cop : m.Coprime n) (mp : 0<m) (np : 0<n) (A : ℕ) :
    (residues (m*n) A).card=(residues m A).card*(residues n A).card := by
  rw [←card_product]
  apply card_bij (fun z _ => (z%m,z%n))
  · intro z hz
    obtain ⟨_,eq⟩ := mem_residues.mp hz
    obtain ⟨left,right⟩ := (Nat.modEq_and_modEq_iff_modEq_mul cop).mpr eq
    exact mem_product.mpr ⟨mem_residues.mpr ⟨Nat.mod_lt _ mp,((Nat.mod_modEq ..).pow 2).trans left⟩,
      mem_residues.mpr ⟨Nat.mod_lt _ np,((Nat.mod_modEq ..).pow 2).trans right⟩⟩
  · intro x hx y hy eq
    obtain ⟨a,b⟩ := Prod.mk.inj eq
    have both := (Nat.modEq_and_modEq_iff_modEq_mul cop).mp ⟨a,b⟩
    simpa only [Nat.ModEq,Nat.mod_eq_of_lt (mem_residues.mp hx).1,
      Nat.mod_eq_of_lt (mem_residues.mp hy).1] using both
  · intro z hz
    obtain ⟨left,right⟩ := mem_product.mp hz
    let x := Nat.chineseRemainder cop z.1 z.2
    have xl := mem_residues.mp left
    have xr := mem_residues.mp right
    refine ⟨x.val,mem_residues.mpr ⟨Nat.chineseRemainder_lt_mul cop _ _ mp.ne' np.ne',?_⟩,?_⟩
    · exact (Nat.modEq_and_modEq_iff_modEq_mul cop).mp
        ⟨(x.prop.1.pow 2).trans xl.2,(x.prop.2.pow 2).trans xr.2⟩
    · exact Prod.ext (Eq.trans x.prop.1 (Nat.mod_eq_of_lt xl.1))
        (Eq.trans x.prop.2 (Nat.mod_eq_of_lt xr.1))

/-- An odd prime has exactly two roots for a represented nonzero target. -/
theorem prime_count {p A y : ℕ} (prime : p.Prime) (odd : p≠2) (unit : A.Coprime p)
    (eqn : y^2 ≡ A [MOD p]) : (residues p A).card=2 := by
  letI : Fact p.Prime := ⟨prime⟩
  have nonzero : (A : ZMod p)≠0 := ((ZMod.isUnit_iff_coprime ..).mpr unit).ne_zero
  have sq : IsSquare (A : ZMod p) := by
    refine ⟨(y : ZMod p),?_⟩
    have e : ((y^2 : ℕ) : ZMod p)=(A : ZMod p) := (ZMod.natCast_eq_natCast_iff ..).mpr eqn
    simpa only [Nat.cast_pow,pow_two,Nat.cast_mul] using e.symm
  rw [←card_squareRootsMod_of_square p odd _ nonzero sq]
  apply card_bij (s:=residues p A) (t:=squareRootsMod p (A : ZMod p))
    (fun (x : ℕ) _ => (x : ZMod p))
  · intro x hx
    have e := (ZMod.natCast_eq_natCast_iff ..).mpr (mem_residues.mp hx).2
    rw [Nat.cast_pow] at e
    exact mem_filter.mpr ⟨mem_erase.mpr ⟨fun h => nonzero (by simpa only [h,zero_pow (by decide : 2≠0)] using e.symm),mem_univ _⟩,e⟩
  · intro x hx z hz h
    have e := (ZMod.natCast_eq_natCast_iff ..).mp h
    simpa only [Nat.ModEq,Nat.mod_eq_of_lt (mem_residues.mp hx).1,
      Nat.mod_eq_of_lt (mem_residues.mp hz).1] using e
  · intro z hz
    have e := (mem_filter.mp hz).2
    refine ⟨z.val,mem_residues.mpr ⟨ZMod.val_lt _,?_⟩,ZMod.natCast_zmod_val ..⟩
    apply (ZMod.natCast_eq_natCast_iff ..).mp
    simpa only [Nat.cast_pow,ZMod.natCast_zmod_val] using e

theorem list_count {L : List ℕ} (primes : ∀ p∈L,p.Prime ∧ p≠2)
    (co : L.Pairwise Nat.Coprime) {A y : ℕ} (unit : A.Coprime L.prod)
    (eqn : y^2 ≡ A [MOD L.prod]) : (residues L.prod A).card=2^L.length := by
  induction L with
  | nil => simp [residues,Nat.ModEq,Nat.mod_one]
  | cons p L ih =>
    have pp := primes p (by simp)
    have tail (q : ℕ) (hq : q∈L) := primes q (List.mem_cons_of_mem _ hq)
    have cop := Nat.coprime_list_prod_right_iff.mpr (List.pairwise_cons.mp co).1
    have pos : 0<L.prod := Nat.pos_of_ne_zero (List.prod_ne_zero (fun h => (tail 0 h).1.ne_zero rfl))
    change A.Coprime (p*L.prod) at unit
    change y^2 ≡ A [MOD p*L.prod] at eqn
    obtain ⟨up,ul⟩ := Nat.coprime_mul_iff_right.mp unit
    obtain ⟨ep,el⟩ := (Nat.modEq_and_modEq_iff_modEq_mul cop).mpr eqn
    rw [List.prod_cons,List.length_cons,pow_succ,product_count cop pp.1.pos pos,
      prime_count pp.1 pp.2 up ep,ih tail co.of_cons ul el,Nat.mul_comm]

end PrimeFactors.RotationSquareRootCount
