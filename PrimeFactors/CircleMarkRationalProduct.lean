import PrimeFactors.NormBatchGCD
import PrimeFactors.FactorialBlockExclusion
import PrimeFactors.CircleMarkSmallTargetPopulation

/-! The rational grid as a rectangular polynomial evaluation, with arbitrary
column blocks. A target nonsquare at one prime ensures that a hit at the
other survives the single final gcd, including when many leaves hit. -/
namespace PrimeFactors.CircleMarkRationalProduct

open Finset Polynomial
open private PrimeFactors.NormBatchGCD.dvd_leaf_iff from PrimeFactors.NormBatchGCD

noncomputable def product (a : ℤ) (H D : ℕ) : ℕ :=
  ∏ j ∈ Icc 1 D, ∏ i ∈ Icc 1 H, NormBatchGCD.leaf a i j

theorem same_square (a : ℤ) (h : ℕ) : product a h h=NormBatchGCD.gridProduct a h := rfl

theorem local_hit {p : ℕ} [hp : Fact p.Prime] (a : ℤ) (H D : ℕ) :
    p∣product a H D ↔ ∃ j∈Icc 1 D, ∃ i∈Icc 1 H, (i:ZMod p)^2=(a:ZMod p)*(j:ZMod p)^2 := by
  simp only [product,hp.out.prime.dvd_finset_prod_iff,PrimeFactors.NormBatchGCD.dvd_leaf_iff,
    sub_eq_zero]

theorem inert {q : ℕ} [Fact q.Prime] {a : ℤ} (nq : ¬IsSquare (a:ZMod q))
    (H : ℕ) {D : ℕ} (small : D<q) : ¬q∣product a H D := by
  rintro hit
  obtain ⟨j,m,i,_,eq⟩ := (local_hit a H D).mp hit
  obtain ⟨pos,le⟩ := mem_Icc.mp m
  have nz : (j:ZMod q)≠0 := fun z => Nat.not_dvd_of_pos_of_lt pos (le.trans_lt small)
    ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp z)
  exact NormOrbit.inert_leaf _ _ _ nz nq (sub_eq_zero.mpr eq)

theorem gcd_eq {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] {a : ℤ}
    (nq : ¬IsSquare (a:ZMod q)) (H : ℕ) {D : ℕ} (small : D<q) :
    (product a H D).gcd (p*q)=if p∣product a H D then p else 1 := by
  have miss := inert nq H small
  split_ifs with hit
  · exact NormBatchGCD.one_batch hq.out hit miss
  · rw [Nat.gcd_comm]
    exact (Nat.coprime_mul_iff_left.mpr
      ⟨hp.out.coprime_iff_not_dvd.mpr hit,hq.out.coprime_iff_not_dvd.mpr miss⟩).gcd_eq_one

/-- A rectangular batch is a hit exactly when at least one of its leaves is.
This equivalence includes empty rectangles and composite moduli. -/
theorem has_hit (n : ℕ) (a : ℤ) (H D : ℕ) : ¬n.Coprime (product a H D) ↔
    ∃ i∈Icc 1 H, ∃ j∈Icc 1 D, ¬n.Coprime (NormBatchGCD.leaf a i j) := by
  classical
  constructor
  · intro hit
    by_contra! none
    exact hit (Nat.Coprime.prod_right (fun j hj => Nat.Coprime.prod_right (fun i hi => none i hi j hj)))
  · rintro ⟨i,hi,j,hj,hit⟩ cop
    apply hit
    apply cop.of_dvd_right
    have row : NormBatchGCD.leaf a i j ∣ ∏ x ∈ Icc 1 H, NormBatchGCD.leaf a x j :=
      Finset.dvd_prod_of_mem (fun x => NormBatchGCD.leaf a x j) hi
    exact row.trans (Finset.dvd_prod_of_mem (fun y => ∏ x ∈ Icc 1 H, NormBatchGCD.leaf a x y) hj)

/-- The monic numerator polynomial uses each positive numerator once. -/
noncomputable def rows (R : Type*) [CommRing R] (H : ℕ) : R[X] :=
  FactorialBlockExclusion.nodePolynomial (Icc 1 H) (fun i : ℕ => (i:R)^2)

theorem degree {R : Type*} [CommRing R] [Nontrivial R] (H : ℕ) :
    (rows R H).natDegree=H := by
  unfold rows FactorialBlockExclusion.nodePolynomial
  rw [natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C,Finset.sum_const,Nat.card_Icc,smul_eq_mul,mul_one,Nat.add_sub_cancel]

noncomputable def sample {R : Type*} [CommRing R] (a : R) (H D : ℕ) : R :=
  ∏ j ∈ Icc 1 D, (rows R H).eval (a*(j:R)^2)

theorem evaluate {R : Type*} [CommRing R] (a : R) (H D : ℕ) :
    sample a H D=∏ j ∈ Icc 1 D, ∏ i ∈ Icc 1 H, (a*(j:R)^2-(i:R)^2) := by
  simp [sample,rows,FactorialBlockExclusion.nodePolynomial,eval_prod]

private def absHom : ℤ →* ℕ where
  toFun := Int.natAbs
  map_one' := rfl
  map_mul' := Int.natAbs_mul

theorem absolute (a : ℤ) (H D : ℕ) : (sample a H D).natAbs=product a H D := by
  rw [evaluate]
  change absHom _=_
  simp only [map_prod,product]
  apply prod_congr rfl; intro j _
  apply prod_congr rfl; intro i _
  change (_-_ : ℤ).natAbs=(_-_ : ℤ).natAbs
  rw [←Int.natAbs_neg,neg_sub]

theorem modular (N : ℕ) (a : ℤ) (H D : ℕ) :
    ((sample a H D:ℤ):ZMod N)=sample (a:ZMod N) H D := by
  simp only [evaluate,Int.cast_prod,Int.cast_sub,Int.cast_mul,Int.cast_pow,Int.cast_natCast]

/-- Streaming arbitrary disjoint column blocks gives the same product. -/
theorem partition {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (a : R) (H D : ℕ) (ids : Finset ι) (block : ι→Finset ℕ)
    (cover : ids.biUnion block=Icc 1 D) (disjoint : (ids:Set ι).PairwiseDisjoint block) :
    sample a H D=∏ k ∈ ids, ∏ j ∈ block k, (rows R H).eval (a*(j:R)^2) := by
  rw [sample,←cover,prod_biUnion disjoint]

/-- Reducing by any monic node polynomial preserves its evaluations at roots.
This step requires no inverses modulo the composite. -/
theorem node_remainder {R : Type*} [CommRing R] (P Q : R[X]) (monic : Q.Monic) (v : R)
    (root : Q.eval v=0) : (P%ₘQ).eval v=P.eval v := by
  have e := congrArg (eval v) (P.modByMonic_add_div monic)
  simpa only [eval_add,eval_mul,root,zero_mul,add_zero] using e

end PrimeFactors.CircleMarkRationalProduct
