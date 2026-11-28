import PrimeFactors.PrimeSumRatioRoots
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

/-! A polynomial relation of one common scaling weight on the product and
sum becomes a single ordinary polynomial in the ratio S²/N. -/

namespace PrimeFactors.PrimeSumHomogeneousGrid

open Finset MvPolynomial

abbrev Poly := MvPolynomial (Fin 2) ℚ
private abbrev Exponent := Fin 2 →₀ ℕ

/-- Scaling both factors by c scales the product by c² and their sum by c. -/
abbrev Weight (F : Poly) (w : ℕ) := F.IsWeightedHomogeneous ![(2:ℕ),1] w

theorem weight_iff {F : Poly} {w : ℕ} :
    Weight F w ↔ ∀ m∈F.support, 2*m 0+m 1=w := by
  have weights (m : Exponent) : Finsupp.weight ![(2:ℕ),1] m = 2*m 0+m 1 := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype m (fun i c => c • ![(2:ℕ),1] i)
      (fun i => zero_smul ℕ _),Fin.sum_univ_two]
    simp [smul_eq_mul,mul_comm]
  simp only [Weight, IsWeightedHomogeneous, mem_support_iff,weights]

/-- Each term N^i S^j contributes its coefficient to T^⌊j/2⌋. Common
weight ensures that distinct supported monomials have distinct exponents here. -/
noncomputable def shape (F : Poly) : Polynomial ℚ :=
  ∑ m∈F.support, Polynomial.monomial (m 1 / 2) (coeff m F)

theorem shape_coeff {F : Poly} {w : ℕ} (h : Weight F w) {m : Exponent}
    (hm : m∈F.support) : (shape F).coeff (m 1/2)=coeff m F := by
  classical
  rw [shape,Polynomial.finset_sum_coeff,sum_eq_single_of_mem m hm]
  · simp
  · intro k hk ne
    have wm := weight_iff.mp h m hm
    have wk := weight_iff.mp h k hk
    have different : k 1 / 2 ≠ m 1 / 2 := by
      intro equal
      apply ne
      ext i
      fin_cases i
      · change k 0=m 0; omega
      · change k 1=m 1; omega
    simp [Polynomial.coeff_monomial,different,Ne.symm different]

theorem shape_ne_zero {F : Poly} {w : ℕ} (h : Weight F w) (nz : F≠0) : shape F≠0 := by
  obtain ⟨m,hm⟩ := Finsupp.support_nonempty_iff.mpr nz
  intro zero
  have c := shape_coeff h hm
  rw [zero,Polynomial.coeff_zero] at c
  exact (mem_support_iff.mp hm) c.symm

private theorem exponent_sum {F : Poly} {m : Exponent} (hm : m∈F.support) :
    m 0+m 1≤F.totalDegree := by
  have cap := le_sup (f:=fun u : Exponent => u.sum fun _ e => e) hm
  change _ ≤ F.support.sup _
  have expand := Finsupp.sum_fintype m (fun (_ : Fin 2) (e : ℕ) => e) (fun _ => rfl)
  rw [Fin.sum_univ_two] at expand
  simpa only [expand] using cap

/-- The number of ratio roots is bounded by half the original total degree. -/
theorem shape_degree (F : Poly) : (shape F).natDegree≤F.totalDegree/2 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  have lim := exponent_sum hm
  exact (Polynomial.natDegree_monomial_le ..).trans (by omega)

/-- Factoring the integer exponents extracts the same common multiplier
from every monomial of the prescribed weight. -/
private theorem term (i j w : ℕ) (weight : 2*i+j=w) (n s : ℚ) (nn : n≠0) :
    n^i*s^j = n^(w/2)*s^(w%2)*(s^2/n)^(j/2) := by
  have k : w/2=i+j/2 := by omega
  have b : w%2=j%2 := by omega
  calc
    _ = n^i * (s^(j%2)*(s^2)^(j/2)) := by rw [←pow_mul,←pow_add]; congr 2; omega
    _ = _ := by rw [k,b,pow_add,div_pow]; field_simp; ring

/-- Exact normalization, including when the sum is zero. -/
theorem evaluation {F : Poly} {w : ℕ} (h : Weight F w) (n s : ℚ) (nn : n≠0) :
    eval ![n,s] F = n^(w/2)*s^(w%2)*(shape F).eval (s^2/n) := by
  classical
  conv_lhs => rw [F.as_sum]
  simp only [map_sum,eval_monomial,Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,
    shape,Polynomial.eval_finset_sum,Polynomial.eval_monomial,mul_sum]
  apply sum_congr rfl
  intro m hm
  rw [term _ _ _ (weight_iff.mp h m hm) n s nn]
  ring

theorem eval_eq_zero_iff {F : Poly} {w : ℕ} (h : Weight F w) (n s : ℚ)
    (nn : n≠0) (sn : s≠0) : eval ![n,s] F=0 ↔ (shape F).eval (s^2/n)=0 := by
  rw [evaluation h n s nn]
  simp [nn,sn]

/-- Every sorted pair of distinct prime factors at any size satisfying F=0. -/
def primeHits (F : Poly) : Set (ℕ×ℕ) :=
  {z | z.1.Prime ∧ z.2.Prime ∧ z.1<z.2 ∧
    eval ![((z.1*z.2:ℕ):ℚ),((z.1+z.2:ℕ):ℚ)] F=0}

/-- A global finite set, without an upper cutoff on the primes. Distinct
sorted prime pairs have distinct reduced ratios S²/N. -/
theorem prime_hits_bound {F : Poly} {w : ℕ} (h : Weight F w) (nz : F≠0) :
    (primeHits F).Finite ∧ (primeHits F).ncard≤F.totalDegree/2 := by
  classical
  let H := shape F
  have in_roots (z : primeHits F) : PrimeSumRatioRoots.ratio z.val.1 z.val.2∈H.roots := by
    obtain ⟨pp,qp,_,hit⟩ := z.property
    have nn : 0<z.val.1*z.val.2 := Nat.mul_pos pp.pos qp.pos
    have sn : 0<z.val.1+z.val.2 := Nat.add_pos_left pp.pos _
    have root := (eval_eq_zero_iff h ((z.val.1*z.val.2:ℕ):ℚ) ((z.val.1+z.val.2:ℕ):ℚ)
      (by exact_mod_cast nn.ne') (by exact_mod_cast sn.ne')).mp hit
    apply (Polynomial.mem_roots (shape_ne_zero h nz)).mpr
    simpa only [PrimeSumRatioRoots.ratio,Nat.cast_pow,Polynomial.IsRoot] using root
  let f (z : primeHits F) : ↥H.roots.toFinset :=
    ⟨PrimeSumRatioRoots.ratio z.val.1 z.val.2,Multiset.mem_toFinset.mpr (in_roots z)⟩
  have inj : Function.Injective f := by
    intro x y eq
    obtain ⟨xp,xq,xlt,_⟩ := x.property
    obtain ⟨yp,yq,ylt,_⟩ := y.property
    have ratio : PrimeSumRatioRoots.ratio x.val.1 x.val.2 =
        PrimeSumRatioRoots.ratio y.val.1 y.val.2 := congrArg Subtype.val eq
    obtain ⟨a,b⟩ := (PrimeSumRatioRoots.eq_iff xp xq yp yq xlt ylt).mp ratio
    exact Subtype.ext (Prod.ext a b)
  have bound := Nat.card_le_card_of_injective f inj
  rw [Nat.card_eq_finsetCard] at bound
  exact ⟨Finite.of_injective f inj,
    bound.trans ((Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' H).trans (shape_degree F)))⟩

/-- The quadratic through a supplied factor pair is S²−(S₀²/N₀)N. -/
noncomputable def ratioFactor (z : ℕ×ℕ) : Poly :=
  X 1^2+C (-(PrimeSumRatioRoots.ratio z.1 z.2))*X 0

/-- Construct a single relation through a prescribed finite set of pairs. -/
noncomputable def prescribed (E : Finset (ℕ×ℕ)) : Poly := ∏ z∈E, ratioFactor z

theorem prescribed_weight (E : Finset (ℕ×ℕ)) : Weight (prescribed E) (2*E.card) := by
  let W : Fin 2 → ℕ := ![2,1]
  have one (z : ℕ×ℕ) : Weight (ratioFactor z) 2 := by
    have hx : Weight (X 1) 1 := isWeightedHomogeneous_X ℚ W 1
    have hn : Weight (X 0) 2 := isWeightedHomogeneous_X ℚ W 0
    exact (hx.pow 2).add ((isWeightedHomogeneous_C W _).mul hn)
  have all := IsWeightedHomogeneous.prod E ratioFactor (fun _ => 2) (fun z _ => one z)
  simpa only [prescribed,sum_const,nsmul_eq_mul,Nat.mul_comm] using all

theorem prescribed_ne_zero (E : Finset (ℕ×ℕ)) : prescribed E≠0 := by
  intro eq
  have h := congrArg (eval ![(0:ℚ),1]) eq
  simp [prescribed,ratioFactor] at h

private theorem eval_ratioFactor (u v : ℕ×ℕ) (pos : 0<u.1*u.2) :
    eval ![((u.1*u.2:ℕ):ℚ),((u.1+u.2:ℕ):ℚ)] (ratioFactor v)=0 ↔
      PrimeSumRatioRoots.ratio u.1 u.2=PrimeSumRatioRoots.ratio v.1 v.2 := by
  have nn : ((u.1*u.2:ℕ):ℚ)≠0 := by exact_mod_cast pos.ne'
  change _ ↔ ((((u.1+u.2)^2:ℕ):ℚ) / ((u.1*u.2:ℕ):ℚ))=_
  rw [div_eq_iff nn,Nat.cast_pow]
  simp only [ratioFactor,map_add,map_pow,eval_X,map_mul,eval_C,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.head_cons,neg_mul]
  exact ⟨fun e => by linarith only [e], fun e => by linarith only [e]⟩

/-- For each finite set of sorted distinct prime pairs the construction has
precisely those hits. No additional prime pair at any width is included. -/
theorem prescribed_hits (E : Finset (ℕ×ℕ))
    (valid : ∀ z∈E, z.1.Prime ∧ z.2.Prime ∧ z.1<z.2) :
    primeHits (prescribed E)=(↑E : Set (ℕ×ℕ)) := by
  ext z
  change (_ ∧ _ ∧ _ ∧ eval _ (prescribed E)=0) ↔ z∈E
  simp only [prescribed,map_prod,prod_eq_zero_iff]
  constructor
  · rintro ⟨p,q,lt,v,hv,eq⟩
    obtain ⟨vp,vq,vlt⟩ := valid v hv
    have ratio := (eval_ratioFactor z v (Nat.mul_pos p.pos q.pos)).mp eq
    obtain ⟨a,b⟩ := (PrimeSumRatioRoots.eq_iff p q vp vq lt vlt).mp ratio
    rwa [Prod.ext a b]
  · intro mem
    obtain ⟨p,q,lt⟩ := valid z mem
    exact ⟨p,q,lt,z,mem,(eval_ratioFactor z z (Nat.mul_pos p.pos q.pos)).mpr rfl⟩

/-- The constructed relation has degree exactly twice the number of requested
pairs, so the global degree bound is attained for every finite example. -/
theorem prescribed_degree (E : Finset (ℕ×ℕ))
    (valid : ∀ z∈E, z.1.Prime ∧ z.2.Prime ∧ z.1<z.2) :
    (prescribed E).totalDegree=2*E.card := by
  have lo := (prime_hits_bound (prescribed_weight E) (prescribed_ne_zero E)).2
  rw [prescribed_hits E valid,Set.ncard_coe_Finset] at lo
  have per (z : ℕ×ℕ) : (ratioFactor z).totalDegree≤2 := by
    apply (totalDegree_add ..).trans (max_le _ _)
    · simp [totalDegree_X_pow]
    · exact (totalDegree_mul ..).trans (by simp)
  have hi : (prescribed E).totalDegree≤2*E.card := (totalDegree_finset_prod ..).trans (by
    simpa only [sum_const,nsmul_eq_mul,Nat.mul_comm] using (sum_le_sum (s:=E) fun z _ => per z))
  omega

/-- The degree-two relation chosen from 7 and 11 hits just that pair. -/
theorem seven_eleven : primeHits (prescribed {(7,11)})={(7,11)} ∧
    (prescribed {(7,11)}).totalDegree=2 := by
  have valid (z : ℕ×ℕ) (hz : z∈({(7,11)} : Finset (ℕ×ℕ))) :
      z.1.Prime ∧ z.2.Prime ∧ z.1<z.2 := by
    obtain rfl := mem_singleton.mp hz
    decide
  exact ⟨by simpa using prescribed_hits {(7,11)} valid,
    by simpa using prescribed_degree {(7,11)} valid⟩

end PrimeFactors.PrimeSumHomogeneousGrid
