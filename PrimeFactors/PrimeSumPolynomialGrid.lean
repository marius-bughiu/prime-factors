import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.Tactic

/-! Bounds on the number of ordered pairs satisfying a single implicit
polynomial relation between their product and sum. The permitted grid may
be any finite set, including a finite set of primes. -/

namespace PrimeFactors.PrimeSumPolynomialGrid

open MvPolynomial Finset

variable {K : Type*} [CommRing K]

/-- The first input variable is the product and the second is the sum. -/
noncomputable def pull : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K :=
  aeval ![X 0*X 1, X 0+X 1]

/-- A relation in the two elementary symmetric polynomials can vanish
identically only if the original polynomial vanishes identically. -/
theorem pull_injective (K : Type*) [CommRing K] :
    Function.Injective (pull (K:=K)) := by
  let e : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
  let f := esymmAlgHom (Fin 2) K 2
  have sym (i : Fin 2) :
      esymm (Fin 2) K ((e i).val+1) = ![X 0*X 1, X 0+X 1] i := by
    have top : (univ : Finset (Fin 2)).powersetCard 2={univ} := by
      simpa only [card_univ,Fintype.card_fin] using powersetCard_self (univ:Finset (Fin 2))
    fin_cases i
    · change esymm (Fin 2) K 2 = X 0*X 1
      simp [esymm,top,Fin.prod_univ_two]
    · change esymm (Fin 2) K 1 = X 0+X 1
      simp [Fin.sum_univ_two]
  have transform (F : MvPolynomial (Fin 2) K) : (f (rename e F)).val=pull F := by
    rw [esymmAlgHom_apply,aeval_rename]
    unfold pull
    exact congrArg (fun g : Fin 2 → MvPolynomial (Fin 2) K => aeval g F) (funext sym)
  intro F G h
  apply rename_injective (R:=K) e e.injective
  apply esymmAlgHom_fin_injective K (le_refl 2)
  exact Subtype.ext ((transform F).trans (h.trans (transform G).symm))

theorem pull_ne_zero {F : MvPolynomial (Fin 2) K} (nz : F≠0) : pull F≠0 := by
  intro h
  exact nz (pull_injective K (h.trans (map_zero pull).symm))

theorem eval_pull (v : Fin 2 → K) (F : MvPolynomial (Fin 2) K) :
    eval v (pull F)=eval ![v 0*v 1,v 0+v 1] F := by
  change aeval v (aeval ![X 0*X 1, X 0+X 1] F) = _
  rw [comp_aeval_apply]
  change aeval _ F = aeval _ F
  apply congrArg (fun g : Fin 2 → K => aeval g F)
  funext i
  fin_cases i <;> simp

/-- Substitution at most doubles total degree. Some relations attain the
bound since the product occupies degree two in the two unknowns. -/
theorem degree_pull [Nontrivial K] (F : MvPolynomial (Fin 2) K) :
    (pull F).totalDegree ≤ 2*F.totalDegree := by
  classical
  let g : Fin 2 → MvPolynomial (Fin 2) K := ![X 0*X 1, X 0+X 1]
  have bound (i : Fin 2) : (g i).totalDegree≤2 := by
    fin_cases i
    · exact (totalDegree_mul ..).trans (by simp)
    · exact (totalDegree_add ..).trans (by simp)
  have expansion : pull F = ∑ m∈F.support, (aeval g) (monomial m (coeff m F)) := by
    simpa only [pull,map_sum,g] using congrArg (aeval g) F.as_sum
  rw [expansion]
  apply totalDegree_finsetSum_le
  intro m hm
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (by simp)]
  apply (totalDegree_mul ..).trans
  rw [algebraMap_eq,totalDegree_C,zero_add]
  apply (totalDegree_finset_prod ..).trans
  have support : (∑ i, m i)≤F.totalDegree := by
    have cap := le_sup (f:=fun u : Fin 2 →₀ ℕ => u.sum fun _ e => e) hm
    change _ ≤ F.support.sup _
    rw [←Finsupp.sum_fintype m (fun _ e => e) (fun _ => rfl)]
    exact cap
  calc
    _ ≤ ∑ i, m i*2 := sum_le_sum fun i _ =>
      (totalDegree_pow ..).trans (Nat.mul_le_mul_left _ (bound i))
    _ = (∑ i, m i)*2 := (sum_mul ..).symm
    _ ≤ 2*F.totalDegree := by omega

/-- Ordered grid pairs that satisfy the relation on their product and sum. -/
noncomputable def hits (A : Finset K) (F : MvPolynomial (Fin 2) K) : Finset (K×K) := by
  classical exact (A×ˢA).filter (fun z => eval ![z.1*z.2,z.1+z.2] F=0)

theorem mem_hits {A : Finset K} {F : MvPolynomial (Fin 2) K} {z : K×K} :
    z∈hits A F ↔ z.1∈A ∧ z.2∈A ∧ eval ![z.1*z.2,z.1+z.2] F=0 := by
  classical
  simp [hits,and_assoc]

/-- A nonzero implicit equation of total degree d covers at most
2d times the size of the coordinate alphabet. -/
theorem grid_bound [IsDomain K] (A : Finset K) (F : MvPolynomial (Fin 2) K) (nz : F≠0) :
    (hits A F).card ≤ 2*F.totalDegree*A.card := by
  classical
  obtain rfl|nonempty := A.eq_empty_or_nonempty
  · simp [hits]
  have pos : (0:ℚ≥0)<A.card := by exact_mod_cast nonempty.card_pos
  let T := (Fintype.piFinset fun _ : Fin 2 => A).filter (fun v => eval v (pull F)=0)
  have card : (hits A F).card≤T.card := by
    apply card_le_card_of_injOn (fun z : K×K => ![z.1,z.2])
    · rintro ⟨x,y⟩ h
      obtain ⟨mem,eq⟩ := mem_filter.mp h
      obtain ⟨mx,my⟩ := mem_product.mp mem
      refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i => ?_),?_⟩
      · fin_cases i <;> assumption
      · exact (eval_pull _ F).trans eq
    · intro a _ b _ h
      exact Prod.ext (congrFun h 0) (congrFun h 1)
  have schwartz := schwartz_zippel_totalDegree (pull_ne_zero nz) A
  change (T.card:ℚ≥0)/(A.card:ℚ≥0)^2 ≤ _ at schwartz
  have cleared := (div_le_div_iff₀ (pow_pos pos 2) pos).mp schwartz
  have scaled : (T.card:ℚ≥0) * A.card ≤ ((pull F).totalDegree*A.card:ℚ≥0)*A.card := by
    simpa only [pow_two, mul_assoc] using cleared
  have size : T.card≤(pull F).totalDegree*A.card := by
    exact_mod_cast (le_of_mul_le_mul_right scaled pos)
  exact card.trans (size.trans (Nat.mul_le_mul_right _ (degree_pull F)))

/-- Rational equations on a finite natural grid, with the natural product
and sum taken before casting the two inputs into the coefficient field. -/
theorem nat_grid_bound (A : Finset ℕ) (F : MvPolynomial (Fin 2) ℚ) (nz : F≠0) :
    ((A×ˢA).filter (fun z => eval ![((z.1*z.2:ℕ):ℚ),((z.1+z.2:ℕ):ℚ)] F=0)).card ≤
      2*F.totalDegree*A.card := by
  classical
  let B := A.image (fun a : ℕ => (a:ℚ))
  have size : B.card=A.card := card_image_of_injective _ Nat.cast_injective
  rw [←size]
  apply le_trans _ (grid_bound B F nz)
  apply card_le_card_of_injOn (fun z : ℕ×ℕ => ((z.1:ℚ),(z.2:ℚ)))
  · rintro ⟨x,y⟩ h
    obtain ⟨hxy,eq⟩ := mem_filter.mp h
    obtain ⟨hx,hy⟩ := mem_product.mp hxy
    exact mem_hits.mpr ⟨mem_image_of_mem _ hx,mem_image_of_mem _ hy,
      by simpa only [Nat.cast_mul,Nat.cast_add] using eq⟩
  · intro a _ b _ eq
    exact Prod.ext (Nat.cast_injective (congrArg Prod.fst eq))
      (Nat.cast_injective (congrArg Prod.snd eq))

end PrimeFactors.PrimeSumPolynomialGrid
