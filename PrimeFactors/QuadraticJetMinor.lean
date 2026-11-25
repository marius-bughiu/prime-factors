import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PrimeFactors.QuadraticJetMinor

open Matrix Finset
open scoped Matrix

abbrev I := Fin 2 ⊕ Fin 3
abbrev Rows := Matrix I I ℤ
abbrev Pairs := Matrix I (Fin 2) ℤ

/-- Coefficients in degrees 0,1 of the remainders of Y²,Y³,Y⁴ modulo Y²−sY+p. -/
noncomputable def tail (s p : ℤ) : Matrix (Fin 3) (Fin 2) ℤ :=
  !![-p,s; -s*p,s^2-p; p^2-s^2*p,s^3-2*s*p]

noncomputable def low (A : Rows) : Pairs := fun i j => A i (Sum.inl j)

noncomputable def basis (n : ℤ) : Rows := fromBlocks !![n^2,0;0,n] 0 0 1

noncomputable def change (s p : ℤ) : Rows := fromBlocks 1 0 (tail s p) 1

noncomputable def jet (n s p : ℤ) : Rows := fromBlocks !![n^2,0;0,n] 0 (tail s p) 1

theorem basis_change (n s p : ℤ) : basis n * change s p = jet n s p := by
  simp [basis,change,jet,fromBlocks_multiply]

theorem high_unchanged (A : Rows) (s p : ℤ) : (A*change s p).toBlocks₂₂=A.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks A]
  simp [change,fromBlocks_multiply]

noncomputable def wedge (L : Pairs) (i j : I) := L i 0 * L j 1 - L i 1 * L j 0

/-- This gcd involves no roots of the common quadratic. -/
def content (n s p : ℤ) : ℕ := Int.gcd (Int.gcd (Int.gcd (n^3) (n^2*s)) (n*p)) (p^2)

private theorem dvd_g {a b c : ℤ} : a ∣ (Int.gcd b c : ℤ) ↔ a ∣ b ∧ a ∣ c :=
  ⟨fun h => ⟨h.trans Int.gcd_dvd_left,h.trans Int.gcd_dvd_right⟩,fun h => Int.dvd_coe_gcd h.1 h.2⟩

private noncomputable def table (n s p u v w z : ℤ) : Rows :=
  fromBlocks !![0,u;0,0] !![v,s*v-n*w,s^2*v-2*n*s*w;w,s*w,(s^2-p)*w]
    0 !![0,z,s*z;0,0,p*z;0,0,0]

private theorem table_formula (n s p : ℤ) (i j : I) :
    wedge (low (jet n s p)) i j =
      table n s p (n^3) (n^2*s) (n*p) (p^2) i j -
      table n s p (n^3) (n^2*s) (n*p) (p^2) j i := by
  rcases i with i|i <;> rcases j with j|j <;> fin_cases i <;> fin_cases j <;>
    simp [wedge,low,jet,tail,table,Matrix.cons_val_two] <;> ring

private theorem table_scale (a n s p u v w z : ℤ) (i j : I) :
    table n s p (a*u) (a*v) (a*w) (a*z) i j = a*table n s p u v w z i j := by
  rcases i with i|i <;> rcases j with j|j <;> fin_cases i <;> fin_cases j <;>
    simp [table,Matrix.cons_val_two] <;> ring

theorem minors_content (a n s p : ℤ) :
    (∀ i j, a ∣ wedge (low (jet n s p)) i j) ↔ a ∣ (content n s p : ℤ) := by
  simp only [content,dvd_g]
  constructor
  · intro h
    have u := h (.inl 0) (.inl 1)
    have v := h (.inl 0) (.inr 0)
    have w := h (.inl 1) (.inr 0)
    have z := h (.inr 0) (.inr 1)
    simp [table_formula,table] at u v w z
    exact ⟨⟨⟨u,v⟩,w⟩,z⟩
  · rintro ⟨⟨⟨⟨u,hu⟩,⟨v,hv⟩⟩,⟨w,hw⟩⟩,⟨z,hz⟩⟩ i j
    refine ⟨table n s p u v w z i j - table n s p u v w z j i,?_⟩
    rw [table_formula,hu,hv,hw,hz,table_scale,table_scale,mul_sub]

/-- The original five jet evaluations at a shifted integer argument. -/
noncomputable def values (n x : ℤ) : I → ℤ := Sum.elim ![n^2,n*x] ![x^2,x^3,x^4]

private theorem at_root {n s p x : ℤ} (root : x^2-s*x+p=0) (i : I) :
    low (jet n s p) i 0 + x*low (jet n s p) i 1 = values n x i := by
  rcases i with i|i <;> fin_cases i <;> simp [low,jet,tail,values,Matrix.cons_val_two]
  · ring
  · linear_combination -root
  · linear_combination -(x+s)*root
  · linear_combination -(x^2+s*x+s^2-p)*root

/-- Every two-point minor has the same Vandermonde factor, with no division by b−a. -/
theorem two_points (n a b : ℤ) (i j : I) :
    values n a i * values n b j - values n b i * values n a j =
      (b-a) * wedge (low (jet n (a+b) (a*b))) i j := by
  have ha : a^2-(a+b)*a+a*b=0 := by ring
  have hb : b^2-(a+b)*b+a*b=0 := by ring
  rw [← at_root ha i,← at_root hb j,← at_root hb i,← at_root ha j]
  unfold wedge
  ring

/-- Common divisors of the actual two-point minors. Taking absolute values gives
|b−a| times the inner gcd, also correctly zero when a=b. -/
theorem two_point_content (n a b c : ℤ) :
    (∀ i j, c ∣ values n a i*values n b j-values n b i*values n a j) ↔
    c ∣ (b-a)*(content n (a+b) (a*b):ℤ) := by
  simp_rw [two_points]
  constructor
  · intro h
    have combine {u v : ℤ} (hu : c ∣ (b-a)*u) (hv : c ∣ (b-a)*v) :
        c ∣ (b-a)*(Int.gcd u v:ℤ) := by
      rw [Int.gcd_eq_gcd_ab,mul_add,← mul_assoc,← mul_assoc]
      exact dvd_add (dvd_mul_of_dvd_left hu _) (dvd_mul_of_dvd_left hv _)
    have u := h (.inl 0) (.inl 1)
    have v := h (.inl 0) (.inr 0)
    have w := h (.inl 1) (.inr 0)
    have z := h (.inr 0) (.inr 1)
    simp [table_formula,table] at u v w z
    exact combine (combine (combine u v) w) z
  · intro h i j
    exact h.trans (mul_dvd_mul_left _ ((minors_content _ _ _ _).mpr (dvd_refl _) i j))

private theorem minors_mul (U : Rows) (L : Pairs) {a : ℤ}
    (h : ∀ i j, a ∣ wedge L i j) (i j : I) : a ∣ wedge (U*L) i j := by
  have expand : wedge (U*L) i j = ∑ r, ∑ e, U i r*U j e*wedge L r e := by
    unfold wedge
    simp only [mul_apply,sub_mul,mul_sub,Finset.sum_sub_distrib,Finset.sum_mul,Finset.mul_sum]
    congr 1 <;> rw [Finset.sum_comm] <;> apply sum_congr rfl <;> intro r _ <;> apply sum_congr rfl <;> intro e _ <;> ring
  rw [expand]
  apply Finset.dvd_sum
  intro r _
  apply Finset.dvd_sum
  intro e _
  exact dvd_mul_of_dvd_right (h r e) _

private theorem invariant (U V : Rows) (inv : V*U=1) (L : Pairs) (a : ℤ) :
    (∀ i j, a ∣ wedge (U*L) i j) ↔ ∀ i j, a ∣ wedge L i j := by
  constructor
  · intro h i j
    simpa [← Matrix.mul_assoc,inv] using minors_mul V _ h i j
  · exact minors_mul U L

private theorem remaining (A : Rows) (zeros : A.toBlocks₂₁=0) (a : ℤ) :
    (∀ i j, a ∣ wedge (low A) i j) ↔ a ∣ A.toBlocks₁₁.det := by
  have z (i : Fin 3) (j : Fin 2) : A (.inr i) (.inl j)=0 := congrFun (congrFun zeros i) j
  have det : A.toBlocks₁₁.det = wedge (low A) (.inl 0) (.inl 1) := by
    rw [Matrix.det_fin_two]
    rfl
  rw [det]
  refine ⟨fun h => h _ _,?_⟩
  intro h i j
  rcases i with i|i <;> rcases j with j|j
  · fin_cases i <;> fin_cases j <;> simp [wedge,low,mul_comm] at h ⊢
    · exact h
    · simpa [mul_comm,neg_sub] using dvd_neg.mpr h
  all_goals simp [wedge,low,z]

private theorem low_mul (U B : Rows) : low (U*B)=U*low B := rfl

/-- Three unchanged high-coefficient rows determine the index when their two
remainder coordinates vanish. V certifies the full integral change of basis U. -/
theorem projected_minor (n s p : ℤ) (U V : Rows) (inv : V*U=1)
    (zeros : ((U*basis n)*change s p).toBlocks₂₁=0) :
    (U*basis n).toBlocks₂₂.det.natAbs * content n s p = n.natAbs^3 := by
  let J := jet n s p
  let A := U*J
  have source : (U*basis n)*change s p=A := by rw [Matrix.mul_assoc,basis_change]
  have zero : A.toBlocks₂₁=0 := source ▸ zeros
  have high : A.toBlocks₂₂=(U*basis n).toBlocks₂₂ := source ▸ high_unchanged (U*basis n) s p
  have test (a : ℤ) : a ∣ A.toBlocks₁₁.det ↔ a ∣ (content n s p : ℤ) := by
    rw [← remaining A zero a]
    change (∀ i j, a ∣ wedge (low (U*J)) i j) ↔ _
    rw [low_mul,invariant U V inv]
    exact minors_content a n s p
  have idx : A.toBlocks₁₁.det.natAbs = content n s p := Nat.dvd_antisymm
    (by simpa only [Int.natAbs_ofNat] using Int.natAbs_dvd_natAbs.mpr ((test _).mp (dvd_refl _)))
    (by simpa only [Int.natAbs_ofNat] using Int.natAbs_dvd_natAbs.mpr ((test _).mpr (dvd_refl _)))
  have split : A.det=A.toBlocks₁₁.det*A.toBlocks₂₂.det := by
    calc
      A.det = (fromBlocks A.toBlocks₁₁ A.toBlocks₁₂ A.toBlocks₂₁ A.toBlocks₂₂).det :=
        by rw [fromBlocks_toBlocks]
      _ = _ := by rw [zero,det_fromBlocks_zero₂₁]
  have unit : U.det.natAbs=1 := by
    have both : V.det.natAbs=1 ∧ U.det.natAbs=1 := by
      simpa [det_mul,Int.natAbs_mul] using congrArg (fun T : Rows => T.det.natAbs) inv
    exact both.2
  have canonical : J.det=n^3 := by
    simp [J,jet,Matrix.det_fromBlocks_zero₁₂,Matrix.det_fin_two]
    ring
  have answer := congrArg Int.natAbs split.symm
  rw [Int.natAbs_mul,idx,high] at answer
  simpa [A,det_mul,Int.natAbs_mul,unit,canonical,Int.natAbs_pow,mul_comm] using answer

private theorem row_value (n s p x : ℤ) (root : x^2-s*x+p=0) (U : Rows) (i : I) :
    (U *ᵥ values n x) i = (U*low (jet n s p)) i 0+x*(U*low (jet n s p)) i 1 := by
  change (∑ j, U i j*values n x j) = _
  calc
    _ = ∑ j, (U i j*low (jet n s p) j 0+x*(U i j*low (jet n s p) j 1)) := by
      apply sum_congr rfl
      intro j _
      rw [← at_root root j]
      ring
    _ = _ := by rw [sum_add_distrib,← mul_sum]; rfl

/-- Two distinct common integer roots imply that all three quadratic remainders vanish. -/
theorem of_two_roots (n a b : ℤ) (ab : a≠b) (U : Rows)
    (ha : ∀ i : Fin 3, (U *ᵥ values n a) (.inr i)=0)
    (hb : ∀ i : Fin 3, (U *ᵥ values n b) (.inr i)=0) :
    ((U*basis n)*change (a+b) (a*b)).toBlocks₂₁=0 := by
  rw [Matrix.mul_assoc,basis_change]
  ext i j
  let L := U*low (jet n (a+b) (a*b))
  change L (.inr i) j = 0
  have vₐ : L (.inr i) 0+a*L (.inr i) 1=0 := by
    rw [← row_value n (a+b) (a*b) a (by ring) U (.inr i),ha]
  have vᵦ : L (.inr i) 0+b*L (.inr i) 1=0 := by
    rw [← row_value n (a+b) (a*b) b (by ring) U (.inr i),hb]
  have mul : (a-b)*L (.inr i) 1=0 := by linear_combination vₐ-vᵦ
  have linear := (mul_eq_zero.mp mul).resolve_left (sub_ne_zero.mpr ab)
  fin_cases j
  · simpa [linear] using vₐ
  · exact linear

private theorem coprime_combination (d q s r : ℤ) (qr : IsCoprime q r) (ds : IsCoprime d s) :
    ∃ u v w z : ℤ, u*(d*q^3)+v*(q^2*s)+w*(q*r)+z*r^2=1 := by
  obtain ⟨a,b,hab⟩ := qr
  obtain ⟨e,f,hef⟩ := ds
  have sub : b*r=1-a*q := by linarith
  have cube : (a*q)^3+b*r*(1+a*q+(a*q)^2)=1 := by rw [sub]; ring
  have sqr : (a*q)^2+b*r*(1+a*q)=1 := by rw [sub]; ring
  have rem : r=a*(q*r)+b*r^2 := by linear_combination -r*hab
  let K := e*d*b*(1+a*q+(a*q)^2)+f*s*b*(1+a*q)
  refine ⟨e*a^3,f*a^2,K*a,K*b,?_⟩
  calc
    _ = e*a^3*(d*q^3)+f*a^2*(q^2*s)+K*(a*(q*r)+b*r^2) := by ring
    _ = e*d+f*s := by rw [← rem]; dsimp [K]; linear_combination e*d*cube+f*s*sqr
    _ = 1 := hef

/-- If N=dq and the quadratic has constant d·r, these two coprimalities force
inner content d². No primality, squarefree, or splitting hypothesis is needed. -/
theorem one_factor_content (d q s r : ℤ) (qr : IsCoprime q r) (ds : IsCoprime d s) :
    content (d*q) s (d*r)=d.natAbs^2 := by
  obtain ⟨u,v,w,z,one⟩ := coprime_combination d q s r qr ds
  have test (a : ℤ) : a ∣ (content (d*q) s (d*r):ℤ) ↔ a ∣ d^2 := by
    simp only [content,dvd_g]
    constructor
    · rintro ⟨⟨⟨⟨c₀,h₀⟩,⟨c₁,h₁⟩⟩,⟨c₂,h₂⟩⟩,⟨c₃,h₃⟩⟩
      refine ⟨u*c₀+v*c₁+w*c₂+z*c₃,?_⟩
      linear_combination u*h₀+v*h₁+w*h₂+z*h₃-d^2*one
    · intro h
      have mult (x : ℤ) : a ∣ d^2*x := dvd_mul_of_dvd_left h _
      refine ⟨⟨⟨?_,?_⟩,?_⟩,?_⟩
      · convert mult (d*q^3) using 1; ring
      · convert mult (q^2*s) using 1; ring
      · convert mult (q*r) using 1; ring
      · convert mult (r^2) using 1; ring
  exact Nat.dvd_antisymm
    (by simpa only [Int.natAbs_ofNat,Int.natAbs_pow] using Int.natAbs_dvd_natAbs.mpr ((test _).mp (dvd_refl _)))
    (by simpa only [Int.natAbs_ofNat,Int.natAbs_pow] using Int.natAbs_dvd_natAbs.mpr ((test _).mpr (dvd_refl _)))

/-- Under the one-factor conditions, the retained three-row minor is Nq². -/
theorem factor_minor (d q : ℕ) (pos : 0<d) (s r : ℤ)
    (copq : IsCoprime (q:ℤ) r) (copd : IsCoprime (d:ℤ) s) (U V : Rows) (inv : V*U=1)
    (zeros : ((U*basis ((d:ℤ)*q))*change s ((d:ℤ)*r)).toBlocks₂₁=0) :
    (U*basis ((d:ℤ)*q)).toBlocks₂₂.det.natAbs = (d*q)*q^2 := by
  have iden := projected_minor ((d:ℤ)*q) s ((d:ℤ)*r) U V inv zeros
  rw [one_factor_content _ _ _ _ copq copd,Int.natAbs_mul,Int.natAbs_ofNat,
    Int.natAbs_ofNat] at iden
  apply Nat.eq_of_mul_eq_mul_right (pow_pos pos 2)
  calc
    _ = (d*q)^3 := iden
    _ = _ := by ring

/-- On 6901 the roots 67 and 1 give inner content 67² and minor 6901·103². -/
theorem example_content : content 6901 68 67=67^2 ∧
    (6901:ℕ)^3/(content 6901 68 67)=6901*103^2 := by decide +kernel

end PrimeFactors.QuadraticJetMinor
