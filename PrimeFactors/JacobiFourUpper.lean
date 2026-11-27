import PrimeFactors.JacobiThreeTerms
/-!
# Four-term identities at prescribed prime-factor periods

These constructions use the local periods to supply each rule. The arithmetic
readout takes a certified minimum span as an input.
-/

namespace PrimeFactors.JacobiFourUpper

open JacobiMomentPeriod JacobiMomentRecurrence Polynomial Finset
open scoped Polynomial

/-- If the two local periods are 2h and 3h, the polynomial
(1+X^h)(1-X^(3h)) kills the full positive even sequence. -/
theorem exceptional {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (hp : p≠2) (hq : q≠2) (h : ℕ)
    (left : localPeriod p = 2*h) (right : localPeriod q = 3*h) (i : ℕ) :
    completeEven (p*q) (i+4*h) + completeEven (p*q) (i+3*h) =
    completeEven (p*q) (i+h) + completeEven (p*q) i := by
  let e := ZMod.chineseRemainder cop
  have crt (j : ℕ) : e (completeEven (p*q) j) = (localEven p j, localEven q j) :=
    ProjectiveWordMoments.components cop hp hq _
  have perP : Function.Periodic (localEven p) (2*h) :=
    (local_iff hp _).mpr (left ▸ dvd_rfl)
  have perQ : Function.Periodic (localEven q) (3*h) :=
    (local_iff hq _).mpr (right ▸ dvd_rfl)
  apply e.injective
  rw [map_add,map_add,crt,crt,crt,crt]
  apply Prod.ext
  · change localEven p _ + localEven p _ = localEven p _ + localEven p _
    rw [show i+4*h=i+2*h+2*h by omega,show i+3*h=i+h+2*h by omega,
      perP _,perP _,perP _,add_comm]
  · change localEven q _ + localEven q _ = localEven q _ + localEven q _
    rw [show i+4*h=i+h+3*h by omega,perQ _,perQ _]

private theorem four_witness {R : Type*} [CommRing R] [Nontrivial R]
    (u : ℕ → R) {a b c : ℕ} (ha : 0 < a) (ab : a < b) (bc : b < c)
    (x y z : R) (ux : IsUnit x) (uy : IsUnit y) (uz : IsUnit z)
    (identity : ∀ i, x*u i + y*u (i+a) + z*u (i+b) + u (i+c) = 0) :
    ∃ P : R[X], P.Monic ∧ P.support = {0,a,b,c} ∧
      (∀ j ∈ P.support, IsUnit (P.coeff j)) ∧ ∀ i, shift P u i = 0 := by
  classical
  let P : R[X] := monomial 0 x + monomial a y + monomial b z + monomial c 1
  have k0 : P.coeff 0=x := by
    simp only [P,coeff_add,coeff_monomial]
    split_ifs <;> first | omega | simp
  have ka : P.coeff a=y := by
    simp only [P,coeff_add,coeff_monomial]
    split_ifs <;> first | omega | simp
  have kb : P.coeff b=z := by
    simp only [P,coeff_add,coeff_monomial]
    split_ifs <;> first | omega | simp
  have kc : P.coeff c=1 := by
    simp only [P,coeff_add,coeff_monomial]
    split_ifs <;> first | omega | simp
  have outside (j : ℕ) (h : j∉({0,a,b,c}:Finset ℕ)) : P.coeff j=0 := by
    simp only [mem_insert,mem_singleton,not_or] at h
    simp only [P,coeff_add,coeff_monomial,if_neg (Ne.symm h.1),if_neg (Ne.symm h.2.1),
      if_neg (Ne.symm h.2.2.1),if_neg (Ne.symm h.2.2.2),add_zero]
  have at_member (j : ℕ) (h : j∈({0,a,b,c}:Finset ℕ)) : IsUnit (P.coeff j) := by
    simp only [mem_insert,mem_singleton] at h
    rcases h with rfl|rfl|rfl|rfl
    · exact k0 ▸ ux
    · exact ka ▸ uy
    · exact kb ▸ uz
    · simp [kc]
  have supp : P.support={0,a,b,c} := by
    ext j
    rw [mem_support_iff]
    exact ⟨fun ne => by_contra fun h => ne (outside j h), fun h => (at_member j h).ne_zero⟩
  have deg : P.natDegree=c := by
    apply natDegree_eq_of_le_of_coeff_ne_zero ?_ (kc ▸ one_ne_zero)
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j cj
    apply outside
    simp only [mem_insert,mem_singleton,not_or]
    omega
  refine ⟨P,?_,supp,?_,?_⟩
  · rw [Monic.def, ← coeff_natDegree,deg,kc]
  · simpa only [supp] using at_member
  · intro i
    rw [shift,supp]
    have distinct : 0∉({a,b,c}:Finset ℕ) ∧ a∉({b,c}:Finset ℕ) ∧ b∉({c}:Finset ℕ) := by
      simp only [mem_insert,mem_singleton,not_or]; omega
    rw [sum_insert distinct.1,sum_insert distinct.2.1,sum_insert distinct.2.2,sum_singleton]
    simpa only [k0,ka,kb,kc,one_mul,Nat.add_zero,add_assoc] using (identity i)

private theorem nontrivial_mod {p q : ℕ} [Fact p.Prime] [Fact q.Prime] : 1 < p*q := by
  have p2 := (Fact.out : p.Prime).two_le
  have q2 := (Fact.out : q.Prime).two_le
  nlinarith

/-- The product of the two local period binomials gives a monic rule whose
four unit coefficients occupy exactly these offsets. -/
theorem generic_witness {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (hp : p≠2) (hq : q≠2) {a b : ℕ}
    (left : localPeriod p=a) (right : localPeriod q=b) (ap : 0 < a) (ab : a < b) :
    ∃ P : (ZMod (p*q))[X], P.Monic ∧ P.support={0,a,b,a+b} ∧
      (∀ j ∈ P.support, IsUnit (P.coeff j)) ∧ ∀ i, shift P (completeEven (p*q)) i=0 := by
  haveI : Fact (1<p*q) := ⟨nontrivial_mod⟩
  apply four_witness _ ap ab (by omega) 1 (-1) (-1) isUnit_one (by simp) (by simp)
  intro i
  have w := JacobiThreeTerms.four_terms cop hp hq i
  rw [left,right,Nat.add_assoc] at w
  linear_combination w

/-- At local periods 2h and 3h a different pairing reaches span 4h. -/
theorem exceptional_witness {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (hp : p≠2) (hq : q≠2) {h : ℕ}
    (pos : 0<h) (left : localPeriod p=2*h) (right : localPeriod q=3*h) :
    ∃ P : (ZMod (p*q))[X], P.Monic ∧ P.support={0,h,3*h,4*h} ∧
      (∀ j ∈ P.support, IsUnit (P.coeff j)) ∧ ∀ i, shift P (completeEven (p*q)) i=0 := by
  haveI : Fact (1<p*q) := ⟨nontrivial_mod⟩
  apply four_witness _ pos (by omega) (by omega) (-1) (-1) 1 (by simp) (by simp) isUnit_one
  intro i
  linear_combination exceptional cop hp hq h left right i

/-- From the two possible minimum widths derive two candidate values for the sum.
The numerical hypotheses express the widths themselves. -/
theorem sum_readouts {p q a b D : ℕ} (pa : p=2*a+1) (qb : q=2*b+1)
    (width : D=a+b ∨ (2*b=3*a ∧ D=2*a)) :
    p+q=2*D+2 ∨ p+q=(5*D)/2+2 := by
  omega

/-- Each correct sum candidate gives the two ordered roots by one square root. -/
theorem read_pair {N S p q : ℕ} (prod : N=p*q) (sum : S=p+q) (ord : p≤q) :
    (S-Nat.sqrt (S^2-4*N))/2=p ∧ (S+Nat.sqrt (S^2-4*N))/2=q := by
  obtain ⟨g,eq⟩ := Nat.exists_eq_add_of_le ord
  subst q
  have sq : S^2=4*N+g^2 := by rw [sum,prod]; ring
  rw [sq,Nat.add_sub_cancel_left,Nat.sqrt_eq']
  omega

/-- The exceptional shape can be recognized directly on the product: when
p=4h+1 and q=6h+1, sqrt(24N+1) recovers both factors. -/
theorem exceptional_readout {p q h : ℕ} (pa : p=4*h+1) (qb : q=6*h+1) :
    24*(p*q)+1=(24*h+5)^2 ∧
    (Nat.sqrt (24*(p*q)+1)+1)/6=p ∧ (Nat.sqrt (24*(p*q)+1)-1)/4=q := by
  have eq : 24*(p*q)+1=(24*h+5)^2 := by rw [pa,qb]; ring
  rw [eq,Nat.sqrt_eq']
  omega

/-- The opposite sign also makes 24N+1 a square. Its integer quotients differ
from those of the exceptional minimum-span branch. -/
theorem opposite_readout {p q h : ℕ} (pa : p=4*h+3) (qb : q=6*h+5) :
    24*(p*q)+1=(24*h+19)^2 ∧
    (Nat.sqrt (24*(p*q)+1)-1)/6=p ∧ (Nat.sqrt (24*(p*q)+1)+1)/4=q := by
  have eq : 24*(p*q)+1=(24*h+19)^2 := by rw [pa,qb]; ring
  rw [eq,Nat.sqrt_eq']
  omega

local instance prime13 : Fact (Nat.Prime 13) := ⟨by decide⟩
local instance prime19 : Fact (Nat.Prime 19) := ⟨by decide⟩

theorem example247 :
    (∀ i, completeEven 247 (i+12) + completeEven 247 (i+9) =
      completeEven 247 (i+3) + completeEven 247 i) ∧
    Nat.sqrt (24*247+1)=77 ∧ (77+1)/6=13 ∧ (77-1)/4=19 := by
  exact ⟨fun i => exceptional (p:=13) (q:=19) (by decide) (by decide) (by decide) 3 rfl rfl i,
         by
           have h := exceptional_readout (p:=13) (q:=19) (h:=3) rfl rfl
           change 24*(13*19)+1=77^2 ∧ _ at h
           change Nat.sqrt (24*(13*19)+1)=77 ∧ _
           rw [h.1,Nat.sqrt_eq']; decide⟩

/-- Certified prime factorizations for all six small four-term width comparisons. -/
theorem panel_factorizations :
    ExactFactorization 143 [11,13] ∧ ExactFactorization 187 [11,17] ∧
    ExactFactorization 209 [11,19] ∧ ExactFactorization 221 [13,17] ∧
    ExactFactorization 247 [13,19] ∧ ExactFactorization 323 [17,19] := by
  norm_num [ExactFactorization]

end PrimeFactors.JacobiFourUpper
