import PrimeFactors.GeometricReadingLift
import PrimeFactors.GeometricPrincipalLift
import PrimeFactors.GeometricNegativeDirection
import Mathlib.Data.Int.ModEq

/-! If the zero factors lift by one extra prime digit, a single scalar evaluation
contains the first surviving coefficient. The argument works at every multiplicity. -/
namespace PrimeFactors.GeometricLiftedDigit
open Finset Polynomial

private theorem product_congr {I : Finset ℕ} {f g : ℕ → ℤ} {p : ℕ}
    (eq : ∀ i∈I, f i ≡ g i [ZMOD (p:ℤ)]) :
    ∏ i∈I,f i ≡ ∏ i∈I,g i [ZMOD (p:ℤ)] := by
  apply (ZMod.intCast_eq_intCast_iff ..).mp
  push_cast
  exact prod_congr rfl (fun i h => (ZMod.intCast_eq_intCast_iff ..).mpr (eq i h))

private theorem first_digit (F : ℤ[X]) {p : ℕ} (q : ℤ)
    (hit : (p:ℤ)^2 ∣ F.coeff 0) (pos : 0<p) :
    (p:ℤ) ∣ F.eval (p*q) ∧
      F.eval (p*q)/p ≡ q*F.coeff 1 [ZMOD (p:ℤ)] := by
  obtain ⟨c,hc⟩ := hit
  let rest := c+q^2*F.coeff 2+p*q^3*F.divX.divX.divX.eval (p*q)
  have shape : F.eval (p*q) = p*(q*F.coeff 1+p*rest) := by
    rw [GeometricReadingLift.taylor_three, hc]; dsimp [rest]; ring
  have nz : (p:ℤ)≠0 := by exact_mod_cast pos.ne'
  rw [shape,Int.mul_ediv_cancel_left _ nz]
  exact ⟨dvd_mul_right .., Int.modEq_add_fac_self⟩

private theorem zero_digit (F : ℤ[X]) (p : ℕ) (q : ℤ) :
    F.eval (p*q) ≡ F.coeff 0 [ZMOD (p:ℤ)] := by
  rw [GeometricReadingLift.taylor_three]
  apply Int.modEq_iff_dvd.mpr
  exact ⟨-(q*F.coeff 1+p*q^2*F.coeff 2+(p:ℤ)^2*q^3*F.divX.divX.divX.eval (p*q)),by ring⟩

/-- At r chosen local roots, the constant term of each factor vanishes modulo p².
At t=pq this removes every contribution below order r modulo p^(r+1). -/
theorem local_digit {p : ℕ} (pos : 0<p) (q : ℤ) {H I : Finset ℕ}
    (sub : H⊆I) (f : ℕ → ℤ[X]) (hits : ∀ i∈H, (p:ℤ)^2 ∣ (f i).coeff 0) :
    let F := ∏ i∈I,f i
    F.eval (p*q) ≡ (p*q)^H.card*F.coeff H.card [ZMOD (p:ℤ)^(H.card+1)] := by
  let r := H.card
  let outer := I \ H
  let tail := ∏ i∈outer,(f i).eval (p*q)
  let reduced := ∏ i∈H,(f i).eval (p*q)/p
  let coeffs := (∏ i∈outer,(f i).coeff 0)*(∏ i∈H,(f i).coeff 1)
  have each := fun i hi => first_digit (f i) q (hits i hi) pos
  have inner : (∏ i∈H,(f i).eval (p*q)) = (p:ℤ)^r*reduced := by
    calc
      _ = ∏ i∈H, ((p:ℤ)*((f i).eval (p*q)/p)) := prod_congr rfl (fun i hi =>
        (Int.mul_ediv_cancel' (each i hi).1).symm)
      _ = _ := by rw [prod_mul_distrib,prod_const]
  have rest := product_congr (I:=outer) (fun i _ => zero_digit (f i) p q)
  have innerMod := product_congr (I:=H) (fun i hi => (each i hi).2)
  rw [prod_mul_distrib,prod_const] at innerMod
  have norm : tail*reduced ≡ q^r*coeffs [ZMOD (p:ℤ)] := by
    convert rest.mul innerMod using 1; ring
  let cast := Int.castRingHom (ZMod p)
  let F := ∏ i∈I,f i
  have correct : F.coeff r ≡ coeffs [ZMOD (p:ℤ)] := by
    have h := (GeometricMatchMoments.first_product_coefficient sub (fun i => (f i).map cast) (by
      intro i hi
      rw [coeff_map]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr
        ((show (p:ℤ)∣(p:ℤ)^2 by exact ⟨p,by ring⟩).trans (hits i hi)))).2
    apply (ZMod.intCast_eq_intCast_iff ..).mp
    change cast (F.coeff H.card) = cast coeffs
    rw [←coeff_map,show F.map cast = ∏ i∈I,(f i).map cast by simp [F,Polynomial.map_prod],h]
    simp only [coeffs,outer,map_mul,map_prod,coeff_map]
  have eq : F.eval (p*q) = (p:ℤ)^r*(tail*reduced) := by
    rw [show F=(∏ i∈outer,f i)*(∏ i∈H,f i) from (prod_sdiff sub).symm,
      eval_mul,eval_prod,eval_prod,inner]
    dsimp only [tail]; ring
  change F.eval (p*q) ≡ (p*q)^r*F.coeff r [ZMOD (p:ℤ)^(r+1)]
  rw [eq,pow_succ,mul_pow,mul_assoc]
  exact (norm.trans (correct.symm.mul_left (q^r))).mul_left'

/-- The two sets may have different members and need only contain r lifted roots
on each side. The r-th digit of any scalar representative is the same public
product coefficient modulo N. -/
theorem public_digit {p q r : ℕ} (pp : 0<p) (qp : 0<q) (cop : p.Coprime q)
    {I Hp Hq : Finset ℕ} (sp : Hp⊆I) (sq : Hq⊆I) (cp : Hp.card=r) (cq : Hq.card=r)
    (f : ℕ → ℤ[X]) (hp : ∀ i∈Hp,(p:ℤ)^2∣(f i).coeff 0)
    (hq : ∀ i∈Hq,(q:ℤ)^2∣(f i).coeff 0) (v : ℤ)
    (rep : v ≡ (∏ i∈I,f i).eval ((p:ℤ)*q) [ZMOD ((p:ℤ)*q)^(r+1)]) :
    ((p:ℤ)*q)^r ∣ v ∧ v/((p:ℤ)*q)^r ≡ (∏ i∈I,f i).coeff r [ZMOD (p:ℤ)*q] := by
  let F := ∏ i∈I,f i
  have lp := local_digit pp (q:ℤ) sp f hp
  have lq := local_digit qp (p:ℤ) sq f hq
  dsimp only at lp lq
  rw [cp] at lp
  rw [cq,mul_comm (q:ℤ) (p:ℤ)] at lq
  have gcd : ((p:ℤ)^(r+1)).natAbs.Coprime ((q:ℤ)^(r+1)).natAbs := by
    simpa only [Int.natAbs_pow,Int.natAbs_natCast] using (cop.pow_left (r+1)).pow_right (r+1)
  have combined := (Int.modEq_and_modEq_iff_modEq_mul gcd).mp ⟨lp,lq⟩
  rw [←mul_pow] at combined
  have all := rep.trans combined
  have witness := Int.modEq_iff_add_fac.mp all.symm
  obtain ⟨k,hk⟩ := witness
  let n := (p:ℤ)*q
  have shape : v=n^r*(F.coeff r+n*k) := by
    change v=n^r*F.coeff r+n^(r+1)*k at hk
    rw [hk,pow_succ]; ring
  have nz : n≠0 := by dsimp [n]; positivity
  change n^r∣v ∧ v/n^r ≡ F.coeff r [ZMOD n]
  rw [shape,Int.mul_ediv_cancel_left _ (pow_ne_zero r nz)]
  exact ⟨dvd_mul_right .., Int.modEq_add_fac_self⟩

/-- One public exponent N suffices for all r. A congruence at either original
prime gives constant-term divisibility by its square in the transported product. -/
theorem geometric {p q r E : ℕ} (hp : p.Prime) (hq : q.Prime) (po : Odd p) (qo : Odd q)
    (lt : p<q) (balanced : q≤2*p) (g z v : ℤ) {I Hp Hq : Finset ℕ}
    (sp : Hp⊆I) (sq : Hq⊆I) (cp : Hp.card=r) (cq : Hq.card=r)
    (ph : ∀ i∈Hp, g^i ≡ g^E [ZMOD (p:ℤ)]) (qh : ∀ i∈Hq, g^i ≡ g^E [ZMOD (q:ℤ)]) :
    let n := (p:ℤ)*q
    let G := g^(p*q)
    let Y := G^E
    v ≡ ∏ i∈I,(Y*(1+z*n)-(G*(1+n))^i) [ZMOD n^(r+1)] →
      n^r∣v ∧ v/n^r ≡ (GeometricReadingLift.product I Y G z).coeff r [ZMOD n] := by
  dsimp only
  let G := g^(p*q)
  let Y := G^E
  let f := GeometricMatchMoments.directionalFactor Y G z
  have c0 (i : ℕ) : (f i).coeff 0 = Y-G^i := by
    simp [f,GeometricMatchMoments.directionalFactor,coeff_zero_eq_eval_zero]
  have lifted (i : ℕ) := GeometricPrincipalLift.geometric hp hq po qo lt balanced 1 i E g
  have highP : ∀ i∈Hp,(p:ℤ)^2∣(f i).coeff 0 := by
    intro i hi; rw [c0]
    simpa only [pow_one] using ((lifted i).1.mpr (ph i hi)).dvd
  have highQ : ∀ i∈Hq,(q:ℤ)^2∣(f i).coeff 0 := by
    intro i hi; rw [c0]
    simpa only [pow_one] using ((lifted i).2.mpr (qh i hi)).dvd
  intro sample
  apply public_digit hp.pos hq.pos ((Nat.coprime_primes hp hq).mpr lt.ne) sp sq cp cq f highP highQ
  exact (GeometricReadingLift.eval_product I Y G z ((p:ℤ)*q)) ▸ sample

/-- The 33127 scalar also supplies precisely the order-two coefficient in the
integer polynomial. Only two of the eight matches modulo 157 are needed to
apply the lift; the matching set modulo 211 is {3,17}. -/
theorem example_33127_digit :
    let G := (12:ℤ)^33127
    (29202:ℤ) ≡ (GeometricReadingLift.product (range 22) (G^32763) G (-1)).coeff 2 [ZMOD 33127] := by
  let G := (12:ℤ)^33127
  let Y := G^32763
  have primeP : Nat.Prime 157 := by norm_num1
  have primeQ : Nat.Prime 211 := by norm_num1
  have hp : ∀ i ∈ ({0, 3}:Finset ℕ), (12:ℤ)^i ≡ 12^32763 [ZMOD 157] := by
    intro i hi
    apply (ZMod.intCast_eq_intCast_iff _ _ 157).mp
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl|rfl <;> simp only [Int.cast_pow, Int.cast_ofNat] <;> reduce_mod_char
  have hq : ∀ i ∈ ({3, 17}:Finset ℕ), (12:ℤ)^i ≡ 12^32763 [ZMOD 211] := by
    intro i hi
    apply (ZMod.intCast_eq_intCast_iff _ _ 211).mp
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl|rfl <;> simp only [Int.cast_pow, Int.cast_ofNat] <;> reduce_mod_char
  obtain ⟨gb,yb,value,_⟩ := GeometricNegativeDirection.example_33127
  have rep : (32046220163058:ℤ) ≡ ∏ i∈range 22, (Y*(1+(-1)*33127)-(G*(1+33127))^i)
      [ZMOD 36353507819383] := by
    apply (ZMod.intCast_eq_intCast_iff _ _ 36353507819383).mp
    simp only [Y, G, Int.cast_prod, Int.cast_sub, Int.cast_neg, Int.cast_mul, Int.cast_add,
      Int.cast_pow, Int.cast_one, Int.cast_ofNat, gb, yb, neg_one_mul, ← sub_eq_add_neg]
    exact value.symm
  have result := geometric (r:=2) (E:=32763) primeP primeQ (by decide) (by decide)
    (by decide) (by decide) 12 (-1) 32046220163058 (I:=range 22) (by decide) (by decide)
    (by decide) (by decide) hp hq rep
  exact result.2

end PrimeFactors.GeometricLiftedDigit
