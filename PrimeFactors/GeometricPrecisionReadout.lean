import PrimeFactors.GeometricLiftedDigit

/-! Higher-precision digits of a geometric product over an arbitrary finite
set of labels. The two sets of local hits need not be the same. -/

namespace PrimeFactors.GeometricPrecisionReadout
open Finset Polynomial GeometricMatchMoments

private theorem transported {p n k : ℕ} (pk : 0 < k) (div : p ∣ n)
    {i E : ℕ} (g : ℤ) (hit : g^i ≡ g^E [ZMOD (p:ℤ)]) :
    let G := g^(n^(2*k-1))
    G^i ≡ G^E [ZMOD ((p:ℤ)^k)^2] := by
  have high := GeometricPrincipalLift.lift div (2*k-1) hit
  have exp : 2*k-1+1=k*2 := by omega
  rw [exp,pow_mul] at high
  dsimp only
  simpa only [←pow_mul,mul_comm i (n^_),mul_comm E (n^_)] using high

/-- For coprime positive factors, a single sample modulo T^(r+1) gives the
r-th directional reading modulo T=(pq)^k. Only r chosen local hits on each
side are needed. No balance, field or unit assumption is used here. -/
theorem public_digit {p q k r E : ℕ} (pp : 0<p) (qp : 0<q) (cop : p.Coprime q)
    (pk : 0<k) (g z v : ℤ) {I Hp Hq : Finset ℕ}
    (sp : Hp⊆I) (sq : Hq⊆I) (cp : Hp.card=r) (cq : Hq.card=r)
    (ph : ∀ i∈Hp, g^i ≡ g^E [ZMOD (p:ℤ)]) (qh : ∀ i∈Hq, g^i ≡ g^E [ZMOD (q:ℤ)]) :
    let T := ((p:ℤ)*q)^k
    let G := g^((p*q)^(2*k-1))
    let Y := G^E
    v ≡ ∏ i∈I,(Y*(1+z*T)-(G*(1+T))^i) [ZMOD T^(r+1)] →
      T^r∣v ∧ v/T^r ≡ (GeometricReadingLift.product I Y G z).coeff r [ZMOD T] := by
  dsimp only
  let G := g^((p*q)^(2*k-1))
  let Y := G^E
  let f := directionalFactor Y G z
  have hit {a : ℕ} (div : a∣p*q) {i : ℕ} (h : g^i ≡ g^E [ZMOD (a:ℤ)]) :
      ((a^k:ℕ):ℤ)^2∣(f i).coeff 0 := by
    simpa only [f,directionalFactor,coeff_zero_eq_eval_zero,eval_sub,eval_add,eval_mul,
      eval_C,eval_X,eval_pow,eval_one,mul_zero,add_zero,one_pow,mul_one,
      Nat.cast_pow] using (transported pk div g h).dvd
  have get := GeometricLiftedDigit.public_digit (pow_pos pp k) (pow_pos qp k)
    ((cop.pow_left k).pow_right k) sp sq cp cq f
    (fun i hi => hit (dvd_mul_right p q) (ph i hi)) (fun i hi => hit (dvd_mul_left q p) (qh i hi)) v
  intro sample
  rw [Nat.cast_pow,Nat.cast_pow,←mul_pow] at get
  apply get
  exact (GeometricReadingLift.eval_product I Y G z (((p:ℤ)*q)^k)) ▸ sample

/-- The label polynomial can be defined over the public ring, independently
of factorization or any particular samples, by taking a polynomial coefficient
with the direction itself an indeterminate. -/
noncomputable def signal {R : Type*} [CommRing R] (I : Finset ℕ) (y g : R) (r : ℕ) : R[X] :=
  (GeometricReadingLift.product I (C y) (C g) X).coeff r

theorem map_product {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (I : Finset ℕ) (y g z : R) :
    (GeometricReadingLift.product I y g z).map f =
      GeometricReadingLift.product I (f y) (f g) (f z) := by
  simp only [GeometricReadingLift.product,Polynomial.map_prod,directionalFactor,
    Polynomial.map_sub,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,
    Polynomial.map_C,Polynomial.map_X,Polynomial.map_one,map_mul,map_pow]

theorem eval_signal {R : Type*} [CommRing R] (I : Finset ℕ) (y g z : R) (r : ℕ) :
    (signal I y g r).eval z = (GeometricReadingLift.product I y g z).coeff r := by
  change (evalRingHom z) (signal I y g r) = _
  unfold signal
  rw [←coeff_map,map_product]
  simp

theorem map_signal {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (I : Finset ℕ) (y g : R) (r : ℕ) :
    (signal I y g r).map f = signal I (f y) (f g) r := by
  change (mapRingHom f) _ = _
  unfold signal
  rw [←coeff_map,map_product]
  simp

/-- Evaluating the symbolic public signal at z gives exactly the order-r
digit extracted from a single high-precision scalar sample. -/
theorem sample_signal {p q k r E : ℕ} (pp : 0<p) (qp : 0<q) (cop : p.Coprime q)
    (pk : 0<k) (g z v : ℤ) {I Hp Hq : Finset ℕ} (sp : Hp⊆I) (sq : Hq⊆I)
    (cp : Hp.card=r) (cq : Hq.card=r) (ph : ∀ i∈Hp, g^i ≡ g^E [ZMOD (p:ℤ)])
    (qh : ∀ i∈Hq, g^i ≡ g^E [ZMOD (q:ℤ)]) :
    let T := (p*q)^k
    let G := g^((p*q)^(2*k-1))
    let Y := G^E
    let F := (signal I Y G r).map (Int.castRingHom (ZMod T))
    v ≡ ∏ i∈I,(Y*(1+z*(T:ℤ))-(G*(1+(T:ℤ)))^i) [ZMOD (T:ℤ)^(r+1)] →
      (T:ℤ)^r∣v ∧ ((v/(T:ℤ)^r:ℤ):ZMod T)=F.eval (z:ZMod T) := by
  dsimp only
  intro h
  have digit := public_digit pp qp cop pk g z v sp sq cp cq ph qh (by
    simpa only [Nat.cast_pow,Nat.cast_mul] using h)
  constructor
  · simpa only [Nat.cast_pow,Nat.cast_mul] using digit.1
  · have target := (ZMod.intCast_eq_intCast_iff _ _ ((p*q)^k)).mpr (by
      simpa only [Nat.cast_pow,Nat.cast_mul] using digit.2)
    rw [show (z:ZMod ((p*q)^k)) = (Int.castRingHom _) z from rfl,Polynomial.eval_map,
      Polynomial.eval₂_at_apply,eval_signal]
    simpa only [Nat.cast_pow,Nat.cast_mul] using target

/-- The factorization itself holds over rings with zero divisors. The factors
may yield additional roots if two labels coincide after reduction to a field. -/
theorem factorization {R : Type*} [CommRing R] {I H : Finset ℕ} (sub : H⊆I)
    (y g : R) (hit : ∀ i∈H,g^i=y) :
    signal I y g H.card =
      C ((∏ i∈I\H,(y-g^i))*y^H.card) * ∏ i∈H,(X-C (i:R)) := by
  have eq := directional_reading sub (C y) (C g) (X : R[X]) (fun i hi => by
    rw [←map_pow,hit i hi])
  simpa only [signal,GeometricReadingLift.product,map_mul,map_prod,map_sub,map_pow,map_natCast]
    using eq

theorem root_of_mem {R : Type*} [CommRing R] {I H : Finset ℕ} (sub : H⊆I)
    (y g : R) (hit : ∀ i∈H,g^i=y) {j : ℕ} (mem : j∈H) :
    (signal I y g H.card).eval (j:R) = 0 := by
  rw [factorization sub y g hit,eval_mul,eval_prod]
  have zero : (∏ i∈H, eval (j:R) (X-C (i:R)))=0 :=
    prod_eq_zero mem (by simp)
  rw [zero,mul_zero]

/-- An arbitrary subset of original hits gives a factorization of the
coefficient modulo p^k. If another hit was omitted, the scalar can vanish. -/
theorem local_factors {p n k E : ℕ} (pk : 0<k) (div : p∣n) (g : ℤ)
    {I H : Finset ℕ} (sub : H⊆I) (hits : ∀ i∈H,g^i ≡ g^E [ZMOD (p:ℤ)]) :
    let G := g^(n^(2*k-1))
    let Y := G^E
    (signal I Y G H.card).map (Int.castRingHom (ZMod (p^k))) =
      C ((∏ i∈I\H,((Y : ZMod (p^k))-(G : ZMod (p^k))^i))*(Y : ZMod (p^k))^H.card) *
        ∏ i∈H,(X-C (i:ZMod (p^k))) := by
  dsimp only
  rw [map_signal]
  apply factorization sub
  intro i hi
  have e := (transported pk div g (hits i hi)).of_dvd
    (show (p:ℤ)^k ∣ ((p:ℤ)^k)^2 from dvd_pow_self _ (by decide : 2≠0))
  have h := (ZMod.intCast_eq_intCast_iff _ _ (p^k)).mpr (by
    simpa only [Nat.cast_pow] using e)
  rw [Int.cast_pow] at h
  exact h

/-- Raising a unit base by a power of an exponent coprime to p−1 preserves
exactly which labels hit, already at the first prime digit. -/
theorem same_hits {p n : ℕ} (hp : p.Prime) (cop : n.Coprime (p-1))
    {g : ℤ} (base : (g:ZMod p) ≠ 0) (u i E : ℕ) :
    let G := g^(n^u)
    G^i ≡ G^E [ZMOD (p:ℤ)] ↔ g^i ≡ g^E [ZMOD (p:ℤ)] := by
  letI : Fact p.Prime := ⟨hp⟩
  let b := Units.mk0 (g:ZMod p) base
  have size : Nat.card (ZMod p)ˣ=p-1 :=
    Nat.card_eq_fintype_card.trans ((Nat.prime_iff_card_units p).mp hp)
  have c : (Nat.card (ZMod p)ˣ).Coprime (n^u) := size ▸ cop.symm.pow_right u
  dsimp only
  rw [←ZMod.intCast_eq_intCast_iff,←ZMod.intCast_eq_intCast_iff]
  push_cast
  have swap (j : ℕ) : ((g:ZMod p)^(n^u))^j = ((g:ZMod p)^j)^(n^u) := by
    rw [←pow_mul,←pow_mul,mul_comm]
  rw [swap i,swap E]
  refine ⟨fun hi => ?_,fun h => congrArg (·^(n^u)) h⟩
  have h : (b^i)^(n^u) = (b^E)^(n^u) := Units.ext hi
  exact congrArg Units.val (c.pow_left_bijective.1 h)

private theorem field_hit_criterion {p n k i E : ℕ} (hp : p.Prime)
    (cop : n.Coprime (p-1)) {g : ℤ} (base : (g:ZMod p) ≠ 0) :
    let G := g^(n^(2*k-1))
    g^i ≡ g^E [ZMOD (p:ℤ)] ↔ (G:ZMod p)^i=((G^E:ℤ):ZMod p) := by
  let G := g^(n^(2*k-1))
  have stable : G^i ≡ G^E [ZMOD (p:ℤ)] ↔ g^i ≡ g^E [ZMOD (p:ℤ)] :=
    same_hits hp cop base _ i E
  change _ ↔ (G:ZMod p)^i=((G^E:ℤ):ZMod p)
  rw [←stable,←ZMod.intCast_eq_intCast_iff,Int.cast_pow]

private theorem label_top {R : Type*} [CommRing R] [Nontrivial R] (H : Finset ℕ) :
    (∏ i∈H,(X-C (i:R))).coeff H.card = 1 := by
  have degree : (∏ i∈H,(X-C (i:R))).natDegree=H.card := by
    rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)]
    simp only [natDegree_X_sub_C,sum_const,nsmul_eq_mul,mul_one,Nat.cast_id]
  rw [←degree]
  exact (monic_prod_X_sub_C _ _).coeff_natDegree

private theorem top_not_zero {p n E k : ℕ} (hp : p.Prime) (cop : n.Coprime (p-1))
    (g : ℤ) (base : (g:ZMod p) ≠ 0) {I H : Finset ℕ} (sub : H⊆I)
    (exact_hits : ∀ i∈I, i∈H ↔ g^i ≡ g^E [ZMOD (p:ℤ)]) :
    let G := g^(n^(2*k-1))
    let Y := G^E
    (((signal I Y G H.card).coeff H.card : ℤ) : ZMod p) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  dsimp only
  let G := g^(n^(2*k-1))
  let Y := G^E
  have criterion (i : ℕ) (hi : i∈I) : i∈H ↔ (G:ZMod p)^i=(Y:ZMod p) := by
    exact (exact_hits i hi).trans (field_hit_criterion hp cop base)
  change (Int.castRingHom (ZMod p)) ((signal I Y G H.card).coeff H.card) ≠ 0
  rw [←coeff_map,map_signal]
  change (signal I (Y:ZMod p) (G:ZMod p) H.card).coeff H.card ≠ 0
  rw [factorization sub _ _
    (fun i hi => (criterion i (sub hi)).mp hi),coeff_C_mul,label_top,mul_one]
  apply mul_ne_zero (prod_ne_zero_iff.mpr _) (pow_ne_zero _ _)
  · intro i hi
    exact sub_ne_zero.mpr (fun eq => (mem_sdiff.mp hi).2 ((criterion i (mem_sdiff.mp hi).1).mpr eq.symm))
  · change (Y : ZMod p) ≠ 0
    simp only [Y,G,Int.cast_pow]
    exact pow_ne_zero _ (pow_ne_zero _ base)

private theorem unit_of_two {p q k : ℕ} (hp : p.Prime) (hq : q.Prime) (hk : 0<k)
    {a : ℤ} (pa : (a:ZMod p)≠0) (qa : (a:ZMod q)≠0) :
    IsUnit (a:ZMod ((p*q)^k)) := by
  letI : NeZero ((p*q)^k) := ⟨pow_ne_zero k (Nat.mul_ne_zero hp.ne_zero hq.ne_zero)⟩
  obtain ⟨v,hv⟩ := ZMod.natCast_zmod_surjective (a:ZMod ((p*q)^k))
  have term {d : ℕ} (prime : d.Prime) (div : d ∣ p*q) (nz : (a:ZMod d)≠0) : v.Coprime d := by
    let f := ZMod.castHom (div.trans (dvd_pow_self (p*q) hk.ne')) (ZMod d)
    have reduce := congrArg f hv
    rw [map_natCast,map_intCast] at reduce
    exact (prime.coprime_iff_not_dvd.mpr
      ((ZMod.natCast_zmod_eq_zero_iff_dvd v d).mpr.mt (fun z => nz (reduce.symm.trans z)))).symm
  rw [←hv,ZMod.isUnit_iff_coprime]
  exact (Nat.coprime_mul_iff_right.mpr
    ⟨term hp (dvd_mul_right p q) pa,term hq (dvd_mul_left q p) qa⟩).pow_right k

private theorem integer_zero {p q k : ℕ} (cop : p.Coprime q) {a : ℤ}
    (atP : (a:ZMod (p^k))=0) (atQ : (a:ZMod (q^k))=0) :
    (a:ZMod ((p*q)^k))=0 := by
  have c : ((p^k:ℕ):ℤ).natAbs.Coprime ((q^k:ℕ):ℤ).natAbs := by
    simpa only [Int.natAbs_natCast] using (cop.pow_left k).pow_right k
  have ep := (ZMod.intCast_zmod_eq_zero_iff_dvd a _).mp atP
  have eq := (ZMod.intCast_zmod_eq_zero_iff_dvd a _).mp atQ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd,mul_pow,Nat.cast_mul]
  exact (Int.isCoprime_iff_nat_coprime.mpr c).mul_dvd ep eq

private theorem local_constraints {p n E k : ℕ} (hp : p.Prime) (hk : 0<k)
    (div : p∣n) (g : ℤ) {I H : Finset ℕ} (sub : H⊆I)
    (hits : ∀ i∈H,g^i ≡ g^E [ZMOD (p:ℤ)]) :
    let G := g^(n^(2*k-1))
    let F := signal I (G^E) G H.card
    (∀ t, H.card<t → (F.coeff t : ZMod (p^k))=0) ∧
      ∀ j∈H,((F.eval (j:ℤ) : ℤ) : ZMod (p^k))=0 := by
  letI : Fact (1<p^k) := ⟨Nat.one_lt_pow hk.ne' hp.one_lt⟩
  let G := g^(n^(2*k-1))
  let F := signal I (G^E) G H.card
  let U := (∏ i∈I\H,(((G^E:ℤ):ZMod (p^k))-(G:ZMod (p^k))^i))*((G^E:ℤ):ZMod (p^k))^H.card
  let D := ∏ i∈H,(X-C (i:ZMod (p^k)))
  have shape : F.map (Int.castRingHom (ZMod (p^k))) = C U*D := local_factors hk div g sub hits
  have degree : D.natDegree=H.card := by
    dsimp only [D]
    rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)]
    simp only [natDegree_X_sub_C,sum_const,nsmul_eq_mul,mul_one,Nat.cast_id]
  constructor
  · intro t high
    change (Int.castRingHom (ZMod (p^k))) (F.coeff t)=0
    rw [←coeff_map,shape,coeff_C_mul,coeff_eq_zero_of_natDegree_lt (degree ▸ high),mul_zero]
  · intro j mem
    have z : D.eval (j:ZMod (p^k))=0 := by
      rw [show D = ∏ i∈H,(X-C (i:ZMod (p^k))) from rfl,eval_prod]
      exact prod_eq_zero mem (by simp)
    change (Int.castRingHom (ZMod (p^k))) (F.eval (j:ℤ))=0
    rw [←Polynomial.eval₂_at_apply,Polynomial.eval₂_eq_eval_map,shape,eval_mul]
    rw [map_natCast,z,mul_zero]

/-- Equal exact hit counts for two balanced primes give a public polynomial
with unit leading coefficient, exact degree r, and every common hit as a root
modulo (pq)^k. The label set is arbitrary and may be disconnected. -/
theorem public_model {p q E k r : ℕ} (hp : p.Prime) (hq : q.Prime) (po : Odd p) (qo : Odd q)
    (lt : p<q) (balance : q≤2*p) (hk : 0<k) (g : ℤ)
    (gp : (g:ZMod p)≠0) (gq : (g:ZMod q)≠0) {I Hp Hq : Finset ℕ}
    (sp : Hp⊆I) (sq : Hq⊆I) (cp : Hp.card=r) (cq : Hq.card=r)
    (ph : ∀ i∈I, i∈Hp ↔ g^i ≡ g^E [ZMOD (p:ℤ)])
    (qh : ∀ i∈I, i∈Hq ↔ g^i ≡ g^E [ZMOD (q:ℤ)]) :
    let G := g^((p*q)^(2*k-1))
    let F := (signal I (G^E) G r).map (Int.castRingHom (ZMod ((p*q)^k)))
    F.natDegree=r ∧ IsUnit F.leadingCoeff ∧ ∀ j∈Hp, j∈Hq → F.eval (j:ZMod ((p*q)^k))=0 := by
  let T := (p*q)^k
  let G := g^((p*q)^(2*k-1))
  let H := signal I (G^E) G r
  let F := H.map (Int.castRingHom (ZMod T))
  have eP := local_constraints hp hk (dvd_mul_right p q) g sp (fun i h => (ph i (sp h)).mp h)
  have eQ := local_constraints hq hk (dvd_mul_left q p) g sq (fun i h => (qh i (sq h)).mp h)
  dsimp only at eP eQ
  rw [cp] at eP
  rw [cq] at eQ
  have cop := (Nat.coprime_primes hp hq).mpr lt.ne
  have group := GeometricPrincipalLift.balanced_coprime hp hq po qo lt balance
  have leadP := top_not_zero (k:=k) hp group.1 g gp sp ph
  have leadQ := top_not_zero (k:=k) hq group.2 g gq sq qh
  dsimp only at leadP leadQ
  rw [cp] at leadP
  rw [cq] at leadQ
  have unit : IsUnit (F.coeff r) := by
    rw [show F=H.map (Int.castRingHom (ZMod T)) from rfl,coeff_map]
    exact unit_of_two hp hq hk (a:=H.coeff r) leadP leadQ
  have bound : F.natDegree≤r := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro t ht
    rw [show F=H.map (Int.castRingHom (ZMod T)) from rfl,coeff_map]
    exact integer_zero cop (a:=H.coeff t) (eP.1 t ht) (eQ.1 t ht)
  letI : Fact (1<T) := ⟨Nat.one_lt_pow hk.ne' (hp.one_lt.trans_le (Nat.le_mul_of_pos_right p hq.pos))⟩
  have degree : F.natDegree=r := bound.antisymm (le_natDegree_of_ne_zero unit.ne_zero)
  refine ⟨degree,?_,?_⟩
  · change IsUnit (F.coeff F.natDegree)
    rwa [degree]
  · intro j h hpq
    change F.eval (j:ZMod T)=0
    rw [show (j:ZMod T) = (Int.castRingHom (ZMod T)) (j:ℤ) from by simp,
      show F=H.map (Int.castRingHom (ZMod T)) from rfl,Polynomial.eval_map,Polynomial.eval₂_at_apply]
    exact integer_zero cop (a:=H.eval (j:ℤ)) (eP.2 j h) (eQ.2 j hpq)

/-- Dividing by the leading unit gives an explicitly monic polynomial over
the public residue ring, preserving the degree and all previously known roots. -/
theorem make_monic {T : ℕ} (F : (ZMod T)[X]) (h : IsUnit F.leadingCoeff) :
    let P := C F.leadingCoeff⁻¹ * F
    P.Monic ∧ P.natDegree=F.natDegree ∧ ∀ z, F.eval z=0 → P.eval z=0 := by
  have u : IsUnit F.leadingCoeff⁻¹ :=
    isUnit_of_mul_eq_one _ _ (ZMod.inv_mul_of_unit _ h)
  refine ⟨?_,natDegree_C_mul_of_isUnit u F,?_⟩
  · change (C F.leadingCoeff⁻¹ * F).leadingCoeff=1
    rw [leadingCoeff_C_mul_of_isUnit u,ZMod.inv_mul_of_unit _ h]
  · intro z hz; simp [hz]

/-- At this precision the index obeys the natural univariate small-root size
inequality. This is a size comparison and does not supply a complexity bound
for producing the readings or for a lattice algorithm. -/
theorem small_root_size {N j r : ℕ} (hr : 0<r) (room : j^2<N) :
    j^r<N^((r+1)/2) := by
  have kpos : 0<(r+1)/2 := by omega
  by_cases z : j=0
  · rw [z,zero_pow hr.ne']
    exact pow_pos (by omega) _
  calc
    j^r ≤ j^(2*((r+1)/2)) := Nat.pow_le_pow_right (Nat.pos_of_ne_zero z) (by omega)
    _ = (j^2)^((r+1)/2) := pow_mul _ _ _
    _ < _ := Nat.pow_lt_pow_left room kpos.ne'

private theorem cast_eval (m j : ℕ) (F : ℤ[X]) :
    (F.map (Int.castRingHom (ZMod m))).eval (j:ZMod m) = (F.eval (j:ℤ) : ℤ) := by
  rw [show (j:ZMod m)=(Int.castRingHom (ZMod m)) (j:ℤ) from by simp,
    Polynomial.eval_map,Polynomial.eval₂_at_apply]
  rfl

private theorem field_only {p n E k j : ℕ} (hp : p.Prime) (cop : n.Coprime (p-1))
    (g : ℤ) (base : (g:ZMod p)≠0) {I H : Finset ℕ} (sub : H⊆I)
    (exact_hits : ∀ i∈I, i∈H ↔ g^i ≡ g^E [ZMOD (p:ℤ)])
    (small : ∀ i∈H,i<p) (room : j<p) :
    let G := g^(n^(2*k-1))
    let F := signal I (G^E) G H.card
    ((F.eval (j:ℤ) : ℤ) : ZMod p)=0 → j∈H := by
  letI : Fact p.Prime := ⟨hp⟩
  let G := g^(n^(2*k-1))
  let Y := G^E
  have criterion (i : ℕ) (hi : i∈I) : i∈H ↔ (G:ZMod p)^i=(Y:ZMod p) := by
    exact (exact_hits i hi).trans (field_hit_criterion hp cop base)
  have hY : (Y : ZMod p) ≠ 0 := by
    simp only [Y,G,Int.cast_pow]
    exact pow_ne_zero _ (pow_ne_zero _ base)
  dsimp only
  intro h
  change ((eval (j:ℤ) (signal I Y G H.card):ℤ):ZMod p)=0 at h
  rw [←cast_eval,map_signal] at h
  change (signal I (Y:ZMod p) (G:ZMod p) H.card).eval (j:ZMod p)=0 at h
  rw [factorization sub _ _ (fun i hi => (criterion i (sub hi)).mp hi),
    eval_mul,eval_C,eval_prod] at h
  have nz : (∏ i∈I\H,((Y:ZMod p)-(G:ZMod p)^i))*(Y:ZMod p)^H.card ≠ 0 := by
    apply mul_ne_zero (prod_ne_zero_iff.mpr _) (pow_ne_zero _ hY)
    intro i hi eq
    exact (mem_sdiff.mp hi).2 ((criterion _ (mem_sdiff.mp hi).1).mpr (sub_eq_zero.mp eq).symm)
  obtain ⟨a,ha,v⟩ := prod_eq_zero_iff.mp ((mul_eq_zero.mp h).resolve_left nz)
  simp only [eval_sub,eval_X,eval_C,sub_eq_zero] at v
  exact ((ZMod.eq_iff_modEq_nat _).mp v).eq_of_lt_of_lt room (small a ha) ▸ ha

/-- On any public label mask contained in [0,W] with W<p, the roots in this
interval are precisely the common local hits. Increasing the digit precision
does not remove any common-hit aliases. The claim includes test indices outside
the mask itself. -/
theorem in_range_iff {p q E k r W : ℕ} (hp : p.Prime) (hq : q.Prime) (po : Odd p) (qo : Odd q)
    (lt : p<q) (balance : q≤2*p) (hk : 0<k) (g : ℤ)
    (gp : (g:ZMod p)≠0) (gq : (g:ZMod q)≠0) {I Hp Hq : Finset ℕ}
    (sp : Hp⊆I) (sq : Hq⊆I) (cp : Hp.card=r) (cq : Hq.card=r)
    (ph : ∀ i∈I, i∈Hp ↔ g^i ≡ g^E [ZMOD (p:ℤ)])
    (qh : ∀ i∈I, i∈Hq ↔ g^i ≡ g^E [ZMOD (q:ℤ)])
    (mask : ∀ i∈I,i≤W) (room : W<p) {j : ℕ} (hj : j≤W) :
    let T := (p*q)^k
    let G := g^((p*q)^(2*k-1))
    let F := (signal I (G^E) G r).map (Int.castRingHom (ZMod T))
    F.eval (j:ZMod T)=0 ↔ j∈Hp∩Hq := by
  dsimp only
  refine ⟨fun h => ?_,fun h => ?_⟩
  · let G := g^((p*q)^(2*k-1))
    let z := (signal I (G^E) G r).eval (j:ℤ)
    have cast : (z:ZMod ((p*q)^k))=0 := (cast_eval _ _ _).symm.trans h
    have reduce {a : ℕ} (d : a∣p*q) : (z:ZMod a)=0 := by
      have e := congrArg (ZMod.castHom (d.trans (dvd_pow_self _ hk.ne')) (ZMod a)) cast
      simpa only [map_intCast,map_zero] using e
    have group := GeometricPrincipalLift.balanced_coprime hp hq po qo lt balance
    apply mem_inter.mpr
    constructor
    · apply field_only (k:=k) hp group.1 g gp sp ph (fun i h => (mask i (sp h)).trans_lt room)
        (hj.trans_lt room)
      simpa only [cp] using reduce (dvd_mul_right p q)
    · apply field_only (k:=k) hq group.2 g gq sq qh
        (fun i h => ((mask i (sq h)).trans_lt room).trans lt) ((hj.trans_lt room).trans lt)
      simpa only [cq] using reduce (dvd_mul_left q p)
  · exact (public_model hp hq po qo lt balance hk g gp gq sp sq cp cq ph qh).2.2 j
      (mem_inter.mp h).1 (mem_inter.mp h).2

/-- Polynomial readings at more nodes than the degree determine a unique
polynomial, even over a ring with zero divisors, when pairwise differences
are units. The degree bound is needed for both candidates. -/
theorem determined_by_nodes {R ι : Type*} [CommRing R] (S : Finset ι) (x : ι → R)
    (units : ∀ i∈S, ∀ j∈S, i≠j → IsUnit (x i-x j)) {F G : R[X]}
    (degF : F.natDegree<S.card) (degG : G.natDegree<S.card)
    (samples : ∀ i∈S,F.eval (x i)=G.eval (x i)) : F=G := by
  classical
  nontriviality R
  let D := ∏ i∈S,(X-C (x i))
  have monic : D.Monic := monic_prod_X_sub_C x S
  have degree : D.natDegree=S.card := by
    rw [show D=∏ i∈S,(X-C (x i)) from rfl,natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)]
    simp only [natDegree_X_sub_C,sum_const,nsmul_eq_mul,mul_one,Nat.cast_id]
  have div : D∣F-G := prod_dvd_of_coprime
    (fun i hi j hj ij => isCoprime_X_sub_C_of_isUnit_sub (units i hi j hj ij))
    (fun i hi => dvd_iff_isRoot.mpr (by rw [IsRoot,eval_sub,samples i hi,sub_self]))
  by_contra ne
  obtain ⟨Q,eq⟩ := div
  have nq : Q≠0 := fun h => (sub_ne_zero.mpr ne) (by simpa [h] using eq)
  have nonzero : D.leadingCoeff*Q.leadingCoeff≠0 := by
    rw [monic.leadingCoeff,one_mul]; exact leadingCoeff_ne_zero.mpr nq
  have upper := (natDegree_sub_le F G).trans_lt (max_lt degF degG)
  rw [eq,natDegree_mul' nonzero,degree] at upper
  omega

private theorem consecutive_units {n r : ℕ} (cop : r.factorial.Coprime n)
    {i j : ℕ} (ir : i≤r) (jr : j≤r) (ne : i≠j) : IsUnit ((i:ZMod n)-j) := by
  have up {a b : ℕ} (lt : b<a) (cap : a≤r) : IsUnit ((a:ZMod n)-b) := by
    rw [←Nat.cast_sub lt.le,ZMod.isUnit_iff_coprime]
    exact cop.of_dvd_left (Nat.dvd_factorial (by omega) (by omega))
  rcases lt_or_gt_of_ne ne with h|h
  · simpa only [neg_sub] using (up h jr).neg
  · exact up h ir

/-- On 0,..,r a single public gcd certifies the required unit differences. -/
theorem determined_by_consecutive {n r : ℕ} (cop : r.factorial.Coprime n)
    {F G : (ZMod n)[X]} (degF : F.natDegree≤r) (degG : G.natDegree≤r)
    (samples : ∀ i≤r,F.eval (i:ZMod n)=G.eval (i:ZMod n)) : F=G := by
  refine determined_by_nodes (range (r+1)) (fun i => (i:ZMod n)) ?_ ?_ ?_ ?_
  · intro i hi j hj ne
    exact consecutive_units cop (Nat.le_of_lt_succ (mem_range.mp hi)) (Nat.le_of_lt_succ (mem_range.mp hj)) ne
  · simpa only [card_range] using Nat.lt_succ_of_le degF
  · simpa only [card_range] using Nat.lt_succ_of_le degG
  · intro i hi; exact samples i (Nat.le_of_lt_succ (mem_range.mp hi))

/-- Explicit Lagrange interpolation uses only the public samples and modular
inverses. Correctness below requires that the positive differences be units. -/
noncomputable def from_samples (n r : ℕ) (value : ℕ → ZMod n) : (ZMod n)[X] :=
  ∑ i∈range (r+1), C (value i) *
    ∏ j∈(range (r+1)).erase i, C ((i:ZMod n)-j)⁻¹ * (X-C (j:ZMod n))

/-- The reconstruction equals any compatible public polynomial of degree ≤r.
Combined with sample_signal and public_model this justifies using r+1 digits. -/
theorem from_samples_eq {n r : ℕ} (cop : r.factorial.Coprime n) (value : ℕ → ZMod n)
    (F : (ZMod n)[X]) (degree : F.natDegree≤r) (samples : ∀ i≤r,F.eval (i:ZMod n)=value i) :
    from_samples n r value=F := by
  let S := range (r+1)
  let term (i j : ℕ) : (ZMod n)[X] := C ((i:ZMod n)-j)⁻¹*(X-C (j:ZMod n))
  have card (i : ℕ) (hi : i∈S) : (S.erase i).card=r := by
    simp only [card_erase_of_mem hi,S,card_range,Nat.add_one_sub_one]
  change (∑ i∈S,C (value i)*∏ j∈S.erase i, term i j)=F
  refine determined_by_consecutive cop ?_ degree ?_
  · apply natDegree_sum_le_of_forall_le
    intro i hi
    apply (natDegree_C_mul_le ..).trans
    apply (natDegree_prod_le ..).trans
    calc
      _ ≤ ∑ _j∈S.erase i, 1 := sum_le_sum (fun j _ =>
        (natDegree_C_mul_le _ _).trans (natDegree_X_sub_C_le (j:ZMod n)))
      _ = r := by simp only [sum_const,nsmul_eq_mul,mul_one,Nat.cast_id,card i hi]
  · intro x hx
    have mem : x∈S := mem_range.mpr (Nat.lt_succ_of_le hx)
    rw [eval_finset_sum,samples x hx,sum_eq_single_of_mem x mem]
    · rw [eval_mul,eval_C,eval_prod]
      have each (j : ℕ) (hj : j∈S.erase x) : (term x j).eval (x:ZMod n)=1 := by
        obtain ⟨ne,inside⟩ := mem_erase.mp hj
        simpa only [term,eval_mul,eval_C,eval_sub,eval_X] using
          ZMod.inv_mul_of_unit ((x:ZMod n)-(j:ZMod n)) (consecutive_units cop hx
            (Nat.le_of_lt_succ (mem_range.mp inside)) ne.symm)
      rw [prod_eq_one each,mul_one]
    · intro i _ ne
      rw [eval_mul,eval_prod,prod_eq_zero (mem_erase.mpr ⟨ne.symm,mem⟩)
        (show (term i x).eval (x:ZMod n)=0 by simp [term]),mul_zero]

end PrimeFactors.GeometricPrecisionReadout
