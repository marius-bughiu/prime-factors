import PrimeFactors.WeightedGlobalTrace
import PrimeFactors.ReducedSlopes

/-! A clean off-gap match as a weighted sum modulo the order of the public base. -/
namespace PrimeFactors.WeightedOffGap

open TraceFoldedRight

/-- Keep the first prime orientation and invert the second. -/
def twist {G H : Type*} [Group G] [Group H] (x : G × H) : G × H := (x.1,x.2⁻¹)

def Mixed {G H : Type*} [Group G] [Group H] (x y : G × H) : Prop :=
  x=twist y ∨ x=(twist y)⁻¹

private theorem twist_pow {G H : Type*} [Group G] [Group H] (v : G × H) (e : ℕ) :
    twist (v^e)=(twist v)^e := by
  ext <;> simp [twist,inv_pow]

/-- Every useful gap for fixed left projections lies in two opposite classes
modulo the joint right period. Conversely, both classes give the same mixed
orientations up to swapping which prime is recovered. -/
theorem all_gaps {G H : Type*} [Group G] [Group H] [Finite G] [Finite H] (x v : G × H) {e f : ℕ}
    (hit : Mixed x (v^e)) :
    Mixed x (v^f) ↔ f ≡ e [MOD orderOf v] ∨ orderOf v ∣ f+e := by
  have period : orderOf (twist v)=orderOf v := by simp [twist,Prod.orderOf]
  set w := twist v
  have same : w^f=w^e ↔ f ≡ e [MOD orderOf v] := by
    rw [←period,Prod.orderOf]
    constructor
    · intro eq
      apply Nat.mod_lcm
      · exact pow_eq_pow_iff_modEq.mp (congrArg Prod.fst eq : w.1^f=w.1^e)
      · exact pow_eq_pow_iff_modEq.mp (congrArg Prod.snd eq : w.2^f=w.2^e)
    · intro eq
      exact Prod.ext (pow_eq_pow_iff_modEq.mpr (eq.of_dvd (Nat.dvd_lcm_left ..)) : w.1^f=w.1^e)
        (pow_eq_pow_iff_modEq.mpr (eq.of_dvd (Nat.dvd_lcm_right ..)) : w.2^f=w.2^e)
  have opp : w^f=(w^e)⁻¹ ↔ orderOf v ∣ f+e := by
    rw [←mul_eq_one_iff_eq_inv,←pow_add,←orderOf_dvd_iff_pow_eq_one,period]
  have exchange : w^e=(w^f)⁻¹ ↔ w^f=(w^e)⁻¹ := by
    constructor <;> intro h <;> simpa using (congrArg Inv.inv h).symm
  simp only [Mixed,twist_pow] at hit ⊢
  change x=w^f ∨ x=(w^f)⁻¹ ↔ _
  rcases hit with h|h
  · rw [h]
    exact or_congr (eq_comm.trans same) (exchange.trans opp)
  · rw [h]
    constructor
    · rintro (a|a)
      · exact Or.inr (opp.mp a.symm)
      · exact Or.inl (same.mp (inv_inj.mp a).symm)
    · rintro (a|a)
      · exact Or.inr (congrArg Inv.inv (same.mpr a).symm)
      · exact Or.inl (opp.mpr a).symm

/-- At most one positive gap can work when the menu is shorter than half a period. -/
theorem short_unique {G H : Type*} [Group G] [Group H] [Finite G] [Finite H] (x v : G × H) {e f D : ℕ}
    (ep : 0<e) (ec : e≤D) (fc : f≤D) (short : 2*D<orderOf v)
    (he : Mixed x (v^e)) (hf : Mixed x (v^f)) : f=e := by
  rcases (all_gaps x v he).mp hf with same|opp
  · exact same.eq_of_lt_of_lt (by omega) (by omega)
  · have := Nat.le_of_dvd (by omega : 0<f+e) opp
    omega

/-- The two reduced orders for the full predecessor are coprime, and their
product divides the joint half-predecessor period used above. -/
theorem reduced_period {p q h : ℕ} (hp : p.Prime) (hq : q.Prime) (odd : p*q=2*h+1)
    (x : (ZMod p)ˣ) (y : (ZMod q)ˣ) :
    orderOf (x^(p*q-1))*orderOf (y^(p*q-1)) ∣ orderOf ((x,y)^h) := by
  apply (reduced_periods_coprime hp hq x y).mul_dvd_of_dvd_of_dvd
  · rw [Prod.orderOf]
    change _ ∣ (orderOf (x^h)).lcm (orderOf (y^h))
    rw [show p*q-1=h*2 by omega,pow_mul]
    exact (orderOf_pow_dvd _).trans (Nat.dvd_lcm_left ..)
  · rw [Prod.orderOf]
    change _ ∣ (orderOf (x^h)).lcm (orderOf (y^h))
    rw [show p*q-1=h*2 by omega,pow_mul]
    exact (orderOf_pow_dvd _).trans (Nat.dvd_lcm_right ..)

/-- Put p=2P+1, q=2Q+1. Then h=(pq−1)/2 and Q−P=(q−p)/2. -/
private theorem local_centers {P Q p q : ℕ} (pp : p=2*P+1) (qq : q=2*Q+1)
    (hp : p.Prime) (hq : q.Prime) (x : (ZMod p)ˣ) (y : (ZMod q)ˣ) :
    let u := (x,y)
    let h := (p*q)/2
    let j := (Q:ℤ)-P
    u^j=twist (u^h) ∧ u^(h+1)=u^(P+Q+1) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  have hN : (p*q)/2=2*P*Q+P+Q := by
    rw [pp,qq,show (2*P+1)*(2*Q+1)=2*(2*P*Q+P+Q)+1 by ring]; omega
  have dp : (orderOf x:ℤ) ∣ 2*(P:ℤ) := by
    have hd := orderOf_dvd_of_pow_eq_one (ZMod.units_pow_card_sub_one_eq_one p x)
    rw [show p-1=2*P by omega] at hd
    exact_mod_cast hd
  have dq : (orderOf y:ℤ) ∣ 2*(Q:ℤ) := by
    have hd := orderOf_dvd_of_pow_eq_one (ZMod.units_pow_card_sub_one_eq_one q y)
    rw [show q-1=2*Q by omega] at hd
    exact_mod_cast hd
  dsimp only
  rw [hN]
  constructor
  · apply Prod.ext
    · change x^((Q:ℤ)-P)=x^(2*P*Q+P+Q)
      rw [←zpow_natCast,←orderOf_dvd_sub_iff_zpow_eq_zpow]
      push_cast
      convert dvd_mul_of_dvd_left dp (-(Q:ℤ)-1) using 1; ring
    · change y^((Q:ℤ)-P)=(y^(2*P*Q+P+Q))⁻¹
      rw [←zpow_natCast,←zpow_neg,←orderOf_dvd_sub_iff_zpow_eq_zpow]
      push_cast
      convert dvd_mul_of_dvd_left dq ((P:ℤ)+1) using 1; ring
  · apply Prod.ext
    · change x^(2*P*Q+P+Q+1)=x^(P+Q+1)
      rw [←zpow_natCast,←zpow_natCast,←orderOf_dvd_sub_iff_zpow_eq_zpow]
      push_cast
      convert dvd_mul_of_dvd_left dp (Q:ℤ) using 1; ring
    · change y^(2*P*Q+P+Q+1)=y^(P+Q+1)
      rw [←zpow_natCast,←zpow_natCast,←orderOf_dvd_sub_iff_zpow_eq_zpow]
      push_cast
      convert dvd_mul_of_dvd_left dq (P:ℤ) using 1; ring

/-- The exact two exponent residues of a clean split. With p=2P+1 and
q=2Q+1 the coefficient P+Q+1 is the factor midpoint and Q−P the signed
half-gap. The modulus is the order of the base in both CRT coordinates. -/
theorem alternate_sums {P Q p q : ℕ} (pp : p=2*P+1) (qq : q=2*Q+1)
    (hp : p.Prime) (hq : q.Prime) (x : (ZMod p)ˣ) (y : (ZMod q)ˣ) (c s e : ℕ) :
    let u := (x,y)
    let h := p*q/2
    let m := (P:ℤ)+Q+1
    let j := (Q:ℤ)-P
    Mixed (WeightedGlobalTrace.left u h c s) (WeightedGlobalTrace.right u h e) ↔
      (s:ℤ) ≡ m*c+j*e [ZMOD orderOf u] ∨ (s:ℤ) ≡ m*c-j*e [ZMOD orderOf u] := by
  let u := (x,y)
  let h := p*q/2
  let m := (P:ℤ)+Q+1
  let j := (Q:ℤ)-P
  obtain ⟨hj,hm⟩ := local_centers pp qq hp hq x y
  change u^j=twist (u^h) at hj
  change u^(h+1)=u^(P+Q+1) at hm
  change Mixed (WeightedGlobalTrace.left u h c s) (WeightedGlobalTrace.right u h e) ↔ _
  rw [Mixed,WeightedGlobalTrace.left,WeightedGlobalTrace.right,pow_mul u h,twist_pow,←hj,
      pow_mul u (h+1),hm]
  have mid : u^(P+Q+1)=u^m := by dsimp [m]; norm_cast
  rw [mid]
  simp only [←zpow_natCast (u^j),←zpow_mul,←zpow_natCast (u^m),←zpow_neg]
  simp only [div_eq_iff_eq_mul,←zpow_add,←zpow_natCast u s]
  simp only [zpow_eq_zpow_iff_modEq]
  simp only [u,m,j,sub_eq_add_neg,add_comm]

/-- When either congruence is an equality, an alternate integer square
appears. This works for d>c and for different parities of c and d. -/
theorem alternate_square (P Q c e s : ℤ) (hit : s=(P+Q+1)*c+(Q-P)*e ∨
    s=(P+Q+1)*c-(Q-P)*e) :
    IsSquare (s^2-(c^2-e^2)*((2*P+1)*(2*Q+1))) := by
  rcases hit with rfl|rfl
  · exact ⟨(Q-P)*c+(P+Q+1)*e,by ring⟩
  · exact ⟨(Q-P)*c-(P+Q+1)*e,by ring⟩

variable {n : ℕ} [NeZero n] {F K : Type*} [Field F] [Field K]

noncomputable def coords (E : ZMod n ≃+* F × K) : (ZMod n)ˣ ≃* Fˣ × Kˣ :=
  (Units.mapEquiv E.toMulEquiv).trans MulEquiv.prodUnits

/-- In an arbitrary ring the discriminant of a unit trace detects whether
the square of the unit differs from 1 by another unit. -/
theorem clear_trace {R : Type*} [CommRing R] (x : Rˣ) :
    IsUnit ((x:R)^2-1) ↔ IsUnit ((trace 1 x)^2-4) := by
  have h : (x:R)^2-1=(x:R)*((x:R)-(↑(x⁻¹):R)) := by
    rw [mul_sub,Units.mul_inv,pow_two]
  have disc : (trace 1 x)^2-4=((x:R)-(↑(x⁻¹):R))^2 := by
    simp only [trace,Units.val_one,one_mul]
    linear_combination 4 * (Units.mul_inv x)
  rw [h,disc,IsUnit.mul_iff,isUnit_pow_iff (by decide : 2≠0)]
  simp [x.isUnit]

/-- A different clear gap at a correct proposed sum implies the own gap
would have split from the same coordinate. -/
theorem own_split_at_true_sum {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (cop : p.Coprime q)
    (odd : Odd (p*q)) (u : (ZMod (p*q))ˣ) (a d e : ℕ) :
    let h := p*q/2
    let x := WeightedGlobalTrace.left u h (a+(a+d)) (a*p+(a+d)*q)
    let own := WeightedGlobalTrace.right u h d
    let other := WeightedGlobalTrace.right u h e
    trace 1 x=trace 1 other → IsUnit ((other:ZMod (p*q))^2-1) →
      1<((x:ZMod (p*q))-(own:ZMod (p*q))).val.gcd (p*q) ∧
      ((x:ZMod (p*q))-(own:ZMod (p*q))).val.gcd (p*q)<p*q := by
  dsimp only
  intro hit clear
  apply WeightedGlobalTrace.proper hp hq cop odd u a d
  apply (clear_trace _).mpr
  rw [←WeightedGlobalTrace.global hp hq cop odd u a d,hit]
  exact (clear_trace _).mp clear

private theorem quadrant (x y : Fˣ × Kˣ) (cp : y.1≠y.1⁻¹) (cq : y.2≠y.2⁻¹) :
    (trace 1 x.1=trace 1 y.1 ∧ trace 1 x.2=trace 1 y.2 ∧ x≠y ∧ x≠y⁻¹) ↔ Mixed x y := by
  rcases x with ⟨x₁,x₂⟩
  rcases y with ⟨y₁,y₂⟩
  change y₁≠y₁⁻¹ at cp
  change y₂≠y₂⁻¹ at cq
  simp only [field_match,mul_eq_one_iff_eq_inv,Mixed,twist,Prod.inv_mk,inv_inv,Prod.mk.injEq]
  aesop

private theorem noninvolution {R S : Type*} [CommRing R] [Field S] (f : R →+* S)
    (y : Rˣ) (clear : IsUnit ((y:R)^2-1)) : Units.map f.toMonoidHom y≠(Units.map f.toMonoidHom y)⁻¹ := by
  intro eq
  have sq := (mul_eq_one_iff_eq_inv).mpr eq
  have val := congrArg Units.val sq
  change f (y:R)*f (y:R)=1 at val
  have z := (clear.map f).ne_zero
  apply z
  rw [map_sub,map_pow,map_one,pow_two,val,sub_self]

private theorem coprime_of_inverse (x y : (ZMod n)ˣ) (eq : x=y⁻¹) (clear : IsUnit ((y:ZMod n)^2-1)) :
    ((x:ZMod n)-(y:ZMod n)).val.Coprime n := by
  subst x
  have mul : (y:ZMod n)*((↑(y⁻¹):ZMod n)-(y:ZMod n))=-((y:ZMod n)^2-1) := by
    rw [mul_sub,Units.mul_inv,pow_two]; ring
  have unit := (IsUnit.mul_iff.mp (mul ▸ clear.neg)).2
  apply (ZMod.isUnit_iff_coprime _ _).mp
  rwa [ZMod.natCast_zmod_val]

private theorem map_trace' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : Rˣ) : f (trace 1 x)=trace 1 (Units.map f.toMonoidHom x) := by simp [trace]

/-- At a clear right entry, the equality-and-proper-gcd actually used by the
public search is equivalent to exactly the two mixed field orientations. -/
theorem observe (E : ZMod n ≃+* F × K) (x y : (ZMod n)ˣ) (clear : IsUnit ((y:ZMod n)^2-1)) :
    (trace 1 x=trace 1 y ∧ 1<((x:ZMod n)-(y:ZMod n)).val.gcd n ∧
      ((x:ZMod n)-(y:ZMod n)).val.gcd n<n) ↔ Mixed (coords E x) (coords E y) := by
  let fp := (RingHom.fst F K).comp E.toRingHom
  let fq := (RingHom.snd F K).comp E.toRingHom
  have trace_p (z : (ZMod n)ˣ) : (E (trace 1 z)).1=trace 1 (coords E z).1 :=
    map_trace' fp z
  have trace_q (z : (ZMod n)ˣ) : (E (trace 1 z)).2=trace 1 (coords E z).2 :=
    map_trace' fq z
  have cp : (coords E y).1≠(coords E y).1⁻¹ := noninvolution fp y clear
  have cq : (coords E y).2≠(coords E y).2⁻¹ := noninvolution fq y clear
  rw [←quadrant _ _ cp cq]
  constructor
  · rintro ⟨tr,gt,lt⟩
    refine ⟨by rw [←trace_p,←trace_p,tr],by rw [←trace_q,←trace_q,tr],?_,?_⟩
    · intro eq
      have eq := (coords E).injective eq
      subst x
      simp at lt
    · intro eq
      rw [←map_inv] at eq
      have eq := (coords E).injective eq
      have one := (coprime_of_inverse x y eq clear).gcd_eq_one
      omega
  · rintro ⟨a,b,c,d⟩
    have tr : trace 1 x=trace 1 y := E.injective (Prod.ext
      ((trace_p x).trans (a.trans (trace_p y).symm)) ((trace_q x).trans (b.trans (trace_q y).symm)))
    refine ⟨tr,?_⟩
    rcases TraceFoldedRight.classify 1 x y tr with eq|mate|proper
    · exact (c (congrArg (coords E) eq)).elim
    · apply False.elim
      apply d
      rw [←map_inv]
      exact congrArg (coords E) (mul_eq_one_iff_eq_inv.mp mate)
    · exact proper

/-- The exact public readout criterion, with the order of the original unit.
Its right-hand side describes the behavior using the unknown factor midpoint
and half-gap; the executable lookup needs neither. -/
theorem public_iff {P Q p q : ℕ} (pp : p=2*P+1) (qq : q=2*Q+1)
    (hp : p.Prime) (hq : q.Prime) (cop : p.Coprime q) (u : (ZMod (p*q))ˣ)
    (c s e : ℕ) :
    let h := p*q/2
    let X := WeightedGlobalTrace.left u h c s
    let Y := WeightedGlobalTrace.right u h e
    let m := (P:ℤ)+Q+1
    let j := (Q:ℤ)-P
    IsUnit ((Y:ZMod (p*q))^2-1) →
      ((trace 1 X=trace 1 Y ∧ 1<((X:ZMod (p*q))-(Y:ZMod (p*q))).val.gcd (p*q) ∧
          ((X:ZMod (p*q))-(Y:ZMod (p*q))).val.gcd (p*q)<p*q) ↔
       (s:ℤ) ≡ m*c+j*e [ZMOD orderOf u] ∨ (s:ℤ) ≡ m*c-j*e [ZMOD orderOf u]) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  letI : NeZero (p*q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  let E := ZMod.chineseRemainder cop
  let f := coords E
  let z := f u
  dsimp only
  intro clear
  rw [observe E _ _ clear]
  have left : f (WeightedGlobalTrace.left u (p*q/2) c s) =
      WeightedGlobalTrace.left z (p*q/2) c s := by simp [WeightedGlobalTrace.left,z]
  have right : f (WeightedGlobalTrace.right u (p*q/2) e) =
      WeightedGlobalTrace.right z (p*q/2) e := by simp [WeightedGlobalTrace.right,z]
  change Mixed (f _) (f _) ↔ _
  rw [left,right,←f.orderOf_eq u]
  exact alternate_sums pp qq hp hq z.1 z.2 c s e

/-- Densities from this period refer to uniform exponent residues, not to
the geometrically chosen sequence of integer candidates in the rectangle. -/
noncomputable def residues (O : ℕ) [NeZero O] (m j : ℤ) (c : ℕ) (E : Finset ℕ) :
    Finset (ZMod O) :=
  (E.image fun e : ℕ => ((m*c+j*e:ℤ):ZMod O)) ∪ (E.image fun e : ℕ => ((m*c-j*e:ℤ):ZMod O))

theorem mem_residues {O : ℕ} [NeZero O] (s m j : ℤ) (c : ℕ) (E : Finset ℕ) :
    (s:ZMod O)∈residues O m j c E ↔ ∃ e∈E,
      s ≡ m*c+j*e [ZMOD O] ∨ s ≡ m*c-j*e [ZMOD O] := by
  simp only [residues,Finset.mem_union,Finset.mem_image,ZMod.intCast_eq_intCast_iff]
  constructor
  · rintro (⟨e,mem,eq⟩|⟨e,mem,eq⟩)
    · exact ⟨e,mem,Or.inl eq.symm⟩
    · exact ⟨e,mem,Or.inr eq.symm⟩
  · rintro ⟨e,mem,eq|eq⟩
    · exact Or.inl ⟨e,mem,eq.symm⟩
    · exact Or.inr ⟨e,mem,eq.symm⟩

theorem residue_budget {O : ℕ} [NeZero O] (m j : ℤ) (c : ℕ) (E : Finset ℕ) :
    (residues O m j c E).card≤2*E.card :=
  (Finset.card_union_le ..).trans (by
    have up := Finset.card_image_le (s:=E) (f:=fun e : ℕ => ((m*c+j*e:ℤ):ZMod O))
    have down := Finset.card_image_le (s:=E) (f:=fun e : ℕ => ((m*c-j*e:ℤ):ZMod O))
    omega)

set_option exponentiation.threshold 4096 in
/-- Public coarse dimension bounds for a left assignment and independently
chosen right-gap assignment in the full-width rectangle. -/
theorem width_caps {N a b a' b' s : ℕ} (lo : 2^2047≤N) (hi : N<2^2048)
    (coordinate : s≤2*RectangularFullWidth.B N)
    (ordered : a≤b) (ordered' : a'≤b')
    (cap : a*b≤RectangularFullWidth.K N) (cap' : a'*b'≤RectangularFullWidth.K N)
    (ratio : 1024*b≤(1024+RectangularFullWidth.excess N)*a)
    (ratio' : 1024*b'≤(1024+RectangularFullWidth.excess N)*a') :
    s≤2^1367 ∧ a+b≤2^345 ∧ b'-a'≤2^344 := by
  obtain ⟨_,_,_,B,_,_,_⟩ := RectangularFullWidth.dimensions lo hi
  have np : 0<N := by omega
  have K : RectangularFullWidth.K N < 2^685+1 := by
    apply (Nat.div_lt_iff_lt_mul np).mpr
    exact (Nat.pow_le_pow_left B 2).trans_lt
      ((by decide +kernel : (2^1366:ℕ)^2<(2^685+1)*2^2047).trans_le (Nat.mul_le_mul_left _ lo))
  have pair (u v : ℕ) (ord : u≤v) (bound : u*v≤RectangularFullWidth.K N)
      (rt : 1024*v≤(1024+RectangularFullWidth.excess N)*u) :
      u≤2^343 ∧ v≤3*u := by
    have isq : u^2≤RectangularFullWidth.K N := by
      rw [pow_two]; exact (Nat.mul_le_mul_left _ ord).trans bound
    have maxsq : 2^685≤(2^343:ℕ)^2 := by decide +kernel
    have upper := (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      (isq.trans ((by omega : RectangularFullWidth.K N≤2^685).trans maxsq))
    have er := (RectangularFullWidth.excess_bound lo hi).1
    have lim := rt.trans (Nat.mul_le_mul_right u (by omega : 1024+RectangularFullWidth.excess N≤3072))
    exact ⟨upper,by omega⟩
  obtain ⟨aa,bb⟩ := pair a b ordered cap ratio
  obtain ⟨aa',bb'⟩ := pair a' b' ordered' cap' ratio'
  exact ⟨by omega,by omega,by omega⟩

set_option exponentiation.threshold 4096 in
/-- A true wrap in the 2048-bit rectangle requires a base of order below
2^1370. No assumption is made on the distribution of actual base orders. -/
theorem unwrapped {O : ℕ} {m j c e s : ℤ}
    (sm : 0≤s) (ss : s≤2^1367) (cc : 0≤c) (cs : c≤2^345)
    (ee : 0≤e) (es : e≤2^344) (mid : |m|≤2^1024) (gap : |j|≤2^1024)
    (order : 2^1370≤O)
    (hit : s ≡ m*c+j*e [ZMOD O] ∨ s ≡ m*c-j*e [ZMOD O]) :
    s=m*c+j*e ∨ s=m*c-j*e := by
  have mc : |m*c|≤(2^1024:ℤ)*2^345 := by
    rw [abs_mul,abs_of_nonneg cc]
    exact mul_le_mul mid cs cc (by positivity)
  have je : |j*e|≤(2^1024:ℤ)*2^344 := by
    rw [abs_mul,abs_of_nonneg ee]
    exact mul_le_mul gap es ee (by positivity)
  have plus := abs_add_le (m*c) (j*e)
  have minus := abs_sub (m*c) (j*e)
  have lim : (2^1024:ℤ)*2^345+2^1024*2^344+2^1367 < 2^1370 := by decide +kernel
  have ord : (2^1370:ℤ)≤O := by exact_mod_cast order
  have recover (v : ℤ) (size : |v|≤2^1024*2^345+2^1024*2^344) (eq : s ≡ v [ZMOD O]) : s=v := by
    have up := abs_sub v s
    rw [abs_of_nonneg sm] at up
    have zero := Int.eq_zero_of_abs_lt_dvd (Int.modEq_iff_dvd.mp eq) (by linarith : |v-s|<(O:ℤ))
    omega
  rcases hit with l|r
  · exact Or.inl (recover _ (by linarith) l)
  · exact Or.inr (recover _ (by linarith) r)

set_option exponentiation.threshold 4096 in
/-- At sufficiently high base order, every clean factor readout within the
two full-size weight assignments has a square alternate discriminant. -/
theorem large_order_square {P Q p q a b a' b' s : ℕ} (pp : p=2*P+1) (qq : q=2*Q+1)
    (hp : p.Prime) (hq : q.Prime) (cop : p.Coprime q) (u : (ZMod (p*q))ˣ)
    (lo : 2^2047≤p*q) (hi : p*q<2^2048) (wp : p<2^1024) (wq : q<2^1024)
    (coordinate : s≤2*RectangularFullWidth.B (p*q)) (ab : a≤b) (ab' : a'≤b')
    (cap : a*b≤RectangularFullWidth.K (p*q)) (cap' : a'*b'≤RectangularFullWidth.K (p*q))
    (ratio : 1024*b≤(1024+RectangularFullWidth.excess (p*q))*a)
    (ratio' : 1024*b'≤(1024+RectangularFullWidth.excess (p*q))*a')
    (order : 2^1370≤orderOf u) :
    let c := a+b
    let e := b'-a'
    let h := p*q/2
    let X := WeightedGlobalTrace.left u h c s
    let Y := WeightedGlobalTrace.right u h e
    IsUnit ((Y:ZMod (p*q))^2-1) → trace 1 X=trace 1 Y →
      1<((X:ZMod (p*q))-(Y:ZMod (p*q))).val.gcd (p*q) →
      ((X:ZMod (p*q))-(Y:ZMod (p*q))).val.gcd (p*q)<p*q →
      IsSquare ((s:ℤ)^2-((c:ℤ)^2-(e:ℤ)^2)*(p*q)) := by
  dsimp only
  intro clear hit gt lt
  have congr := (public_iff pp qq hp hq cop u (a+b) s (b'-a') clear).mp ⟨hit,gt,lt⟩
  obtain ⟨ss,cs,es⟩ := width_caps lo hi coordinate ab ab' cap cap' ratio ratio'
  have mid : |(P:ℤ)+Q+1|≤2^1024 := abs_le.mpr ⟨by omega,by omega⟩
  have gap : |(Q:ℤ)-P|≤2^1024 := abs_le.mpr ⟨by omega,by omega⟩
  have eq := unwrapped (Nat.cast_nonneg s) (by exact_mod_cast ss)
    (Nat.cast_nonneg (a+b)) (by exact_mod_cast cs)
    (Nat.cast_nonneg (b'-a')) (by exact_mod_cast es) mid gap order congr
  have ip : (p:ℤ)=2*P+1 := by exact_mod_cast pp
  have iq : (q:ℤ)=2*Q+1 := by exact_mod_cast qq
  rw [ip,iq]
  exact alternate_square P Q (a+b:ℕ) (b'-a':ℕ) s eq

private theorem involution_match {A : Type*} [Field A] (f : ZMod n →+* A)
    (x y : (ZMod n)ˣ) (hit : trace 1 x=trace 1 y) (sy : y^2=1) :
    Units.map f.toMonoidHom x=Units.map f.toMonoidHom y := by
    have tr := congrArg f hit
    rw [map_trace',map_trace'] at tr
    have sq := congrArg (Units.map f.toMonoidHom) sy
    rw [map_pow,map_one,pow_two] at sq
    rcases (field_match ..).mp tr with eq|mate
    · exact eq
    · exact (mul_eq_one_iff_eq_inv.mp mate).trans (mul_eq_one_iff_eq_inv.mp sq).symm

/-- A right precheck returning the whole semiprime is harmless: a full trace
match at that entry is scalar and its readout gcd is also the whole modulus. -/
theorem whole_precheck {n : ℕ} [NeZero n] {F K : Type*} [Field F] [Field K]
    (E : ZMod n ≃+* F × K) (x y : (ZMod n)ˣ)
    (whole : ((y:ZMod n)^2-1).val.gcd n=n) (hit : trace 1 x=trace 1 y) :
    ((x:ZMod n)-(y:ZMod n)).val.gcd n=n := by
  have dv := Nat.gcd_eq_right_iff_dvd.mp whole
  have small := ZMod.val_lt ((y:ZMod n)^2-1)
  have zero := (ZMod.val_eq_zero _).mp (Nat.eq_zero_of_dvd_of_lt dv small)
  have sy : y^2=1 := Units.ext (sub_eq_zero.mp zero)
  have eq : x=y := (coords E).injective (Prod.ext
    (involution_match ((RingHom.fst F K).comp E.toRingHom) x y hit sy)
    (involution_match ((RingHom.snd F K).comp E.toRingHom) x y hit sy))
  rw [eq,sub_self,ZMod.val_zero,Nat.gcd_zero_left]

end PrimeFactors.WeightedOffGap
