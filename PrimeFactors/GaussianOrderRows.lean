import PrimeFactors.ReflectedGeometricBlocks
import PrimeFactors.GeometricPrincipalLift
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Prime.Factorial

/-! Low Gaussian coefficients at the public row index N=pq can only split
the two primes when the same base has different multiplicative orders.
The block coefficients include the usual sign and unit power of the base. -/
namespace PrimeFactors.GaussianOrderRows
open Polynomial Finset ReflectedGeometricBlocks

/-- One complete orbit contributes only a constant and a term of degree d. -/
theorem cycle {R : Type*} [CommRing R] [IsDomain R] {h : R} {d : ℕ}
    (dp : 0<d) (prim : IsPrimitiveRoot h d) : block h d = 1-X^d := by
  classical
  letI : NeZero d := ⟨dp.ne'⟩
  have pc : IsPrimitiveRoot (C h : R[X]) d := prim.map_of_injective C_injective
  calc block h d = ∏ z ∈ nthRootsFinset d (1:R[X]), (1-z*X) := by
         unfold block
         apply prod_bij (fun i _ => (C h:R[X])^i)
         · intro i hi
           apply (mem_nthRootsFinset dp _).mpr
           rw [←pow_mul,mul_comm,pow_mul,pc.pow_eq_one,one_pow]
         · exact fun i hi j hj eq => pc.pow_inj (mem_range.mp hi) (mem_range.mp hj) eq
         · intro z hz
           obtain ⟨i,hi,eq⟩ := pc.eq_pow_of_pow_eq_one ((mem_nthRootsFinset dp _).mp hz)
           exact ⟨i,mem_range.mpr hi,eq⟩
         · intro i hi
           rw [map_pow]
       _ = 1-X^d := by simpa only [one_pow] using (pc.pow_sub_pow_eq_prod_sub_mul 1 X dp).symm

private theorem period_add {R : Type*} [CommRing R] {h : R} {d : ℕ}
    (period : h^d=1) (m t : ℕ) :
    block h (d*m+t)=block h (d*m)*block h t := by
  unfold block
  rw [prod_range_add]
  simp only [pow_add,pow_mul,period,one_pow,one_mul]

theorem cycles {R : Type*} [CommRing R] [IsDomain R] {h : R} {d : ℕ}
    (dp : 0<d) (prim : IsPrimitiveRoot h d) (m t : ℕ) :
    block h (d*m+t)=(1-X^d)^m*block h t := by
  have base : ∀ j, block h (d*j) = (1-X^d)^j := by
    intro j
    induction j with
    | zero => simp [block]
    | succ j ih => rw [Nat.mul_succ,period_add prim.pow_eq_one,ih,cycle dp prim,pow_succ]
  rw [period_add prim.pow_eq_one,base]

private theorem coeff_powers {R : Type*} [CommRing R] {d : ℕ} (dp : 0<d) (m k : ℕ) :
    (((1-X^d)^m:R[X]).coeff k) =
      if d∣k then (m.choose (k/d):R)*(-1)^(k/d) else 0 := by
  let f := (((1+X)^m:R[X]).comp (C (-1)*X))
  have ident : expand R d f = (1-X^d)^m := by
    dsimp only [f]
    simp [pow_comp,sub_eq_add_neg]
  rw [←ident,coeff_expand dp]
  simp only [f,comp_C_mul_X_coeff,coeff_one_add_X_pow]

private theorem digit_unit {p a b j : ℕ} [Fact p.Prime] (ap : a<p) (ja : j≤a) :
    ((a+p*b).choose j : ZMod p) ≠ 0 := by
  have jp := ja.trans_lt ap
  have r := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p:=p) (n:=a+p*b) (k:=j)
  simp [Nat.mod_eq_of_lt ap,Nat.mod_eq_of_lt jp,Nat.div_eq_of_lt jp] at r
  have nz : ¬p∣a.choose j := by
    intro h
    have fact := Nat.choose_mul_factorial_mul_factorial ja
    have df : p∣a.factorial := fact ▸ dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _
    exact (not_le_of_gt ap) ((Fact.out : p.Prime).dvd_factorial.mp df)
  rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr r]
  exact fun zero => nz ((ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp zero)

private theorem coeff_cycle_support {p a b d k : ℕ} [Fact p.Prime] (dp : 0<d)
    (ap : a<p) (kj : k/d≤a) :
    (((1-X^d)^(a+p*b) : (ZMod p)[X]).coeff k ≠ 0) ↔ d∣k := by
  rw [coeff_powers dp]
  by_cases h : d∣k
  · simp [h,digit_unit ap kj]
  · simp [h]

private theorem block_degree {R : Type*} [CommRing R] (h : R) (t : ℕ) : (block h t).natDegree≤t := by
  have deg (x:R) : (1-C x*X).natDegree≤1 :=
    (natDegree_sub_le ..).trans (max_le (by simp) ((natDegree_C_mul_le x X).trans natDegree_X_le))
  calc _ ≤ ∑ i ∈ range t, (1 - C (h^i)*X).natDegree := natDegree_prod_le ..
       _ ≤ ∑ _i ∈ range t, 1 := sum_le_sum (f:=fun i => (1-C (h^i)*X).natDegree) (fun i _ => deg _)
       _ = t := by simp

private theorem tail_support {R : Type*} [CommRing R] [IsDomain R] {h : R} {d t k : ℕ}
    (prim : IsPrimitiveRoot h d) (td : t<d) : (block h t).coeff k≠0 ↔ k≤t := by
  constructor
  · intro n
    by_contra! fail
    exact n (coeff_eq_zero_of_natDegree_lt ((block_degree h t).trans_lt fail))
  · intro kt
    induction k with
    | zero => simp [block,coeff_zero_eq_eval_zero,eval_prod]
    | succ k ih =>
      have prev := ih (by omega)
      have unequal : h^t≠h^k := fun e => (by omega : t≠k) (prim.pow_inj td (by omega) e)
      have rec := recurrence h t k
      intro zero
      rw [zero,mul_zero] at rec
      exact mul_ne_zero (sub_ne_zero.mpr unequal) prev rec.symm

private theorem separate_coeff {R : Type*} [CommRing R] {h : R} {d m t k : ℕ}
    (td : t<d) :
    (((1-X^d)^m * block h t).coeff k)=
    (((1-X^d)^m:R[X]).coeff (d*(k/d))) * ((block h t).coeff (k%d)) := by
  classical
  rw [coeff_mul]
  apply sum_eq_single (d*(k/d),k%d)
  · rintro ⟨i,j⟩ mem ne
    have eq : i+j=k := mem_antidiagonal.mp mem
    change ((1-X^d)^m:R[X]).coeff i*(block h t).coeff j=0
    by_cases jt : t<j
    · rw [coeff_eq_zero_of_natDegree_lt ((block_degree h t).trans_lt jt),mul_zero]
    · have bad : ¬d∣i := by
        rintro ⟨u,iu⟩
        have jk : k%d=j := by rw [←eq,iu,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt (by omega : j<d)]
        have split := Nat.mod_add_div k d
        exact ne (Prod.ext (by dsimp; omega) (by dsimp; omega))
      rw [coeff_powers (by omega),if_neg bad,zero_mul]
  · intro absent
    exact (absent (mem_antidiagonal.mpr (by simpa only [add_comm] using Nat.mod_add_div k d))).elim

/-- Gaussian vanishing in characteristic p is exactly one carry in base d,
when N=pq, d is the order of the unit base, d does not divide q, and k<p.
The test depends on the order and the public row index alone. -/
theorem public_residue {p q d k : ℕ} [Fact p.Prime] {h : ZMod p}
    (dp : 0<d) (prim : IsPrimitiveRoot h d) (foreign : ¬d∣q) (kp : k<p) :
    (block h (p*q)).coeff k ≠ 0 ↔ k%d ≤ (p*q)%d := by
  have hn : h≠0 := (prim.isUnit dp).ne_zero
  obtain ⟨a,pa⟩ := (prim.pow_eq_one_iff_dvd (p-1)).mp (ZMod.pow_card_sub_one_eq_one hn)
  have pp : 0<p := (Fact.out : p.Prime).pos
  have pe : p=d*a+1 := by omega
  let t := q%d
  let b := q/d
  have td : t<d := Nat.mod_lt _ dp
  have tp : 0<t := Nat.pos_of_ne_zero (fun zero => foreign (Nat.dvd_of_mod_eq_zero zero))
  have qe : q=d*b+t := by simpa only [b,t,add_comm] using (Nat.mod_add_div q d).symm
  have decomp : p*q=d*(t*a+p*b)+t := by
    calc p*q = p*(d*b+t) := by rw [←qe]
         _ = d*(t*a+p*b)+t := by have aux := congrArg (fun x : ℕ => x*t) pe; dsimp at aux; nlinarith only [aux]
  have nmod : (p*q)%d=t := by rw [decomp,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt td]
  have ta : t*a<p := by have := Nat.mul_le_mul_right a td.le; omega
  have jle : k/d ≤ t*a := (Nat.div_le_div_right (show k≤d*a by omega)).trans
    ((Nat.mul_div_cancel_left _ dp).le.trans (Nat.le_mul_of_pos_left a tp))
  have support := coeff_cycle_support (p:=p) (d:=d) (k:=d*(k/d)) (a:=t*a) (b:=b) dp ta
    (by rwa [Nat.mul_div_cancel_left _ dp])
  have nonzero := support.mpr (dvd_mul_right _ _)
  rw [nmod,decomp,cycles dp prim,separate_coeff td,mul_ne_zero_iff]
  rw [tail_support prim td]
  exact ⟨And.right, fun yes => ⟨nonzero,yes⟩⟩

/-- The information available if a local multiplicative order d is known. -/
def survives (n k d : ℕ) : Prop := if d=1 then k=0 else k%d≤n%d

instance (n k d : ℕ) : Decidable (survives n k d) := by
  unfold survives
  split <;> infer_instance

private theorem map_block {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T) (g : R) (n : ℕ) :
    Polynomial.map f (block g n)=block (f g) n := by simp [block,Polynomial.map_prod]

private theorem unit_base_one {p q k : ℕ} [Fact p.Prime] (kp : k<p) :
    (block (1:ZMod p) (p*q)).coeff k ≠ 0 ↔ k=0 := by
  have form : block (1:ZMod p) (p*q)=(1-X^1)^(p*q) := by simp [block]
  have r := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p:=p) (n:=p*q) (k:=k)
  simp only [Nat.mul_mod_right, Nat.mod_eq_of_lt kp,Nat.div_eq_of_lt kp,Nat.choose_zero_right,mul_one] at r
  rw [form,coeff_powers (by decide : 0<1)]
  simp only [one_dvd,if_true,Nat.div_one,(ZMod.natCast_eq_natCast_iff _ _ _).mpr r]
  cases k <;> simp

private theorem one_prime {p q d k : ℕ} [Fact p.Prime] (g : ℤ) (dp : 0<d)
    (cop : (p*q).Coprime (p-1)) (prim : IsPrimitiveRoot (g:ZMod p) d) (kp : k<p) :
    ¬p∣((block g (p*q)).coeff k).natAbs ↔ survives (p*q) k d := by
  have wd : p∣((block g (p*q)).coeff k).natAbs ↔ (p:ℤ)∣(block g (p*q)).coeff k :=
    Int.natAbs_dvd_natAbs (a:=(p:ℤ))
  rw [wd,←ZMod.intCast_zmod_eq_zero_iff_dvd]
  change (Int.castRingHom (ZMod p)) ((block g (p*q)).coeff k) ≠ 0 ↔ _
  rw [←coeff_map,map_block]
  change (block (g:ZMod p) (p*q)).coeff k ≠ 0 ↔ _
  by_cases e : d=1
  · subst d
    rw [IsPrimitiveRoot.one_right_iff.mp prim,unit_base_one kp]
    simp [survives]
  · have od := (prim.pow_eq_one_iff_dvd (p-1)).mp (ZMod.pow_card_sub_one_eq_one (prim.isUnit dp).ne_zero)
    have dis := cop.coprime_dvd_right od
    have foreign : ¬d∣q := by
      intro dq
      have h := Nat.dvd_gcd (dq.trans (dvd_mul_left q p)) (dvd_refl d)
      exact e (Nat.dvd_one.mp (dis.gcd_eq_one ▸ h))
    simpa only [survives,if_neg e] using public_residue dp prim foreign kp

/-- Exactly which of the two hidden primes divides an observable coefficient.
The common integer row uses the public product and base. The classification
depends on one local order for each prime and no further secret parameter. -/
theorem gcd_row {p q d e k : ℕ} [Fact p.Prime] [Fact q.Prime] (g : ℤ)
    (oddP : Odd p) (oddQ : Odd q) (lt : p<q) (balanced : q≤2*p) (kp : k<p)
    (dp : 0<d) (ep : 0<e) (a : IsPrimitiveRoot (g:ZMod p) d) (b : IsPrimitiveRoot (g:ZMod q) e) :
    let n := p*q
    let v := ((block g n).coeff k).natAbs
    n.gcd v=(if survives n k d then 1 else p)*(if survives n k e then 1 else q) := by
  classical
  dsimp only
  let v := ((block g (p*q)).coeff k).natAbs
  have pp := (Fact.out : p.Prime)
  have qp := (Fact.out : q.Prime)
  have cop := (Nat.coprime_primes pp qp).mpr lt.ne
  have balancedCop := GeometricPrincipalLift.balanced_coprime pp qp oddP oddQ lt balanced
  have lp : ¬p∣v ↔ survives (p*q) k d := one_prime g dp balancedCop.1 a kp
  have lq : ¬q∣v ↔ survives (p*q) k e := by
    simpa only [Nat.mul_comm q p] using one_prime (q:=p) g ep (by simpa only [Nat.mul_comm q p] using balancedCop.2) b (kp.trans lt)
  change (p*q).gcd v = _
  by_cases pd : p∣v <;> by_cases qd : q∣v
  · simp only [if_neg (fun x => lp.mpr x pd),if_neg (fun x => lq.mpr x qd)]
    exact Nat.gcd_eq_left (cop.mul_dvd_of_dvd_of_dvd pd qd)
  · simp only [if_neg (fun x => lp.mpr x pd), if_pos (lq.mp qd),mul_one]
    rw [Nat.mul_comm p q]
    exact Nat.gcd_mul_of_coprime_of_dvd (qp.coprime_iff_not_dvd.mpr qd) pd
  · simp only [if_pos (lp.mp pd),if_neg (fun x => lq.mpr x qd),one_mul]
    exact Nat.gcd_mul_of_coprime_of_dvd (pp.coprime_iff_not_dvd.mpr pd) qd
  · simp only [if_pos (lp.mp pd),if_pos (lq.mp qd),one_mul]
    exact (Nat.coprime_mul_iff_left.mpr ⟨pp.coprime_iff_not_dvd.mpr pd,qp.coprime_iff_not_dvd.mpr qd⟩).gcd_eq_one

private theorem large_order {n k d : ℕ} (kp : 0<k) (dk : k<d) :
    survives n k d ↔ ¬∃ j<k, n ≡ j [MOD d] := by
  have dn : d≠1 := by omega
  rw [survives,if_neg dn,Nat.mod_eq_of_lt dk]
  constructor
  · rintro bound ⟨j,jk,eq⟩
    change n%d=j%d at eq
    rw [Nat.mod_eq_of_lt (jk.trans dk)] at eq
    omega
  · intro no
    by_contra! fail
    exact no ⟨n%d,fail,(Nat.mod_modEq n d).symm⟩

/-- A discrepancy in a Gaussian coefficient already occurs among the
exponents 1 through k, or among comparisons of N with 0 through k-1. -/
theorem detected {n k d e : ℕ} (dp : 0<d) (ep : 0<e)
    (diff : ¬(survives n k d ↔ survives n k e)) :
    (∃ i, 0 < i ∧ i≤k ∧ ¬(d∣i ↔ e∣i)) ∨ (∃ j<k, ¬(n≡j [MOD d] ↔ n≡j [MOD e])) := by
  classical
  by_contra! missed
  obtain ⟨same,cong⟩ := missed
  apply diff
  have eq_small (a b : ℕ) (ap : 0<a) (bp : 0<b) (lt : a≤k)
      (test : ∀ i, 0 < i → i≤k → (a∣i ↔ b∣i)) : a=b := by
    have ba := (test a ap lt).mp (dvd_refl a)
    have bl := (Nat.le_of_dvd ap ba).trans lt
    exact Nat.dvd_antisymm ((test b bp bl).mpr (dvd_refl b)) ba
  by_cases dk : d≤k
  · rw [eq_small d e dp ep dk same]
  by_cases ek : e≤k
  · rw [eq_small e d ep dp ek (fun i ip ik => (same i ip ik).symm)]
  cases k with
  | zero => simp only [survives,Nat.zero_mod,Nat.zero_le,ite_self]
  | succ k =>
    rw [large_order (by omega) (by omega : k+1<d),large_order (by omega) (by omega : k+1<e)]
    exact not_congr ⟨fun ⟨j,lt,h⟩ => ⟨j,lt,(cong j lt).mp h⟩,
      fun ⟨j,lt,h⟩ => ⟨j,lt,(cong j lt).mpr h⟩⟩

private theorem pow_mod_order {R : Type*} [CommMonoid R] {h : R} {d n : ℕ}
    (prim : IsPrimitiveRoot h d) : h^(n%d)=h^n := by
  conv_rhs => rw [←Nat.mod_add_div n d,pow_add,pow_mul,prim.pow_eq_one,one_pow,mul_one]

private theorem equal_power {R : Type*} [CommMonoid R] {h : R} {d : ℕ}
    (dp : 0<d) (prim : IsPrimitiveRoot h d) (n j : ℕ) :
    h^n=h^j ↔ n≡j [MOD d] := by
  rw [←pow_mod_order (n:=n) prim,←pow_mod_order (n:=j) prim]
  exact ⟨prim.pow_inj (Nat.mod_lt _ dp) (Nat.mod_lt _ dp),fun eq => congrArg (fun i => h^i) eq⟩

private theorem power_test {p d : ℕ} [Fact p.Prime] (g : ℤ) (dp : 0<d)
    (prim : IsPrimitiveRoot (g:ZMod p) d) (n j : ℕ) :
    p∣(g^n-g^j).natAbs ↔ n≡j [MOD d] := by
  rw [show p∣(g^n-g^j).natAbs ↔ (p:ℤ)∣g^n-g^j from Int.natAbs_dvd_natAbs (a:=(p:ℤ)),
    ←ZMod.intCast_zmod_eq_zero_iff_dvd,Int.cast_sub,Int.cast_pow,Int.cast_pow,sub_eq_zero]
  exact equal_power dp prim _ _

/-- Product-only elementary differences subsume all low coefficient splits.
The witness can be located by scanning the two ranges with modular powers
and gcds. No local order is supplied to the scan. -/
theorem elementary_witness {p q d e k : ℕ} [Fact p.Prime] [Fact q.Prime] (g : ℤ)
    (oddP : Odd p) (oddQ : Odd q) (lt : p<q) (balanced : q≤2*p) (kp : k<p)
    (dp : 0<d) (ep : 0<e) (a : IsPrimitiveRoot (g:ZMod p) d) (b : IsPrimitiveRoot (g:ZMod q) e)
    (proper : let n := p*q; let v := ((block g n).coeff k).natAbs; n.gcd v≠1 ∧ n.gcd v≠n) :
    ∃ z : ℤ, ((∃ i, 0 < i ∧ i≤k ∧ z=g^i-1) ∨ (∃ j<k, z=g^(p*q)-g^j)) ∧
      ((p*q).gcd z.natAbs=p ∨ (p*q).gcd z.natAbs=q) := by
  classical
  dsimp only at proper
  rw [gcd_row g oddP oddQ lt balanced kp dp ep a b] at proper
  have unequal : ¬(survives (p*q) k d ↔ survives (p*q) k e) := by
    intro same
    by_cases h : survives (p*q) k d
    · simpa [h,same.mp h] using proper.1
    · have he := mt same.mpr h
      simpa only [if_neg h,if_neg he,ne_self_iff_false] using proper.2
  have split (z:ℤ) (xor : ¬(p∣z.natAbs ↔ q∣z.natAbs)) :
      (p*q).gcd z.natAbs=p ∨ (p*q).gcd z.natAbs=q := by
    by_cases pd : p∣z.natAbs <;> by_cases qd : q∣z.natAbs
    · exact (xor ⟨fun _ => qd,fun _ => pd⟩).elim
    · left
      rw [Nat.mul_comm p q]
      exact Nat.gcd_mul_of_coprime_of_dvd ((Fact.out : q.Prime).coprime_iff_not_dvd.mpr qd) pd
    · exact Or.inr (Nat.gcd_mul_of_coprime_of_dvd ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr pd) qd)
    · exact (xor ⟨fun h => (pd h).elim,fun h => (qd h).elim⟩).elim
  rcases detected dp ep unequal with ⟨i,ip,ik,h⟩|⟨j,jk,h⟩
  · refine ⟨g^i-g^0,Or.inl ⟨i,ip,ik,by rw [pow_zero]⟩,split _ ?_⟩
    rwa [power_test g dp a,power_test g ep b,Nat.modEq_zero_iff_dvd,Nat.modEq_zero_iff_dvd]
  · exact ⟨_,Or.inr ⟨j,jk,rfl⟩,split _ (by rwa [power_test g dp a,power_test g ep b])⟩

/-- The same search implication with only the public coprimality check on
the base. The two orders exist in the proof and need never be computed. -/
theorem order_free {p q k : ℕ} [Fact p.Prime] [Fact q.Prime] (g : ℤ)
    (oddP : Odd p) (oddQ : Odd q) (lt : p<q) (balanced : q≤2*p) (kp : k<p)
    (unit : (p*q).Coprime g.natAbs)
    (proper : let n := p*q; let v := ((block g n).coeff k).natAbs; n.gcd v≠1 ∧ n.gcd v≠n) :
    ∃ z : ℤ, ((∃ i, 0 < i ∧ i≤k ∧ z=g^i-1) ∨ (∃ j<k, z=g^(p*q)-g^j)) ∧
      ((p*q).gcd z.natAbs=p ∨ (p*q).gcd z.natAbs=q) := by
  have positive (r : ℕ) [Fact r.Prime] (div : r∣p*q) : 0<orderOf (g:ZMod r) := by
    have pr := (Fact.out : r.Prime)
    have nz := pr.coprime_iff_not_dvd.mp (unit.coprime_dvd_left div)
    have field : (g:ZMod r)≠0 := fun z => nz (Int.natAbs_dvd_natAbs.mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd g r).mp z))
    have power := (IsPrimitiveRoot.orderOf (g:ZMod r)).pow_eq_one_iff_dvd (r-1)
    exact Nat.pos_of_dvd_of_pos (power.mp (ZMod.pow_card_sub_one_eq_one field))
      (Nat.sub_pos_of_lt pr.one_lt)
  exact elementary_witness g oddP oddQ lt balanced kp (positive p (dvd_mul_right p q))
    (positive q (dvd_mul_left q p)) (IsPrimitiveRoot.orderOf _) (IsPrimitiveRoot.orderOf _) proper

private theorem finite_order {M : Type*} [CommMonoid M] {x : M} {d : ℕ} (dp : 0<d)
    (per : x^d=1) (checked : ∀ i : Fin d, x^(i:ℕ)=1 → (i:ℕ)=0) : IsPrimitiveRoot x d := by
  refine ⟨per,fun n hn => Nat.dvd_of_mod_eq_zero (checked ⟨n%d,Nat.mod_lt _ dp⟩ ?_)⟩
  have eq : x^(n%d)=x^n := by
    conv_rhs => rw [←Nat.mod_add_div n d,pow_add,pow_mul,per,one_pow,mul_one]
  exact eq.trans hn

/-- The coefficient and an elementary difference split the same product. -/
theorem example143 :
    (143:ℕ).gcd ((block (2:ℤ) 143).coeff 4).natAbs=11 ∧
    (143:ℕ).gcd (2^143-2^3)=11 := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  have a : IsPrimitiveRoot (2:ZMod 11) 10 := finite_order (by decide) (by decide +kernel) (by decide +kernel)
  have b : IsPrimitiveRoot (2:ZMod 13) 12 := finite_order (by decide) (by decide +kernel) (by decide +kernel)
  have value := gcd_row (p:=11) (q:=13) (k:=4) (2:ℤ) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) a b
  exact ⟨value.trans (by decide +kernel),by decide +kernel⟩

/-- The unit base 9 has order three in both fields. None of the first
seven coefficients of row 91 gives a proper factor. -/
theorem example91 {k : ℕ} (small : k<7) :
    let g := (91:ℕ).gcd ((block (9:ℤ) 91).coeff k).natAbs
    g=1 ∨ g=91 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  have a : IsPrimitiveRoot (9:ZMod 7) 3 := finite_order (by decide) (by decide +kernel) (by decide +kernel)
  have b : IsPrimitiveRoot (9:ZMod 13) 3 := finite_order (by decide) (by decide +kernel) (by decide +kernel)
  have value := gcd_row (p:=7) (q:=13) (9:ℤ) (by decide) (by decide)
    (by decide) (by decide) small (by decide) (by decide) a b
  change (7*13).gcd ((block (9:ℤ) (7*13)).coeff k).natAbs=1 ∨ _
  rw [value]
  by_cases yes : survives (7*13) k 3 <;> simp [yes]

end PrimeFactors.GaussianOrderRows
