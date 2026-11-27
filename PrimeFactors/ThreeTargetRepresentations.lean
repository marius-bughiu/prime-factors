import PrimeFactors.ThreeRootTargets
import PrimeFactors.SmallDiscriminantLattice
import Mathlib.Data.Rat.Sqrt

/-! The public three-target menu contains a signed discriminant admitting two
bounded primitive representations whose determinant splits every eligible pq. -/
namespace PrimeFactors.ThreeTargetRepresentations

open SmallDiscriminantLattice

def values : List ℤ := [-1,2,-2,3,-3,6,-6]

theorem value_bounds {D : ℤ} (mem : D∈values) :
    0<abs D ∧ abs D≤6 ∧ ¬IsSquare (D:ℚ) := by
  rw [Rat.isSquare_intCast_iff]
  simp only [values,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

private theorem value_unit {p : ℕ} [Fact p.Prime] (large : 3<p) {D : ℤ} (mem : D∈values) :
    (D:ZMod p)≠0 := by
  have two : (2:ZMod p)≠0 := by exact_mod_cast ZMod.prime_ne_zero p 2 (by omega)
  have three : (3:ZMod p)≠0 := by exact_mod_cast ZMod.prime_ne_zero p 3 (by omega)
  have six : (6:ZMod p)≠0 := by
    rw [show (6:ZMod p)=2*3 by norm_num]
    exact mul_ne_zero two three
  simp only [values,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp_all

private theorem opposite_distinct {p : ℕ} [Fact p.Prime] (large : 3<p) {D : ℤ} (mem : D∈values)
    {x : ZMod p} (square : x^2=D) : x≠-x := by
  intro eq
  have z : (2:ZMod p)*x=0 := by linear_combination eq
  have xzero := (mul_eq_zero.mp z).resolve_left (by exact_mod_cast ZMod.prime_ne_zero p 2 (by omega))
  exact value_unit large mem (by simpa [xzero] using square.symm)

theorem second_root {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (lp : 3<p) (lq : 3<q) {D : ℤ} (mem : D∈values)
    (r : ZMod (p*q)) (root : r^2=D) : ∃ t, t^2=(D:ZMod (p*q)) ∧ r≠t ∧ r≠-t := by
  let e := ZMod.chineseRemainder cop
  have both := congrArg e root
  rw [map_pow,map_intCast] at both
  have hp : (e r).1^2=(D:ZMod p) := congrArg Prod.fst both
  have hq : (e r).2^2=(D:ZMod q) := congrArg Prod.snd both
  let t := e.symm ((e r).1,-(e r).2)
  have tval : e t = ((e r).1,-(e r).2) := e.apply_symm_apply _
  refine ⟨t,e.injective ?_,?_,?_⟩
  · rw [map_pow,tval,map_intCast]
    exact Prod.ext hp (by simpa using hq)
  · intro eq
    exact opposite_distinct lq mem hq (congrArg Prod.snd ((congrArg e eq).trans tval))
  · intro eq
    have localEq := congrArg e eq
    rw [map_neg,tval] at localEq
    exact opposite_distinct lp mem hp (congrArg Prod.fst localEq)

private theorem gcd_intCast (N : ℕ) [NeZero N] (z : ℤ) : z.natAbs.gcd N = (z:ZMod N).val.gcd N := by
  have localDvd {d : ℕ} (dv : d∣N) : d∣z.natAbs ↔ d∣(z:ZMod N).val := by
    rw [← Int.natCast_dvd,← ZMod.intCast_zmod_eq_zero_iff_dvd,← ZMod.natCast_zmod_eq_zero_iff_dvd]
    have eq := congrArg (ZMod.castHom dv (ZMod d)) (ZMod.natCast_zmod_val (z:ZMod N))
    simp only [map_natCast,map_intCast] at eq
    rw [eq]
  apply Nat.dvd_antisymm
  · exact Nat.dvd_gcd ((localDvd (Nat.gcd_dvd_right ..)).mp (Nat.gcd_dvd_left ..)) (Nat.gcd_dvd_right ..)
  · exact Nat.dvd_gcd ((localDvd (Nat.gcd_dvd_right ..)).mpr (Nat.gcd_dvd_left ..)) (Nat.gcd_dvd_right ..)

/-- On the five small targets of absolute value at most three the multiplier
has absolute value one. For -3 the residue 2 modulo 4 cannot be represented.
For +3 an extreme norm of size 2N forces one coordinate to vanish, which
the same modulus rules out. Only the two targets ±6 need the larger bound. -/
theorem small_multiplier {N : ℕ} (np : 0<N) (odd : Odd N) {D : ℤ} (small : abs D ≤ 3)
    {r : ZMod N} (u : Representation N D r) : u.m.natAbs=1 := by
  obtain ⟨nz,cap⟩ := u.multiplier
  by_contra bad
  have m2 : u.m=2 ∨ u.m= -2 := by omega
  let E := u.x^2+abs D*u.y^2
  have en : 0≤E := by dsimp [E]; positivity
  have npz : 0<(N:ℤ) := by exact_mod_cast np
  have down := mul_le_mul_of_nonneg_right (neg_abs_le D) (sq_nonneg u.y)
  have up := mul_le_mul_of_nonneg_right (le_abs_self D) (sq_nonneg u.y)
  have bound := u.hermite
  change 3*E^2≤4*(abs D)*(N:ℤ)^2 at bound
  have upper : 2*(N:ℤ)≤E := by
    dsimp [E]
    rcases m2 with eq|eq <;> have h := u.norm <;> rw [eq] at h <;>
      nlinarith only [h,down,up,sq_nonneg u.x]
  have es := pow_le_pow_left₀ (by positivity : 0≤2*(N:ℤ)) upper 2
  have absD : abs D=3 := by
    by_contra! off
    have low : abs D≤2 := by omega
    nlinarith only [bound,es,mul_le_mul_of_nonneg_right low (sq_nonneg (N:ℤ)),sq_pos_of_pos npz]
  have equal : E=2*N := by
    rw [absD] at bound
    by_contra! off
    have es' := pow_lt_pow_left₀ (lt_of_le_of_ne upper (Ne.symm off)) (by positivity) (by decide : 2≠0)
    nlinarith only [bound,es']
  have twice : (2:ZMod 4)*N=2 := by
    obtain ⟨j,hj⟩ := odd
    rw [hj]; push_cast; ring_nf; rw [show (4:ZMod 4)=0 from rfl,mul_zero,add_zero]
  have modNorm : (u.x:ZMod 4)^2-(D:ZMod 4)*(u.y:ZMod 4)^2=2 := by
    have h := congrArg (fun z : ℤ => (z:ZMod 4)) u.norm
    push_cast at h
    rcases m2 with eq|eq <;> rw [eq] at h
    · simpa using h.trans (by exact twice)
    · have neg : (-2:ZMod 4)*(N:ZMod 4)=2 := by
        rw [neg_mul,twice]; decide
      simpa using h.trans (by exact neg)
  rcases le_or_gt 0 D with pos|neg
  · rw [abs_of_nonneg pos] at absD
    subst D
    have same : u.x^2+3*u.y^2=2*(N:ℤ) := by simpa [E] using equal
    have point := u.norm
    have used : (u.x:ZMod 4)≠0 ∧ (u.y:ZMod 4)≠0 :=
      (by decide : ∀ x y : ZMod 4, x^2-3*y^2=2 → x≠0 ∧ y≠0) _ _ (by simpa using modNorm)
    have xn : u.x≠0 := fun h => used.1 (by rw [h,Int.cast_zero])
    have yn : u.y≠0 := fun h => used.2 (by rw [h,Int.cast_zero])
    rcases m2 with eq|eq <;> rw [eq] at point <;> nlinarith only [same,point,sq_pos_of_ne_zero xn,sq_pos_of_ne_zero yn]
  · rw [abs_of_neg neg] at absD
    have d : D= -3 := by omega
    subst D
    exact (by decide : ∀ x y : ZMod 4, x^2-(-3)*y^2≠2) _ _ (by simpa using modNorm)

/-- For every product of distinct primes above three, one of three targets
chosen from N alone has two short, primitive representations giving a proper
divisor by gcd. Their existence does not supply a method to find the roots. -/
theorem semiprime {p q : ℕ} (pp : p.Prime) (pq : q.Prime) (ne : p≠q) (lp : 3<p) (lq : 3<q) :
    ∃ D ∈ ThreeRootTargets.menu (p*q) ThreeRootTargets.signed, ∃ r t : ZMod (p*q),
      ∃ u : Representation (p*q) D r, ∃ v : Representation (p*q) D t,
        r^2=D ∧ t^2=D ∧ r≠t ∧ r≠-t ∧
        let g := (u.x*v.y-v.x*u.y).natAbs.gcd (p*q)
        1<g ∧ g<p*q ∧ g∣p*q := by
  letI : Fact p.Prime := ⟨pp⟩
  letI : Fact q.Prime := ⟨pq⟩
  have cp := (Nat.coprime_primes pp pq).mpr ne
  have gen (i : Fin 3) : ThreeRootTargets.signed i ∈ values := by fin_cases i <;> decide
  obtain ⟨_,D,mem,sq⟩ := ThreeRootTargets.cover cp ThreeRootTargets.signed
    (fun i => value_unit lp (gen i)) (fun i => value_unit lq (gen i))
  have good := (ThreeRootTargets.signed_values (p*q)).subset mem
  obtain ⟨dp,small,ns⟩ := value_bounds good
  have positive := Nat.mul_pos pp.pos pq.pos
  letI : NeZero (p*q) := ⟨positive.ne'⟩
  have odd := (pp.odd_of_ne_two (by omega)).mul (pq.odd_of_ne_two (by omega))
  obtain ⟨r,hr⟩ := sq
  have root : r^2=D := by simpa [pow_two] using hr.symm
  obtain ⟨t,tr,diff,neg⟩ := second_root cp lp lq good r root
  obtain ⟨u⟩ := exists_representation positive odd dp small ns r root
  obtain ⟨v⟩ := exists_representation positive odd dp small ns t tr
  refine ⟨D,mem,r,t,u,v,root,tr,diff,neg,?_,?_,Nat.gcd_dvd_right ..⟩
  all_goals
    rw [gcd_intCast]
    push_cast
  · exact (split u v root tr diff neg).1
  · exact (split u v root tr diff neg).2

end PrimeFactors.ThreeTargetRepresentations
