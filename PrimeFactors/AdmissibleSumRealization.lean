import PrimeFactors.FactorSum
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

/-! Which factor-sum residues can be realized by distinct primes in one
prescribed interval when only the product residue is fixed? The integer
product may vary. Two primes per unit class suffice for any modulus and
are also necessary for a squarefree modulus. -/

namespace PrimeFactors.AdmissibleSumRealization

/-- Every reduced residue has two distinct prime representatives in [L,H). -/
def TwoRepresentatives (m L H : ℕ) : Prop :=
  ∀ a < m, a.Coprime m → ∃ p q : ℕ, L ≤ p ∧ p < q ∧ q < H ∧
    p.Prime ∧ q.Prime ∧ p%m = a ∧ q%m = a

/-- The product and sum of a pair of actual primes have the specified residues. -/
def Realized {m : ℕ} (L H : ℕ) (r s : ZMod m) : Prop :=
  ∃ p q : ℕ, L ≤ p ∧ p < q ∧ q < H ∧ p.Prime ∧ q.Prime ∧
    ((p*q : ℕ) : ZMod m) = r ∧ ((p+q : ℕ) : ZMod m) = s

private theorem lift_two {m L H : ℕ} [NeZero m] (supply : TwoRepresentatives m L H)
    {x : ZMod m} (unit : IsUnit x) :
    ∃ p q : ℕ, L ≤ p ∧ p < q ∧ q < H ∧ p.Prime ∧ q.Prime ∧
      (p : ZMod m) = x ∧ (q : ZMod m) = x := by
  have cu : x.val.Coprime m :=
    (ZMod.isUnit_iff_coprime _ _).mp (by simpa only [ZMod.natCast_zmod_val] using unit)
  obtain ⟨p,q,lo,lt,hi,P,Q,px,qx⟩ := supply x.val x.val_lt cu
  exact ⟨p,q,lo,lt,hi,P,Q,ZMod.val_injective m (by simpa only [ZMod.val_natCast] using px),
    ZMod.val_injective m (by simpa only [ZMod.val_natCast] using qx)⟩

private theorem sort_pair {m L H p q : ℕ} {x y : ZMod m} (pLo : L≤p) (pHi : p<H)
    (qLo : L≤q) (qHi : q<H) (P : p.Prime) (Q : q.Prime) (px : (p : ZMod m) = x)
    (qy : (q : ZMod m) = y) (ne : p ≠ q) : Realized L H (x*y) (x+y) := by
  subst x y
  rcases lt_or_gt_of_ne ne with lt|gt
  · exact ⟨p,q,pLo,lt,qHi,P,Q,Nat.cast_mul ..,Nat.cast_add ..⟩
  · exact ⟨q,p,qLo,gt,pHi,Q,P,by rw [Nat.mul_comm,Nat.cast_mul],
      by rw [Nat.add_comm,Nat.cast_add]⟩

/-- A residue condition is exactly as strong as the realizable prime-pair
sum condition under the stated supply. The two local roots may coincide. -/
theorem iff_realized {m L H : ℕ} [NeZero m] (supply : TwoRepresentatives m L H)
    (r s : ZMod m) (unit : IsUnit r) : AdmissibleSum r s ↔ Realized L H r s := by
  constructor
  · rintro ⟨x,y,rfl,rfl⟩
    obtain ⟨ux,uy⟩ := (Commute.all x y).isUnit_mul_iff.mp unit
    obtain ⟨p,p',pl,lt,hi,P,_,px,_⟩ := lift_two supply ux
    obtain ⟨q,q',ql,lt',hi',Q,Q',qy,qy'⟩ := lift_two supply uy
    by_cases eq : p=q
    · exact sort_pair pl (lt.trans hi) (ql.trans lt'.le) hi' P Q' px qy' (eq ▸ lt'.ne)
    · exact sort_pair pl (lt.trans hi) ql (lt'.trans hi') P Q px qy eq
  · rintro ⟨p,q,_,_,_,_,_,rfl,rfl⟩
    exact admissibleSum_of_factor_pair m rfl

private theorem eq_zero_of_sq {m : ℕ} [NeZero m] (sf : Squarefree m) {x : ZMod m}
    (zero : x^2 = 0) : x = 0 := by
  have dv : m ∣ x.val^2 := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp
    (by simpa only [Nat.cast_pow,ZMod.natCast_zmod_val] using zero)
  simpa only [ZMod.natCast_zmod_val] using
    (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr ((sf.dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp dv)

/-- For squarefree m the double root with product a² and sum 2a forces both
prime factors into the same residue class a. This makes the supply criterion
necessary as well as sufficient. -/
theorem squarefree_iff {m L H : ℕ} [NeZero m] (sf : Squarefree m) :
    TwoRepresentatives m L H ↔
      ∀ r s : ZMod m, IsUnit r → (AdmissibleSum r s ↔ Realized L H r s) := by
  refine ⟨fun h => iff_realized h,?_⟩
  intro all a small cop
  let x : ZMod m := a
  have u : IsUnit x := (ZMod.isUnit_iff_coprime _ _).mpr cop
  have witness := (all (x*x) (x+x) (u.mul u)).mp ⟨x,x,rfl,rfl⟩
  obtain ⟨p,q,lo,lt,hi,P,Q,prod,sum⟩ := witness
  push_cast at prod sum
  have px : (p : ZMod m) = x := sub_eq_zero.mp (eq_zero_of_sq sf
    (show ((p : ZMod m)-x)^2=0 by linear_combination (p : ZMod m)*sum-prod))
  have qx : (q : ZMod m) = x := by linear_combination sum-px
  refine ⟨p,q,lo,lt,hi,P,Q,?_,?_⟩
  · simpa only [x,ZMod.val_natCast,Nat.mod_eq_of_lt small] using congrArg ZMod.val px
  · simpa only [x,ZMod.val_natCast,Nat.mod_eq_of_lt small] using congrArg ZMod.val qx

private def avoidsSmallDivisors (p : ℕ) : Bool :=
  (List.range 64).all fun d => d<2 || p%d != 0

private theorem avoidsSmallDivisors_iff {p : ℕ} (lo : 2048 ≤ p) (hi : p < 4096) :
    avoidsSmallDivisors p = true ↔ p.Prime := by
  simp only [avoidsSmallDivisors,List.all_eq_true,List.mem_range,Bool.or_eq_true,
    decide_eq_true_eq,bne_iff_ne]
  constructor
  · intro h
    refine Nat.prime_def_le_sqrt.mpr ⟨by omega,?_⟩
    intro d hd small
    have lim : p.sqrt < 64 := Nat.sqrt_lt'.mpr (by omega)
    exact (Nat.dvd_iff_mod_eq_zero).not.mpr ((h d (small.trans_lt lim)).resolve_left (by omega))
  · intro h d hd
    by_cases small : d<2
    · exact Or.inl small
    · exact Or.inr (Nat.dvd_iff_mod_eq_zero.not.mp
        ((Nat.prime_def_lt'.mp h).2 d (by omega) (by omega)))

/-- All twelve-bit primes in a specified class modulo 210. The quotient is
less than 20, so each class is checked in at most 20 candidate positions. -/
noncomputable def classroomPrimes (a : Fin 210) : Finset ℕ :=
  (((Finset.range 20).image fun k => 210*k+a.val).filter fun p =>
    2048 ≤ p ∧ p < 4096 ∧ avoidsSmallDivisors p)

theorem mem_classroomPrimes {a : Fin 210} {p : ℕ} : p ∈ classroomPrimes a ↔
    2048 ≤ p ∧ p < 4096 ∧ p.Prime ∧ p%210 = a.val := by
  simp only [classroomPrimes,Finset.mem_filter,Finset.mem_image,Finset.mem_range]
  constructor
  · rintro ⟨⟨k,_,rfl⟩,lo,hi,P⟩
    exact ⟨lo,hi,(avoidsSmallDivisors_iff lo hi).mp P,by have := a.isLt; omega⟩
  · rintro ⟨lo,hi,P,eq⟩
    exact ⟨⟨p/210,by omega,by omega⟩,lo,hi,(avoidsSmallDivisors_iff lo hi).mpr P⟩

/-- All 48 unit classes meet the supply condition with at least three
distinct primes; class 19 attains the minimum. -/
theorem classroom_counts :
    (210 : ℕ).totient = 48 ∧
      (∀ a : Fin 210, a.val.Coprime 210 → 3 ≤ (classroomPrimes a).card) ∧
      classroomPrimes 19 = {2539,2749,3169} := by decide +kernel

theorem classroom_supply : TwoRepresentatives 210 2048 4096 := by
  intro a small cop
  let r : Fin 210 := ⟨a,small⟩
  have card := classroom_counts.2.1 r cop
  obtain ⟨p,hp,q,hq,ne⟩ := Finset.one_lt_card.mp (show 1 < (classroomPrimes r).card by omega)
  obtain ⟨pl,ph,P,pa⟩ := mem_classroomPrimes.mp hp
  obtain ⟨ql,qh,Q,qa⟩ := mem_classroomPrimes.mp hq
  rcases lt_or_gt_of_ne ne with lt|gt
  · exact ⟨p,q,pl,lt,qh,P,Q,pa,qa⟩
  · exact ⟨q,p,ql,gt,ph,Q,P,qa,pa⟩

theorem classroom_realized (r s : ZMod 210) (unit : IsUnit r) :
    AdmissibleSum r s ↔ Realized 2048 4096 r s := iff_realized classroom_supply r s unit

end PrimeFactors.AdmissibleSumRealization
