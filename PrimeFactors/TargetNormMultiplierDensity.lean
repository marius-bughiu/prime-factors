import PrimeFactors.TargetNormMultiplier
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Nat.Totient
import Mathlib.SetTheory.Cardinal.Finite

/-! Multiplier sieve for a primitive norm with target D = 2. Primes 3 or 5
modulo 8 missing N exclude every multiplier they divide exactly once. -/
namespace PrimeFactors.TargetNormMultiplierDensity

/-- The allowable residues modulo p² are zero and the units. -/
def Allowed (p : ℕ) (z : ZMod (p^2)) : Prop := z = 0 ∨ IsUnit z

theorem allowed_nat_iff {p : ℕ} (hp : p.Prime) (k : ℕ) :
    Allowed p k ↔ p^2 ∣ k ∨ ¬p ∣ k := by
  rw [Allowed,ZMod.natCast_zmod_eq_zero_iff_dvd,ZMod.isUnit_iff_coprime,
    Nat.coprime_pow_right_iff (by decide : 0<2),Nat.coprime_comm,hp.coprime_iff_not_dvd]

/-- Whatever the other factors of k, valuation one at this prime rules out
a primitive solution to the target-2 norm. -/
theorem primitive_allowed {p k N X Y T : ℕ} (hp : p.Prime) (res : p%8=3 ∨ p%8=5)
    (miss : ¬p ∣ N) (norm : X^2 = k*N*Y^2+2*T^2) (primitive : X.Coprime Y) :
    Allowed p k := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [allowed_nat_iff hp]
  by_contra! bad
  have sq := TargetNormMultiplier.multiplier_square norm primitive bad.2 bad.1 miss
  have ht := (ZMod.exists_sq_eq_two_iff (p:=p) (by rintro rfl; norm_num at res)).mp
    (show IsSquare (2 : ZMod p) by simpa using sq)
  omega

/-- A complete local period has p(p−1) unit classes and the zero class. -/
theorem local_count {p : ℕ} (hp : p.Prime) :
    Nat.card {z : ZMod (p^2) // Allowed p z} = p*(p-1)+1 := by
  classical
  letI : NeZero (p^2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : Fact (1 < p^2) := ⟨one_lt_pow₀ hp.one_lt (by decide)⟩
  let units := Finset.univ.map (⟨((↑) : (ZMod (p^2))ˣ → ZMod (p^2)),Units.ext⟩)
  have mem (z : ZMod (p^2)) : z ∈ units ↔ IsUnit z := by simp [units,IsUnit]
  have kept : Finset.univ.filter (Allowed p) = insert 0 units := by ext z; simp [Allowed,mem]
  have absent : (0 : ZMod (p^2)) ∉ units := fun h => not_isUnit_zero ((mem 0).mp h)
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype,kept,Finset.card_insert_of_not_mem absent]
  simp [units,ZMod.card_units_eq_totient,Nat.totient_prime_pow_succ hp 1]

/-- The product of the squared primes is one complete public period. -/
noncomputable def period (F : Finset ℕ) := ∏ p : F, p.val^2

private theorem cop {F : Finset ℕ} (prime : ∀ p ∈ F, Nat.Prime p) :
    Pairwise (fun i j : F => (i.val^2).Coprime (j.val^2)) :=
  fun i j h => (((Nat.coprime_primes (prime i i.property) (prime j j.property)).mpr
    (fun e => h (Subtype.ext e))).pow_left 2).pow_right 2

/-- Simultaneous local gate on the residue of the multiplier. -/
def Passes (F : Finset ℕ) (prime : ∀ p ∈ F, Nat.Prime p) (z : ZMod (period F)) : Prop :=
  ∀ p : F, Allowed p.val (ZMod.prodEquivPi (fun i : F => i.val^2) (cop prime) z p)

theorem primitive_passes {F : Finset ℕ} (prime : ∀ p ∈ F, Nat.Prime p)
    {k N X Y T : ℕ} (classes : ∀ p ∈ F, p%8=3 ∨ p%8=5) (miss : ∀ p ∈ F, ¬p ∣ N)
    (norm : X^2 = k*N*Y^2+2*T^2) (primitive : X.Coprime Y) : Passes F prime k := by
  intro p
  rw [map_natCast]
  exact primitive_allowed (prime _ p.property) (classes _ p.property) (miss _ p.property) norm primitive

/-- Exact number of classes passing the finite sieve in one full period. -/
theorem period_count (F : Finset ℕ) (prime : ∀ p ∈ F, Nat.Prime p) :
    Nat.card {z : ZMod (period F) // Passes F prime z} = ∏ p : F, (p.val*(p.val-1)+1) := by
  let e : ZMod (period F) ≃ ((j : F) → ZMod (j.val^2)) := (ZMod.prodEquivPi (fun i : F => i.val^2) (cop prime)).toEquiv
  let f : {z : ZMod (period F) // Passes F prime z} ≃
      (∀ p : F, {u : ZMod (p.val^2) // Allowed p.val u}) :=
    (e.subtypeEquiv (p := Passes F prime) (q := fun t : ((j : F) → ZMod (j.val^2)) => ∀ p : F, Allowed p.val (t p)) (fun _ => Iff.rfl)).trans
      Equiv.subtypePiEquivPi
  rw [Nat.card_congr f,Nat.card_pi]
  exact Finset.prod_congr rfl fun p _ => local_count (prime p p.property)

/-- Exact fraction passing the finite sieve. True primitive multipliers form
a subset by `primitive_passes`. -/
theorem period_fraction (F : Finset ℕ) (prime : ∀ p ∈ F, Nat.Prime p) :
    (Nat.card {z : ZMod (period F) // Passes F prime z} : ℚ) / (period F : ℚ) =
      ∏ p : F, (1-((p.val:ℚ)-1)/(p.val:ℚ)^2) := by
  rw [period_count,period,Nat.cast_prod,Nat.cast_prod,← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p _
  have hp := prime _ p.property
  have nz : (p.val : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  push_cast [Nat.cast_sub hp.one_le]
  field_simp
  ring

/-- The two roots obtained in the bounded target-3 example separate by gcd. -/
theorem two_root_receipt :
    189325693069900^2 % 246180296426219 = 3 ∧
    156855619935814^2 % 246180296426219 = 3 ∧
    Nat.gcd (189325693069900-156855619935814) 246180296426219 = 15230737 := by decide

end PrimeFactors.TargetNormMultiplierDensity
