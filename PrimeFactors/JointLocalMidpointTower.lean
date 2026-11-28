import PrimeFactors.PersistentScorePrefix
import PrimeFactors.CoherentMidpointRoots
import PrimeFactors.JacobiPeriodPrimeSupport

/-! Simultaneous midpoint roots for composite moduli built from the tested primes.
The CRT permits different exponents at every prime, including zero. The common
power tower also admits one pair of factor residues compatible at every depth. -/
namespace PrimeFactors.JointLocalMidpointTower

open Finset EarlyPersistentMidpoints PersistentLocalSurvivors
open scoped Classical
set_option maxRecDepth 8192
open private PrimeFactors.JacobiPeriodPrimeSupport.squarefree_product from PrimeFactors.JacobiPeriodPrimeSupport

/-- An integer has a square root modulo a product of powers of distinct primes
exactly when it has a square root at each of those precisions. -/
theorem square_product_iff (d : ℤ) (S : Finset ℕ) (E : ℕ→ℕ)
    (prime : ∀ p∈S,p.Prime) :
    IsSquare (d:ZMod (∏ p∈S,p^(E p))) ↔ ∀ p∈S, IsSquare (d:ZMod (p^(E p))) := by
  classical
  let m (p : S) := p.val^(E p.val)
  have cop : Pairwise (fun a b : S => (m a).Coprime (m b)) := fun a b ne =>
    (((Nat.coprime_primes (prime a a.property) (prime b b.property)).mpr
      (fun eq => ne (Subtype.ext eq))).pow_left _).pow_right _
  let crt := ZMod.prodEquivPi m cop
  have per : (∏ p:S, m p)=(∏ p∈S,p^(E p)) := Finset.prod_coe_sort S (fun p => p^E p)
  rw [←per]
  constructor
  · rintro ⟨r,root⟩ p hp
    have proj := congrFun (congrArg crt root) (⟨p,hp⟩:S)
    exact ⟨crt r ⟨p,hp⟩,by simpa only [map_intCast,map_mul,Pi.intCast_apply,Pi.mul_apply] using proj⟩
  · intro all
    choose r root using (fun p : S => all p p.property)
    refine ⟨crt.symm r,crt.injective ?_⟩
    rw [map_intCast,map_mul,crt.apply_symm_apply]
    exact funext root

private theorem primes (p : ℕ) (hp : p∈smallPrimes 643) : p.Prime := (mem_filter.mp hp).2

noncomputable def K := ∏ p∈smallPrimes 643,p

theorem K_squarefree : Squarefree K := PrimeFactors.JacobiPeriodPrimeSupport.squarefree_product _ primes
instance : NeZero K := ⟨K_squarefree.ne_zero⟩
theorem K_primes : K.primeFactors=smallPrimes 643 := Nat.primeFactors_prod primes

attribute [local irreducible] K smallPrimes

/-- One pair of residue factors exists for the whole selected modulus. -/
theorem mixed {n h : ℕ} (ok : Passes n h) (S : Finset ℕ) (sub : S⊆smallPrimes 643) (E : ℕ→ℕ) :
    let m := ∏ p∈S,p^(E p)
    IsSquare (((h:ℤ)^2-n:ℤ):ZMod m) ∧ AdmissibleSum (n:ZMod m) (2*(h:ZMod m)) := by
  dsimp only
  have root := (square_product_iff ((h:ℤ)^2-n) S E (fun p hp => primes p (sub hp))).mpr
    (fun p hp => ok p (sub hp) (E p))
  exact ⟨root,(LocalMidpointLanes.midpoint_iff _ _).mpr
    (by simpa only [Int.cast_sub,Int.cast_pow,Int.cast_natCast] using root)⟩

/-- Arbitrary positive moduli with no prime divisors outside the tested set. -/
theorem supported {n h m : ℕ} (ok : Passes n h) (pos : 0<m) (support : m.primeFactors⊆smallPrimes 643) :
    IsSquare (((h:ℤ)^2-n:ℤ):ZMod m) ∧ AdmissibleSum (n:ZMod m) (2*(h:ZMod m)) := by
  have fac : (∏ p∈m.primeFactors,p^(m.factorization p))=m := Nat.factorization_prod_pow_eq_self pos.ne'
  let Q (r : ℕ) := IsSquare (((h:ℤ)^2-n:ℤ):ZMod r) ∧ AdmissibleSum (n:ZMod r) (2*(h:ZMod r))
  exact (congrArg Q fac).mp (mixed ok m.primeFactors support m.factorization)

theorem joint_squares {n h : ℕ} (ok : Passes n h) (e : ℕ) :
    IsSquare (((h:ℤ)^2-n:ℤ):ZMod (K^e)) := by
  have per : (∏ p∈smallPrimes 643,p^e)=K^e := by
    unfold K; exact Finset.prod_pow _ _ (fun p => p)
  exact (congrArg (fun r : ℕ => IsSquare (((h:ℤ)^2-n:ℤ):ZMod r)) per).mp
    (mixed ok (smallPrimes 643) (fun _ h => h) (fun _ => e)).1

/-- The greatest requested exponent supplies one common power of K above the
entire mixed modulus. For an empty set this common power is one. -/
theorem mixed_dvd_power (S : Finset ℕ) (sub : S⊆smallPrimes 643) (E : ℕ→ℕ) :
    (∏ p∈S,p^(E p)) ∣ K^(S.sup E) := by
  have up := prod_dvd_prod_of_dvd (fun p => p^(E p)) (fun p => p^(S.sup E))
    (fun p hp => pow_dvd_pow p (Finset.le_sup hp))
  rw [prod_pow] at up
  have incl : (∏ p∈S,p)∣K := by
    unfold K; exact prod_dvd_prod_of_subset _ _ (fun p => p) sub
  exact up.trans (pow_dvd_pow_of_dvd incl _)

/-- Reducing a compatible tower component to a divisor of two levels gives
the same residue from either level. This applies to both ordered factors. -/
theorem projection_agrees {b m : ℕ} {x : ∀ e : ℕ, ZMod (b^e)} (coherent : CoherentMidpointRoots.Compatible x)
    {i j : ℕ} (hi : m∣b^i) (hj : m∣b^j) :
    ZMod.castHom hi (ZMod m) (x i)=ZMod.castHom hj (ZMod m) (x j) := by
  have ordered {s t : ℕ} (hs : m∣b^s) (ht : m∣b^t) (le : s≤t) :
      ZMod.castHom hs (ZMod m) (x s)=ZMod.castHom ht (ZMod m) (x t) := by
    rw [←coherent le]
    exact RingHom.congr_fun (ZMod.castHom_comp hs (pow_dvd_pow b le)) (x t)
  rcases le_total i j with le|le
  · exact ordered hi hj le
  · exact (ordered hj hi le).symm

/-- Every depth and prime contributes to the same two compatible sequences. -/
theorem joint_tower {n h : ℕ} (ok : Passes n h) : CoherentMidpointRoots.HasFactors K n h :=
  (CoherentMidpointRoots.factor_tower K n h).mp (joint_squares ok)

/-- Requiring one compatible ordered factor pair for every power of K gives
exactly the original midpoint test through the individual prime powers. -/
theorem tower_iff {n h : ℕ} : CoherentMidpointRoots.HasFactors K n h ↔ Passes n h := by
  refine ⟨?_,joint_tower⟩
  intro towers p hp e
  have divisor : p∣K := by unfold K; exact dvd_prod_of_mem (fun q => q) hp
  have root := (CoherentMidpointRoots.factor_tower K n h).mpr towers e
  have reduced := root.map (ZMod.castHom (pow_dvd_pow_of_dvd divisor e) (ZMod (p^e)))
  simpa only [map_intCast] using reduced

private theorem wrong_midpoint {v : ℕ×ℕ} {t : ℕ} (inside : t∈PersistentScorePrefix.wrong v) :
    t=2*(t/2) ∧ Passes (v.1*v.2) (t/2) := by
  obtain ⟨_,_,_,even,ok,_⟩ := mem_filter.mp inside
  exact ⟨even,ok⟩

theorem wrong_squares {v : ℕ×ℕ} {t : ℕ} (inside : t∈PersistentScorePrefix.wrong v) (e : ℕ) :
    IsSquare ((((t/2:ℕ):ℤ)^2-(v.1*v.2:ℕ):ℤ):ZMod (K^e)) :=
  joint_squares (wrong_midpoint inside).2 e

theorem wrong_tower {v : ℕ×ℕ} {t : ℕ} (inside : t∈PersistentScorePrefix.wrong v) :
    CoherentMidpointRoots.HasFactors K (v.1*v.2:ℕ) (t/2:ℕ) :=
  joint_tower (wrong_midpoint inside).2

theorem wrong_factors {v : ℕ×ℕ} {t m : ℕ} (inside : t∈PersistentScorePrefix.wrong v)
    (pos : 0<m) (support : m.primeFactors⊆smallPrimes 643) :
    AdmissibleSum ((v.1*v.2:ℕ):ZMod m) (t:ZMod m) := by
  obtain ⟨even,ok⟩ := wrong_midpoint inside
  have pair := (supported ok pos support).2
  have sum : ((2*(t/2):ℕ):ZMod m)=(t:ZMod m) := congrArg (fun a : ℕ => (a:ZMod m)) even.symm
  rw [Nat.cast_mul,Nat.cast_ofNat] at sum
  exact sum ▸ pair

end PrimeFactors.JointLocalMidpointTower
