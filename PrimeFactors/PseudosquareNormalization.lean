import PrimeFactors.MaskedSquareWitness
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic

/-! Pseudosquare cutoffs concern nonzero squares at every tested odd prime.
To apply one to an arbitrary positive integer, remove every power of the
listed primes and of two, keeping the parity of those exponents. -/

namespace PrimeFactors.PseudosquareNormalization

/-- A nonzero square residue, with an explicitly bounded representative. -/
def UnitSquare (p u : ℕ) : Prop := ∃ a : Fin p, a.val ≠ 0 ∧ a.val^2 % p = u % p

noncomputable instance (p u : ℕ) : Decidable (UnitSquare p u) := by unfold UnitSquare; infer_instance

theorem unitSquare_iff {p u : ℕ} (prime : p.Prime) :
    UnitSquare p u ↔ ¬p ∣ u ∧ IsSquare (u : ZMod p) := by
  letI : Fact p.Prime := ⟨prime⟩
  constructor
  · rintro ⟨a,ne,eq⟩
    have cast := (ZMod.natCast_eq_natCast_iff' (a.val^2) u p).mpr eq
    push_cast at cast
    have az : (a.val : ZMod p) ≠ 0 := fun h => ne (Nat.eq_zero_of_dvd_of_lt
      ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp h) a.isLt)
    exact ⟨fun h => (pow_ne_zero 2 az) (cast.trans ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mpr h)),
      (isSquare_iff_exists_sq _).mpr ⟨a.val,cast.symm⟩⟩
  · rintro ⟨notdiv,square⟩
    obtain ⟨x,eq⟩ := square.exists_sq
    have ux : (x.val : ZMod p) = x := ZMod.natCast_zmod_val x
    have cast : ((x.val^2 : ℕ):ZMod p) = (u:ZMod p) := by push_cast; rw [ux,←eq]
    refine ⟨⟨x.val,x.val_lt⟩,?_,(ZMod.natCast_eq_natCast_iff' ..).mp cast⟩
    intro zero
    change x.val = 0 at zero
    have hx : x = 0 := ux.symm.trans (by rw [zero,Nat.cast_zero])
    exact notdiv ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp (by simpa [hx] using eq))

/-- At an odd prime this is exactly a positive Legendre/Jacobi value. -/
theorem unitSquare_iff_jacobi {p u : ℕ} (prime : p.Prime) :
    UnitSquare p u ↔ jacobiSym (u : ℤ) p = 1 := by
  letI : Fact p.Prime := ⟨prime⟩
  rw [unitSquare_iff prime]
  constructor
  · rintro ⟨nd,square⟩
    have cop := (prime.coprime_iff_not_dvd.mpr nd).symm
    have signs := jacobiSym.eq_one_or_neg_one (by simpa using cop.gcd_eq_one : (u:ℤ).gcd p=1)
    exact signs.resolve_right (fun h => (ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mp h)
      (by simpa using square))
  · intro h
    refine ⟨?_,by simpa using ZMod.isSquare_of_jacobiSym_eq_one h⟩
    intro dv
    have bad : (u:ℤ).gcd p ≠ 1 := by
      simp only [Int.gcd_natCast_natCast,Nat.gcd_eq_right dv]
      exact prime.ne_one
    have := jacobiSym.eq_zero_iff.mpr ⟨prime.ne_zero,bad⟩
    omega

/-- The classical pseudosquare tests include the two-adic unit condition. -/
def Passes (tests : List ℕ) (u : ℕ) : Prop := u%8 = 1 ∧ ∀ p ∈ tests, UnitSquare p u

noncomputable instance (tests : List ℕ) (u : ℕ) : Decidable (Passes tests u) := by unfold Passes; infer_instance

/-- A cutoff excludes all smaller positive nonsquares and is attained at its endpoint. -/
structure Cutoff (tests : List ℕ) (L : ℕ) : Prop where
  below : ∀ u, 0 < u → u < L → Passes tests u → IsSquare u
  positive : 0 < L
  nonsquare : ¬ IsSquare L
  endpoint : Passes tests L

/-- The cofactor after removing the power of the specified prime. -/
noncomputable def away (p D : ℕ) : ℕ := D / p^D.factorization p

noncomputable def residual : List ℕ → ℕ → ℕ
  | [], D => D
  | p::ps, D => residual ps (away p D)

noncomputable def evenExponents : List ℕ → ℕ → Prop
  | [], _ => True
  | p::ps, D => Even (D.factorization p) ∧ evenExponents ps (away p D)

private theorem remove_square {k u : ℕ} (hk : 0<k) : IsSquare (k^2*u) ↔ IsSquare u := by
  constructor
  · intro h
    obtain ⟨x,hx⟩ := h.exists_sq
    obtain ⟨q,rfl⟩ := (Nat.pow_dvd_pow_iff (by decide : 2≠0)).mp (show k^2 ∣ x^2 from ⟨u,hx.symm⟩)
    rw [mul_pow] at hx
    exact (isSquare_iff_exists_sq _).mpr ⟨q,Nat.eq_of_mul_eq_mul_left (pow_pos hk _) hx⟩
  · exact fun h => (IsSquare.sq _).mul h

private theorem one_prime {p D : ℕ} (prime : p.Prime) :
    IsSquare D ↔ Even (D.factorization p) ∧ IsSquare (away p D) := by
  have restore (even : Even (D.factorization p)) : IsSquare D ↔ IsSquare (away p D) := by
    obtain ⟨a,ha⟩ := even
    have decomp := Nat.ordProj_mul_ordCompl_eq_self D p
    change p^D.factorization p * away p D = D at decomp
    rw [ha,←Nat.mul_two, pow_mul] at decomp
    exact (congrArg IsSquare decomp.symm).to_iff.trans (remove_square (pow_pos prime.pos a))
  constructor
  · intro h
    have even : Even (D.factorization p) := by
      obtain ⟨x,rfl⟩ := h.exists_sq
      rw [Nat.factorization_pow]
      exact ⟨x.factorization p,by simp [two_smul]⟩
    exact ⟨even,(restore even).mp h⟩
  · rintro ⟨even,h⟩
    exact (restore even).mpr h

private theorem residual_dvd (ps : List ℕ) (D : ℕ) : residual ps D ∣ D := by
  induction ps generalizing D with
  | nil => exact dvd_rfl
  | cons p ps ih =>
    apply (ih (away p D)).trans
    exact ⟨p^D.factorization p,(Nat.ordProj_mul_ordCompl_eq_self D p).symm.trans (Nat.mul_comm ..)⟩

theorem residual_properties (ps : List ℕ) {D : ℕ} (pos : 0<D) (primes : ∀p∈ps, Nat.Prime p) :
    0 < residual ps D ∧ ∀p∈ps, ¬p ∣ residual ps D := by
  induction ps generalizing D with
  | nil => simpa [residual]
  | cons p ps ih =>
    have hp := primes p (by simp)
    obtain ⟨good,clean⟩ := ih (Nat.ordCompl_pos p pos.ne') (fun q h => primes q (by simp [h]))
    refine ⟨good,?_⟩
    intro q h
    rcases List.mem_cons.mp h with rfl | h
    · exact fun dv => Nat.not_dvd_ordCompl hp pos.ne' (dv.trans (residual_dvd ps (away _ D)))
    · exact clean q h

theorem stripping (ps : List ℕ) (D : ℕ) (primes : ∀p∈ps,Nat.Prime p) :
    IsSquare D ↔ evenExponents ps D ∧ IsSquare (residual ps D) := by
  induction ps generalizing D with
  | nil => simp [residual,evenExponents]
  | cons p ps ih =>
    rw [one_prime (primes p (by simp)),ih (away p D) (fun q h => primes q (by simp [h]))]
    simp [residual,evenExponents,and_assoc]

private theorem square_passes {tests : List ℕ} {u : ℕ} (primes : ∀p∈tests,Nat.Prime p)
    (clean : ∀p∈2::tests, ¬p∣u) (sq : IsSquare u) : Passes tests u := by
  obtain ⟨x,rfl⟩ := sq.exists_sq
  constructor
  · have h := clean 2 (by simp)
    have odd : x%2=1 := by
      by_contra! bad
      apply h
      exact (Nat.dvd_of_mod_eq_zero (by omega : x%2=0)).trans (dvd_pow_self _ (by decide : 2≠0))
    rw [Nat.pow_mod]
    have unit : x%8=1 ∨ x%8=3 ∨ x%8=5 ∨ x%8=7 := by omega
    rcases unit with h|h|h|h <;> rw [h]
  · intro p hp
    apply (unitSquare_iff (primes p hp)).mpr
    exact ⟨clean p (by simp [hp]), by push_cast; exact IsSquare.sq _⟩

/-- Exact square recognition below a classical cutoff, with arbitrary factors at the
tested primes accepted at even valuation when their remaining unit is square. -/
theorem normalized_iff {tests : List ℕ} {D L : ℕ} (cutoff : Cutoff tests L) (pos : 0<D)
    (primes : ∀p∈tests,Nat.Prime p) (size : residual (2::tests) D < L) :
    IsSquare D ↔ evenExponents (2::tests) D ∧ Passes tests (residual (2::tests) D) := by
  have all : ∀p∈2::tests,Nat.Prime p := List.forall_mem_cons.mpr ⟨Nat.prime_two,primes⟩
  obtain ⟨up,clean⟩ := residual_properties _ pos all
  rw [stripping _ D all]
  exact and_congr_right (fun _ => ⟨square_passes primes clean,cutoff.below _ up size⟩)

private theorem clean_id (ps : List ℕ) (D : ℕ) (clean : ∀ p ∈ ps, ¬p ∣ D) :
    residual ps D = D ∧ evenExponents ps D := by
  induction ps with
  | nil => simp [residual,evenExponents]
  | cons p ps ih =>
    have zero := Nat.factorization_eq_zero_of_not_dvd (clean p (by simp))
    have rest := ih (fun q h => clean q (by simp [h]))
    simpa [residual,evenExponents,away,zero] using rest

/-- When all removed exponents are even, their product is a square scale. -/
theorem even_scale (ps : List ℕ) {D : ℕ} (pos : 0 < D) (primes : ∀p∈ps,Nat.Prime p)
    (even : evenExponents ps D) : ∃ x : ℕ, 0<x ∧ D = residual ps D*x^2 := by
  induction ps generalizing D with
  | nil => exact ⟨1,by decide,by simp [residual]⟩
  | cons p ps ih =>
    obtain ⟨⟨j,hj⟩,he⟩ := even
    have hp := primes p (by simp)
    obtain ⟨x,xp,eq⟩ := ih (Nat.ordCompl_pos p pos.ne') (fun q h => primes q (by simp [h])) he
    refine ⟨p^j*x,mul_pos (pow_pos hp.pos _) xp,?_⟩
    have factors := (Nat.ordProj_mul_ordCompl_eq_self D p).symm
    change D = p^D.factorization p * away p D at factors
    calc
      D = p^(j+j) * away p D := by rw [←hj]; exact factors
      _ = p^(j+j) * (residual ps (away p D)*x^2) := congrArg (p^(j+j) * ·) eq
      _ = residual (p::ps) D * (p^j*x)^2 := by
        change _ = residual ps (away p D) * (p^j*x)^2
        rw [pow_add]
        ring

/-- Removing a square factor preserves any residual prime-power test after
raising the original modulus by exactly its valuation in the candidate. -/
theorem depth_iff {D u x p : ℕ} (up : 0<u) (xp : 0<x) (eq : D=u*x^2)
    (prime : p.Prime) (clean : ¬p∣u) (k : ℕ) :
    IsSquare ((D:ℕ):ZMod (p^(D.factorization p+k))) ↔ IsSquare ((u:ℕ):ZMod (p^k)) := by
  have val : D.factorization p = 2*x.factorization p := by
    rw [eq,Nat.factorization_mul up.ne' (pow_pos xp _).ne',Nat.factorization_pow]
    simp [Nat.factorization_eq_zero_of_not_dvd clean,two_smul,two_mul]
  have dot := MaskedSquareWitness.at_depth (a:=x.factorization p) prime.ne_zero
    (Nat.coprime_ordCompl prime xp.ne').symm k (u:ℤ)
  rw [Nat.ordProj_mul_ordCompl_eq_self] at dot
  rw [val,eq]
  simpa only [Int.cast_mul,Int.cast_natCast,Int.cast_pow,Nat.cast_mul,Nat.cast_pow] using dot

/-- A prime-power form of the same cutoff test. The input valuation at two
requires three additional bits, and each odd-prime unit test requires one
additional copy of its prime. -/
theorem prime_power_iff {tests : List ℕ} {D L : ℕ} (cutoff : Cutoff tests L) (pos : 0<D)
    (primes : ∀p∈tests,Nat.Prime p) (size : residual (2::tests) D < L) :
    IsSquare D ↔ evenExponents (2::tests) D ∧ IsSquare ((D:ℕ):ZMod (2^(D.factorization 2+3))) ∧
      ∀ p∈tests, IsSquare ((D:ℕ):ZMod (p^(D.factorization p+1))) := by
  let u := residual (2::tests) D
  have all := List.forall_mem_cons.mpr ⟨Nat.prime_two,primes⟩
  obtain ⟨up,clean⟩ := residual_properties _ pos all
  constructor
  · intro sq
    have lift (m : ℕ) : IsSquare ((D:ℕ):ZMod m) := sq.map (Nat.castRingHom (ZMod m))
    exact ⟨((normalized_iff cutoff pos primes size).mp sq).1,lift _,fun _ _ => lift _⟩
  · rintro ⟨even,two,odd⟩
    obtain ⟨x,xp,eq⟩ := even_scale _ pos all even
    apply (normalized_iff cutoff pos primes size).mpr
    refine ⟨even,?_,?_⟩
    · have twoclean := clean 2 (by simp)
      have local8 := (depth_iff up xp eq Nat.prime_two twoclean 3).mp two
      have table : ∀ z : ZMod 8, IsSquare z → z.val % 2 = 1 → z.val = 1 := by decide +kernel
      have res := table (u : ZMod 8) local8
      rw [ZMod.val_natCast] at res
      change ¬2∣u at twoclean
      exact res (by omega)
    · intro p hp
      have nd := clean p (by simp [hp])
      have unit := (depth_iff up xp eq (primes p hp) nd 1).mp (odd p hp)
      exact (unitSquare_iff (primes p hp)).mpr ⟨nd,(congrArg (fun m : ℕ => IsSquare ((u:ℕ):ZMod m)) (pow_one p)).mp unit⟩

/-- At the cutoff itself the residual equals the cutoff, every check passes,
and the original number is nonsquare. The strict inequality is necessary. -/
theorem strict_endpoint {tests : List ℕ} {L : ℕ} (cutoff : Cutoff tests L)
    (primes : ∀p∈tests,Nat.Prime p) :
    residual (2::tests) L = L ∧ evenExponents (2::tests) L ∧
      Passes tests (residual (2::tests) L) ∧ ¬IsSquare L := by
  have clean : ∀ p∈2::tests, ¬p∣L := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · have := cutoff.endpoint.1
      omega
    · exact ((unitSquare_iff (primes p hp)).mp (cutoff.endpoint.2 p hp)).1
  obtain ⟨same,e⟩ := clean_id _ L clean
  exact ⟨same,e,by rw [same]; exact cutoff.endpoint,cutoff.nonsquare⟩

end PrimeFactors.PseudosquareNormalization
