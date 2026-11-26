import Mathlib.NumberTheory.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-! Transport local geometric matches from residues to prime powers by an
exponent formed only from the public product. The basic congruence is the
classical power-lifting lemma used to construct Witt vectors. -/

namespace PrimeFactors.GeometricPrincipalLift

/-- For an odd balanced pair, neither prime can divide the other's
predecessor. The only possible smaller-prime multiple would give q=p+1. -/
theorem balanced_coprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (po : Odd p) (qo : Odd q) (lt : p<q) (balanced : q≤2*p) :
    (p*q).Coprime (p-1) ∧ (p*q).Coprime (q-1) := by
  have ps := hp.two_le
  have qs := hq.two_le
  have no (a b : ℕ) (positive : 0<b) (small : b<a) : ¬ a∣b :=
    Nat.not_dvd_of_pos_of_lt positive small
  have cross : ¬p∣q-1 := by
    intro d
    have e := Nat.eq_of_dvd_of_lt_two_mul (by omega : q-1≠0) d (by omega)
    have op := Nat.odd_iff.mp po
    have oq := Nat.odd_iff.mp qo
    omega
  rw [Nat.coprime_mul_iff_left,Nat.coprime_mul_iff_left]
  exact ⟨⟨hp.coprime_iff_not_dvd.mpr (no _ _ (by omega) (by omega)),
    hq.coprime_iff_not_dvd.mpr (no _ _ (by omega) (by omega))⟩,
    ⟨hp.coprime_iff_not_dvd.mpr cross,hq.coprime_iff_not_dvd.mpr (no _ _ (by omega) (by omega))⟩⟩

/-- Every positive precision is gained by a public power. The forward
divisibility itself works even if p is composite or either input is a nonunit. -/
theorem lift {p n : ℕ} (div : p∣n) (r : ℕ) {a b : ℤ} (eq : a ≡ b [ZMOD (p:ℤ)]) :
    a^(n^r) ≡ b^(n^r) [ZMOD (p:ℤ)^(r+1)] := by
  obtain ⟨q, rfl⟩ := div
  have step : a^(p^r) ≡ b^(p^r) [ZMOD (p:ℤ)^(r+1)] :=
    Int.modEq_iff_dvd.mpr (dvd_sub_pow_of_dvd_sub eq.dvd r)
  simpa only [mul_pow,pow_mul] using step.pow (q^r)

/-- All local orders survive, including those smaller than p−1. -/
theorem order {p n : ℕ} (hp : p.Prime) (cop : n.Coprime (p-1))
    (r : ℕ) (g : (ZMod p)ˣ) : orderOf (g^(n^r))=orderOf g := by
  letI : Fact p.Prime := ⟨hp⟩
  have divides : orderOf g ∣ p-1 := (Nat.prime_iff_card_units p).mp hp ▸ orderOf_dvd_card
  exact ((cop.of_dvd_right divides).symm.pow_right r).orderOf_pow

private theorem power_injective {p n : ℕ} (hp : p.Prime) (pos : 0<n)
    (cop : n.Coprime (p-1)) (r : ℕ) :
    Function.Injective (fun a : ZMod p => a^(n^r)) := by
  letI : Fact p.Prime := ⟨hp⟩
  have size : Nat.card (ZMod p)ˣ=p-1 := (Nat.card_eq_fintype_card).trans ((Nat.prime_iff_card_units p).mp hp)
  have c : (Nat.card (ZMod p)ˣ).Coprime (n^r) := size ▸ cop.symm.pow_right r
  have pn := pow_pos pos r
  intro a b eq
  change a^(n^r)=b^(n^r) at eq
  by_cases za : a=0
  · rw [za,zero_pow pn.ne'] at eq
    exact za.trans (pow_eq_zero eq.symm).symm
  by_cases zb : b=0
  · rw [zb,zero_pow pn.ne'] at eq
    exact (za (pow_eq_zero eq)).elim
  have h : (Units.mk0 a za)^(n^r)=(Units.mk0 b zb)^(n^r) := Units.ext eq
  exact congrArg Units.val (c.pow_left_bijective.1 h)

/-- The transported p-adic equality is equivalent to the original equality of
residues, so it introduces no new matching index. -/
theorem lift_iff {p n : ℕ} (hp : p.Prime) (pos : 0<n) (div : p∣n)
    (cop : n.Coprime (p-1)) (r : ℕ) (a b : ℤ) :
    a^(n^r) ≡ b^(n^r) [ZMOD (p:ℤ)^(r+1)] ↔ a ≡ b [ZMOD (p:ℤ)] := by
  refine ⟨fun high => ?_,lift div r⟩
  have de : (p:ℤ)∣(p:ℤ)^(r+1) := by rw [pow_succ]; exact dvd_mul_left _ _
  have low := high.of_dvd de
  have eq := (ZMod.intCast_eq_intCast_iff _ _ p).mpr low
  rw [Int.cast_pow,Int.cast_pow] at eq
  exact (ZMod.intCast_eq_intCast_iff _ _ p).mp (power_injective hp pos cop r eq)

/-- Powers G^j and Y where G=g^(N^r) and Y=G^E. Set E=N+1−L for the
actual target. The conclusion applies independently to every index. -/
theorem geometric {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (po : Odd p) (qo : Odd q)
    (lt : p<q) (balanced : q≤2*p) (r j E : ℕ) (g : ℤ) :
    let G := g^((p*q)^r)
    ((G^j ≡ G^E [ZMOD (p:ℤ)^(r+1)]) ↔ g^j ≡ g^E [ZMOD (p:ℤ)]) ∧
    ((G^j ≡ G^E [ZMOD (q:ℤ)^(r+1)]) ↔ g^j ≡ g^E [ZMOD (q:ℤ)]) := by
  dsimp only
  have cp := balanced_coprime hp hq po qo lt balanced
  have pos := Nat.mul_pos hp.pos hq.pos
  have swap (i : ℕ) : (g^((p*q)^r))^i = (g^i)^((p*q)^r) := by rw [←pow_mul,←pow_mul,mul_comm]
  rw [swap j,swap E]
  exact ⟨lift_iff hp pos (dvd_mul_right p q) cp.1 r _ _,lift_iff hq pos (dvd_mul_left q p) cp.2 r _ _⟩

end PrimeFactors.GeometricPrincipalLift
