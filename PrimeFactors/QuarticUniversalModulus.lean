import PrimeFactors.QuarticSingleModulus

/-! A single modulus decides whether the primitive quartic congruences
have points at all positive moduli. Among positive fixed multipliers of the
odd input, the exact condition for universality is divisibility by sixteen. -/
namespace PrimeFactors.QuarticUniversalModulus

open QuarticLocalClassification
open private PrimeFactors.QuarticLocalClassification.crt from PrimeFactors.QuarticLocalClassification

/-- A point at a multiple restricts to a point at each divisor. -/
theorem restrict {n m k : ℕ} (div : k∣m) (h : Point n m) : Point n k := by
  obtain ⟨a,b,d,pos,primitive,eq⟩ := h
  exact ⟨a,b,d,pos,fun p hp pk => primitive p hp (pk.trans div),eq.of_dvd div⟩

/-- The modulus 16N includes the entire obstruction at two and every
odd prime dividing N. -/
theorem sixteen {n : ℕ} (odd : Odd n) : Point n (16*n) ↔ Tests n := by
  have pos : 0<16*n := Nat.mul_pos (by decide) odd.pos
  refine ⟨fun h => ?_,fun all => all _ pos⟩
  obtain ⟨a,b,d,_,primitive,eq⟩ := restrict (dvd_mul_right 16 n) h
  have good := QuarticTwoLocalPoints.class_of_mod16 odd (primitive 2 Nat.prime_two (by decide)) eq
  refine (all_iff odd).mpr ⟨good,?_⟩
  intro p hp pn
  exact (QuarticSingleModulus.point_iff pos (Or.inr good)).mp h p hp
    (pn.trans (dvd_mul_left n 16)) pn

private theorem control_odd {m : ℕ} (odd : Odd m) : Point 2173 m := by
  apply (QuarticSingleModulus.point_iff odd.pos (Or.inl odd)).mpr
  intro p hp _ pn
  change p∣41*53 at pn
  rcases hp.dvd_mul.mp pn with left | right
  · have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 41)).mp left
    omega
  · have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 53)).mp right
    omega

/-- The same semiprime, 41·53, distinguishes every positive modulus
divisible by sixteen from those with at most three factors of two. -/
theorem control_iff {m : ℕ} (pos : 0<m) : Point 2173 m ↔ ¬16∣m := by
  constructor
  · intro h div
    obtain ⟨a,b,d,_,prim,eq⟩ := restrict div h
    exact (by decide : ¬(2173%16=1 ∨ 2173%16=5))
      (QuarticTwoLocalPoints.class_of_mod16 (by decide : Odd 2173) (prim 2 Nat.prime_two (by decide)) eq)
  · intro bad
    obtain ⟨k,t,odd,rfl⟩ := Nat.exists_eq_two_pow_mul_odd pos.ne'
    have le : k≤3 := by
      by_contra! high
      have divides : (2:ℕ)^4∣2^k := pow_dvd_pow 2 (by omega)
      exact bad (divides.trans (dvd_mul_right _ _))
    have eight : Point 2173 8 :=
      ⟨1,1,1,by decide,fun p hp _ => Or.inl hp.not_dvd_one,by decide⟩
    exact PrimeFactors.QuarticLocalClassification.crt (by positivity) odd.pos (odd.coprime_two_left.pow_left k)
      (restrict (show 2^k∣8 from pow_dvd_pow 2 le) eight) (control_odd odd)

/-- No smaller positive fixed multiplier has this property for every odd
input. The counterexample 2173 even works for every multiplier missing 16. -/
theorem universal_iff {c : ℕ} (pos : 0<c) :
    (∀ n, Odd n → (Point n (c*n) ↔ Tests n)) ↔ 16∣c := by
  constructor
  · intro uniform
    by_contra bad
    have miss : ¬16∣c*2173 := fun h => bad ((by decide : Nat.Coprime 16 2173).dvd_of_dvd_mul_right h)
    have hit := (control_iff (Nat.mul_pos pos (by decide))).mpr miss
    have all := (uniform 2173 (by decide)).mp hit
    exact (control_iff (by decide : 0<16)).mp (all 16 (by decide)) dvd_rfl
  · intro div n odd
    exact ⟨fun h => (sixteen odd).mp (restrict (Nat.mul_dvd_mul_right div n) h),
      fun all => all _ (Nat.mul_pos pos odd.pos)⟩

theorem eight_fails : Point 2173 (8*2173) ∧ ¬Tests 2173 := by
  exact ⟨(control_iff (by decide)).mpr (by decide),
    fun all => (control_iff (by decide : 0<16)).mp (all 16 (by decide)) dvd_rfl⟩

end PrimeFactors.QuarticUniversalModulus
