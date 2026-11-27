import PrimeFactors.JacobiMomentPeriod
import PrimeFactors.JacobiPeriodCount

/-! Period tests common to all starting offsets in a strided sequence of
positive even Jacobi moments. The least period and an arbitrary multiple
have different consequences for the factor sum. -/
namespace PrimeFactors.JacobiPeriodProbe

open JacobiMomentPeriod

/-- Each starting position gives a sequence sampled at the same stride. -/
def AllOffsets {α : Type*} (u : ℕ → α) (s t : ℕ) : Prop :=
  ∀ j, Function.Periodic (fun k => u (j + s*k)) t

theorem allOffsets_iff {α : Type*} (u : ℕ → α) (s t : ℕ) :
    AllOffsets u s t ↔ Function.Periodic u (s*t) := by
  constructor
  · intro h j
    simpa using h j 0
  · intro h j k
    simpa only [Nat.mul_add, Nat.add_assoc] using h (j+s*k)

/-- A common shift at any stride is equivalent to a power identity on all units. -/
theorem allOffsets_iff_units {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (hp : 7 ≤ p) (hq : 7 ≤ q) (s t : ℕ) :
    AllOffsets (completeEven (p*q)) s t ↔ ∀ x : (ZMod (p*q))ˣ, x^(2*(s*t)) = 1 := by
  rw [allOffsets_iff, composite_iff cop (by omega) (by omega),
    ← Monoid.exponent_dvd_iff_forall_pow_eq_one, ← unit_exponent cop hp hq,
    Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)]

private theorem twice_stride {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : 7 ≤ p) (hq : 7 ≤ q) : 2*((p*q-1)/2) = p*q-1 := by
  have ho := ((Fact.out : p.Prime).odd_of_ne_two (by omega)).mul
    ((Fact.out : q.Prime).odd_of_ne_two (by omega))
  obtain ⟨j,hj⟩ := ho
  omega

/-- At the stride obtained by halving N−1, testing a unit requires just N and the guess. -/
theorem public_test {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (hp : 7 ≤ p) (hq : 7 ≤ q) (t : ℕ) :
    AllOffsets (completeEven (p*q)) ((p*q-1)/2) t ↔
      ∀ x : (ZMod (p*q))ˣ, x^((p*q-1)*t) = 1 := by
  rw [allOffsets_iff_units cop hp hq, ← Nat.mul_assoc, twice_stride hp hq]

/-- A single failed power check also rejects every divisor of the proposed shift. -/
theorem rejects_divisors {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (hp : 7 ≤ p) (hq : 7 ≤ q) {d t : ℕ} (hd : d ∣ t)
    (x : (ZMod (p*q))ˣ) (fail : x^((p*q-1)*t) ≠ 1) :
    ¬ AllOffsets (completeEven (p*q)) ((p*q-1)/2) d := by
  intro works
  obtain ⟨k,rfl⟩ := hd
  apply fail
  rw [← Nat.mul_assoc, pow_mul, (public_test cop hp hq d).mp works x, one_pow]

/-- A least-prime-outside-subgroup bound makes a fixed list of small prime
bases sufficient for every multiplier. The analytic bound is a hypothesis. -/
theorem small_prime_test {p q B : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (hp : 7 ≤ p) (hq : 7 ≤ q) (outside : SmallPrimeOutside (p*q) B)
    (t : ℕ) : AllOffsets (completeEven (p*q)) ((p*q-1)/2) t ↔
      ∀ a : ℕ, a.Prime → a ≤ B → ∀ ha : a.Coprime (p*q),
        (ZMod.unitOfCoprime a ha)^((p*q-1)*t) = 1 := by
  rw [public_test cop hp hq]
  constructor
  · exact fun all _ _ _ _ => all _
  · intro small x
    let H := (powMonoidHom ((p*q-1)*t) : (ZMod (p*q))ˣ →* (ZMod (p*q))ˣ).ker
    by_contra hx
    have proper : H ≠ ⊤ := fun top => hx (show x ∈ H from top ▸ Subgroup.mem_top x)
    obtain ⟨a,prime,bounded,ha,miss⟩ := outside H proper
    exact miss (small a prime bounded ha)

private theorem twice_local {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p) :
    2*localPeriod p = p-1 := by
  obtain ⟨k,hk⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  simp only [localPeriod, if_neg (show p ≠ 5 by omega)]
  omega

/-- Write p−1 and q−1 as g times coprime positive integers a and b.
Then exactly the multiples of a*b work from every offset. -/
theorem exact_period {p q g a b : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (hp : 7 ≤ p) (hq : 7 ≤ q)
    (hg : 0 < g) (pa : p = g*a+1) (qb : q = g*b+1) (ab : a.Coprime b) (t : ℕ) :
    AllOffsets (completeEven (p*q)) ((p*q-1)/2) t ↔ a*b ∣ t := by
  let k := a+b+g*(a*b)
  have expand : p*q-1 = g*k := by
    have h : p*q = g*k+1 := by rw [pa,qb]; dsimp [k]; ring
    omega
  have rel : (a*b).Coprime k := by
    apply (Nat.coprime_add_mul_right_right (a*b) (a+b) g).mpr
    exact ((Nat.coprime_self_add_right).mpr ab).mul ((Nat.coprime_add_self_right).mpr ab.symm)
  rw [public_test cop hp hq, ← Monoid.exponent_dvd_iff_forall_pow_eq_one,
    ← unit_exponent cop hp hq, ← Nat.lcm_mul_left, twice_local hp, twice_local hq,
    show p-1 = g*a by omega, show q-1 = g*b by omega,
    Nat.lcm_mul_left, ab.lcm_eq_mul, expand, Nat.mul_assoc, Nat.mul_dvd_mul_iff_left hg]
  exact ⟨rel.dvd_of_dvd_mul_left, fun h => dvd_mul_of_dvd_right h _⟩

/-- In terms of the prime factors themselves, the least all-offset period
is the product of their two reduced predecessors. -/
theorem canonical_period {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (hp : 7 ≤ p) (hq : 7 ≤ q) (t : ℕ) :
    AllOffsets (completeEven (p*q)) ((p*q-1)/2) t ↔
      JacobiPeriodCount.residualProduct p q ∣ t := by
  let g := (p-1).gcd (q-1)
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  have pa : g*((p-1)/g) = p-1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have qb : g*((q-1)/g) = q-1 := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  exact exact_period cop hp hq hg (by omega : p = g*((p-1)/g)+1)
    (by omega : q = g*((q-1)/g)+1) (Nat.coprime_div_gcd_div_gcd hg) t

/-- An exact period determines g by rounding just once. The strictly ordered
positive reduced predecessors rule out the degenerate pair a=b=1. -/
theorem sum_from_period {p q g a b : ℕ} (ha : 0 < a) (hab : a < b)
    (pa : p = g*a+1) (qb : q = g*b+1) :
    let R := a*b
    ((p*q)/R).sqrt = g ∧ p*q+1-((p*q)/R).sqrt^2*R = p+q := by
  dsimp only
  have hR := Nat.mul_pos ha (ha.trans hab)
  obtain ⟨u,hu⟩ := Nat.exists_eq_add_of_le (show 1 ≤ a by omega)
  obtain ⟨v,hv⟩ := Nat.exists_eq_add_of_le (show a+1 ≤ b by omega)
  have lower : g^2*(a*b) ≤ p*q := by rw [pa,qb]; nlinarith
  have upper : p*q < (g+1)^2*(a*b) := by
    rw [pa,qb,hv,hu]
    nlinarith only [Nat.zero_le u, Nat.zero_le v, Nat.zero_le g, Nat.zero_le (u*v),
      Nat.zero_le (u^2), Nat.zero_le (g*u), Nat.zero_le (g*v),
      Nat.zero_le (g*u*v), Nat.zero_le (g*u^2)]
  have sqrt_g : ((p*q)/(a*b)).sqrt = g := by
    apply Nat.le_antisymm
    · have h := Nat.sqrt_lt'.mpr ((Nat.div_lt_iff_lt_mul hR).mpr upper)
      omega
    · exact Nat.le_sqrt'.mpr ((Nat.le_div_iff_mul_le hR).mpr lower)
  refine ⟨sqrt_g, ?_⟩
  rw [sqrt_g]
  have sum : g^2*(a*b)+(p+q) = p*q+1 := by rw [pa,qb]; ring
  omega

end PrimeFactors.JacobiPeriodProbe
