import PrimeFactors.ReducedSmoothReadout
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Prime.Factorial

/-! A square-root prefix leaves at most one large prime-power component. -/

namespace PrimeFactors.SharedSmoothPowers

open ReducedSmoothReadout

/-- Largest missing power of the indicated prime after the square-root prefix. -/
def tail (l cap : ℕ) : ℕ := l ^ (Nat.log l cap - Nat.log l cap.sqrt)

private theorem prime_power_in_prefix {l bound cap : ℕ} (hl : l.Prime) (b : l ≤ bound) :
    l^Nat.log l cap ∣ (schedule bound cap).prod := by
  by_cases fits : l ≤ cap
  · apply List.dvd_prod
    apply List.mem_map.mpr
    exact ⟨l, by simp [hl, b, fits, Nat.lt_succ_of_le b], rfl⟩
  · simp [Nat.log_of_lt (Nat.lt_of_not_ge fits)]

private theorem small_power {l k bound cap : ℕ} (hl : l.Prime) (b : l ≤ bound)
    (fits : l^k ≤ cap) : l^k ∣ (schedule bound cap).prod :=
  (pow_dvd_pow l (Nat.le_log_of_pow_le hl.one_lt fits)).trans (prime_power_in_prefix hl b)

/-- Two distinct prime-power divisors of a positive integer bounded by C
cannot both exceed the integer square root of C. -/
theorem one_large_component {u v k m d cap : ℕ} (hu : u.Prime) (hv : v.Prime)
    (diff : u ≠ v) (hpos : 0 < d) (hcap : d ≤ cap) (a : u^k ∣ d) (b : v^m ∣ d)
    (large : cap.sqrt < u^k) : v^m ≤ cap.sqrt := by
  by_contra! other
  have cp := (((Nat.coprime_primes hu hv).mpr diff).pow_left k).pow_right m
  have low := Nat.le_of_dvd hpos (cp.mul_dvd_of_dvd_of_dvd a b)
  have high : cap < (cap.sqrt+1)*(cap.sqrt+1) := Nat.sqrt_lt.mp (Nat.lt_succ_self _)
  have both : (cap.sqrt+1)*(cap.sqrt+1) ≤ u^k*v^m :=
    Nat.mul_le_mul (Nat.succ_le_of_lt large) (Nat.succ_le_of_lt other)
  exact (Nat.not_lt_of_ge hcap) (high.trans_le (both.trans low))

/-- Every B-smooth d up to C divides the common prefix or the prefix times a
single scheduled completion. The prime is unknown but the entire menu is public. -/
theorem one_completion {d bound cap : ℕ} (hpos : 0 < d) (hcap : d ≤ cap)
    (smooth : ∀ l, l.Prime → l ∣ d → l ≤ bound) :
    d ∣ (schedule bound cap.sqrt).prod ∨
    ∃ l : ℕ, l.Prime ∧ l ≤ bound ∧ l ≤ cap ∧ d ∣ (schedule bound cap.sqrt).prod * tail l cap := by
  by_cases heavy : ∃ l k : ℕ, l.Prime ∧ l^k ∣ d ∧ cap.sqrt < l^k
  · obtain ⟨l,k,hl,hk,large⟩ := heavy
    have capone : 1 ≤ cap.sqrt := Nat.le_sqrt.mpr (by omega)
    have kpos : k ≠ 0 := by rintro rfl; simp at large; omega
    have ldiv := (dvd_pow_self l kpos).trans hk
    have lb := smooth l hl ldiv
    refine Or.inr ⟨l,hl,lb,(Nat.le_of_dvd hpos ldiv).trans hcap,?_⟩
    apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
    intro a j ha hj
    by_cases same : l = a
    · subst a
      have full : l^j ∣ l^Nat.log l cap :=
        pow_dvd_pow l (Nat.le_log_of_pow_le hl.one_lt ((Nat.le_of_dvd hpos hj).trans hcap))
      apply full.trans
      have logle := Nat.log_mono_right (b := l) (Nat.sqrt_le_self cap)
      have factor : l^(Nat.log l cap) = l^(Nat.log l cap.sqrt) * tail l cap := by
        rw [tail, ← pow_add, Nat.add_sub_of_le logle]
      rw [factor]
      exact Nat.mul_dvd_mul (prime_power_in_prefix hl lb) (dvd_refl _)
    · by_cases zero : j = 0
      · simp [zero]
      apply Dvd.dvd.trans _ (dvd_mul_right _ _)
      exact small_power ha (smooth a ha ((dvd_pow_self a zero).trans hj))
        (one_large_component hl ha same hpos hcap hk hj large)
  · push_neg at heavy
    apply Or.inl
    apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
    intro l k hl hk
    by_cases zero : k = 0
    · simp [zero]
    exact small_power hl (smooth l hl ((dvd_pow_self l zero).trans hk)) (heavy l k hl hk)

private theorem prime_in_list_product {l : ℕ} (hl : l.Prime) (xs : List ℕ)
    (h : l ∣ xs.prod) : ∃ x ∈ xs, l ∣ x := by
  induction xs with
  | nil => exact (hl.ne_one (Nat.dvd_one.mp h)).elim
  | cons x xs ih =>
    rcases hl.dvd_mul.mp h with left | right
    · exact ⟨x,by simp,left⟩
    · obtain ⟨y,hy,d⟩ := ih right
      exact ⟨y,by simp [hy],d⟩

private theorem small_prime_of_schedule {l bound cap : ℕ} (hl : l.Prime)
    (h : l ∣ (schedule bound cap).prod) : l ≤ bound := by
  obtain ⟨w,hw,d⟩ := prime_in_list_product hl _ h
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hw
  simp only [List.mem_filter,List.mem_range,decide_eq_true_eq] at hr
  have eq := (Nat.prime_dvd_prime_iff_eq hl hr.2.1).mp (hl.dvd_of_dvd_pow d)
  omega

/-- The single-completion menu preserves the exact original exponent coverage
for every possible local order, including accidental successes. -/
theorem same_coverage {d bound cap : ℕ} (hpos : 0 < d) (hcap : d ≤ cap) :
    d ∣ (schedule bound cap).prod ↔
    d ∣ (schedule bound cap.sqrt).prod ∨
      ∃ l : ℕ, l.Prime ∧ l ≤ bound ∧ l ≤ cap ∧ d ∣ (schedule bound cap.sqrt).prod * tail l cap := by
  constructor
  · intro h
    exact one_completion hpos hcap (fun _ hp hd => small_prime_of_schedule hp (hd.trans h))
  · intro covered
    apply smooth_dvd_schedule hpos hcap
    intro a ha hd
    rcases covered with left | ⟨l,hl,lb,_,right⟩
    · exact small_prime_of_schedule ha (hd.trans left)
    · rcases ha.dvd_mul.mp (hd.trans right) with low | big
      · exact small_prime_of_schedule ha low
      · exact ((Nat.prime_dvd_prime_iff_eq ha hl).mp (ha.dvd_of_dvd_pow big)) ▸ lb

/-- A positional exponent digit can be multiplied into a shared result
before advancing the base to its next radix power. -/
theorem radix_split {G : Type*} [Monoid G] (z : G) (e radix : ℕ) :
    z^e = z^(e % radix) * (z^radix)^(e/radix) := by
  rw [← pow_mul, ← pow_add, Nat.mod_add_div]

/-- After the common prefix, each bounded smooth local order is already killed
or a member of the independent completion menu kills it. -/
theorem kills_smooth_order {G : Type*} [Group G] (x : G) {d bound cap : ℕ}
    (localOrder : orderOf x ∣ d) (hpos : 0 < d) (hcap : d ≤ cap)
    (smooth : ∀ l, l.Prime → l ∣ d → l ≤ bound) :
    let z := x^(schedule bound cap.sqrt).prod
    z = 1 ∨ ∃ l : ℕ, l.Prime ∧ l ≤ bound ∧ l ≤ cap ∧ z^(tail l cap) = 1 := by
  rcases one_completion hpos hcap smooth with done | ⟨l,hp,hb,hc,h⟩
  · exact Or.inl (orderOf_dvd_iff_pow_eq_one.mp (localOrder.trans done))
  · refine Or.inr ⟨l,hp,hb,hc,?_⟩
    rw [← pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.mp (localOrder.trans h)

/-- Once both coordinates at the prefix are nonidentity, a terminal prime
power can never equal the identity simultaneously at both primes. -/
theorem no_double_hit {G H : Type*} [Group G] [Group H] {x : G} {y : H}
    (cp : (orderOf x).Coprime (orderOf y)) (nx : x ≠ 1) (ny : y ≠ 1)
    {l : ℕ} (hl : l.Prime) (cap : ℕ) : (x,y)^(tail l cap) ≠ 1 := by
  intro bad
  by_cases zero : Nat.log l cap - Nat.log l cap.sqrt = 0
  · simp [tail,zero] at bad
    exact nx bad.1
  · have pp : IsPrimePow (tail l cap) :=
      (isPrimePow_nat_iff _).mpr ⟨l,_,hl,Nat.pos_of_ne_zero zero,rfl⟩
    have nz : (x,y) ≠ 1 := fun e => nx (congrArg Prod.fst e)
    rcases before_saturation cp nz pp bad with h | h
    · exact nx h.1
    · exact ny h.2

/-- If the full power is nonidentity no prefix could have reached the
identity. A certificate of the full power therefore suffices on a miss. -/
theorem live_full {G : Type*} [Monoid G] [DecidableEq G] (blocks : List ℕ) (x : G)
    (live : x^blocks.prod ≠ 1) : readout x blocks = x^blocks.prod := by
  induction blocks generalizing x with
  | nil => simp [readout]
  | cons e es ih =>
    rw [List.prod_cons,pow_mul] at live ⊢
    have ne : x^e ≠ 1 := fun h => live (by rw [h,one_pow])
    exact (live_step es rfl ne).trans (ih _ live)

/-- A local numerical power can be linked into a long exponent certificate
without expanding the remaining exponent in the kernel. -/
theorem pow_cons {G : Type*} [Monoid G] {x y : G} {e : ℕ}
    (step : x^e = y) (es : List ℕ) : x^(e::es).prod = y^es.prod := by
  rw [List.prod_cons,pow_mul,step]

/-- The ordinary modulus, accepted base and full-exponent gcd of 1 suffice
to exclude smoothness on both hidden reduced predecessors. -/
theorem certified_exclusion {p q a bound cap : ℕ} (hp : p.Prime) (hq : q.Prime) (different : p ≠ q)
    [NeZero (p*q)] (unit : a.Coprime (p*q)) (accepted : (a : ZMod (p*q))^(p*q-1) ≠ 1)
    (pfit : p-1 ≤ cap) (qfit : q-1 ≤ cap)
    (clear : Nat.gcd (((((a : ZMod (p*q))^(p*q-1))^(schedule bound cap).prod)).val-1) (p*q) = 1) :
    (∃ l : ℕ, l.Prime ∧ l ∣ (p-1)/(p-1).gcd (q-1) ∧ bound < l) ∧
    (∃ l : ℕ, l.Prime ∧ l ∣ (q-1)/(p-1).gcd (q-1) ∧ bound < l) := by
  let u := ZMod.unitOfCoprime a unit
  have nonidentity : u^(p*q-1) ≠ 1 := fun h => accepted (congrArg Units.val h)
  have live : (((a : ZMod (p*q))^(p*q-1))^(schedule bound cap).prod) ≠ 1 := by
    intro h
    have n : 1 < p*q := hp.one_lt.trans_le (Nat.le_mul_of_pos_right p hq.pos)
    haveI : Fact (1 < p*q) := ⟨n⟩
    rw [h, ZMod.val_one (p*q), Nat.sub_self, Nat.gcd_zero_left] at clear
    omega
  apply exhaustion hp hq different u nonidentity pfit qfit
  change (((readout (u^(p*q-1)) (schedule bound cap) : (ZMod (p*q))ˣ) : ZMod (p*q)).val-1).gcd _ = 1
  rw [value_readout, Units.val_pow_eq_pow_val]
  change ((readout ((a : ZMod (p*q))^(p*q-1)) (schedule bound cap)).val-1).gcd _ = 1
  rw [live_full _ _ live]
  exact clear

/-- Above the public sieve cutoff and below its next square, coprimality with
the cutoff factorial recognizes primes. Only the small table uses this test. -/
noncomputable def trialPrime (cut n : ℕ) : Bool :=
  if 2 ≤ n ∧ cut < n ∧ n < (cut+1)^2 then decide (n.Coprime cut.factorial)
  else decide n.Prime

theorem trialPrime_eq (cut n : ℕ) : trialPrime cut n = decide n.Prime := by
  unfold trialPrime
  split_ifs with range
  · apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    rw [Nat.coprime_factorial_iff (by omega : n ≠ 1)]
    constructor
    · intro big
      by_contra np
      have small := Nat.minFac_sq_le_self (by omega : 0 < n) np
      exact (Nat.not_lt_of_ge (Nat.pow_le_pow_left (Nat.succ_le_of_lt big) 2))
        (small.trans_lt range.2.2)
    · intro prime
      rw [prime.minFac_eq]
      exact range.2.1
  · rfl

end PrimeFactors.SharedSmoothPowers
