import PrimeFactors.SingleBaseRepeat
import Mathlib.Tactic.NormNum.Prime

/-! A sufficient injectivity criterion for one prescribed unit, using its
actual local orders. The criterion need not be computable before factoring. -/

namespace PrimeFactors.FixedBaseSignature
open Finset

/-- Two local orders can share at most the gcd of their ambient group sizes. -/
theorem product_gap {A B r s e : ℕ} (a : 0<A)
    (localA : r∣A) (localB : s∣B) (pos : 0<e) (gapA : r∣e) (gapB : s∣e) :
    r*s ≤ e*A.gcd B := by
  have overlap : r.gcd s ∣ A.gcd B :=
    Nat.dvd_gcd ((Nat.gcd_dvd_left r s).trans localA) ((Nat.gcd_dvd_right r s).trans localB)
  have common := Nat.le_of_dvd (Nat.gcd_pos_of_pos_left B a) overlap
  have period := Nat.le_of_dvd pos (Nat.lcm_dvd gapA gapB)
  calc
    r*s = r.lcm s*r.gcd s := by rw [mul_comm (r.lcm s),Nat.gcd_mul_lcm]
    _ ≤ _ := Nat.mul_le_mul period common

/-- A positive repeat up to W is impossible for this particular unit. -/
theorem no_repeat {p q W : ℕ} [NeZero (p*q)] (hp : p.Prime) (hq : q.Prime)
    (g : (ZMod (p*q))ˣ)
    (large : W*Nat.gcd (p-1) (q-1) <
      orderOf (ZMod.unitsMap (dvd_mul_right p q) g)*orderOf (ZMod.unitsMap (dvd_mul_left q p) g)) :
    g∉SingleBaseRepeat.repeated (p*q) W := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  intro hit
  obtain ⟨e,he,eq⟩ := SingleBaseRepeat.mem_repeated.mp hit
  obtain ⟨ep,ew⟩ := mem_Icc.mp he
  let x := ZMod.unitsMap (dvd_mul_right p q) g
  let y := ZMod.unitsMap (dvd_mul_left q p) g
  have ox : orderOf x∣p-1 := (Nat.prime_iff_card_units p).mp hp ▸ orderOf_dvd_card
  have oy : orderOf y∣q-1 := (Nat.prime_iff_card_units q).mp hq ▸ orderOf_dvd_card
  have ex : x^e=1 := by simpa [x] using congrArg (ZMod.unitsMap (dvd_mul_right p q)) eq
  have ey : y^e=1 := by simpa [y] using congrArg (ZMod.unitsMap (dvd_mul_left q p)) eq
  have bound := product_gap (Nat.sub_pos_of_lt hp.one_lt) ox oy ep
    (orderOf_dvd_of_pow_eq_one ex) (orderOf_dvd_of_pow_eq_one ey)
  exact (not_le_of_gt large) (bound.trans (Nat.mul_le_mul_right _ ew))

/-- Any two exponents in the interval have different signatures unless they
coincide. This applies independently of which interval contains the factor sum. -/
theorem interval_injective {n L U : ℕ} [NeZero n] (g : (ZMod n)ˣ)
    (regular : g∉SingleBaseRepeat.repeated n (U-L)) :
    Set.InjOn (fun s : ℕ => g^s) (Set.Icc L U) := by
  intro s hs t ht eq
  have impossible {i j : ℕ} (ord : i<j) (low : L ≤ i) (hi : j≤U) (same : g^i=g^j) : False := by
    apply regular
    apply SingleBaseRepeat.mem_repeated.mpr
    refine ⟨j-i,mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩
    have cancel : g^i*g^(j-i)=g^i := by rw [←pow_add,Nat.add_sub_of_le ord.le,same]
    exact mul_eq_left.mp cancel
  rcases lt_trichotomy s t with less|equal|more
  · exact (impossible less hs.1 ht.2 eq).elim
  · exact equal
  · exact (impossible more ht.1 hs.2 eq.symm).elim

/-- Test one candidate against a public target when the allowed gap is below
every possible repeat. The proof uses the unit to cancel equal powers. -/
theorem recognize {n L U S target s : ℕ} [NeZero n] (g : (ZMod n)ˣ)
    (noGap : ∀ e, 0<e → e≤U-L → (g : ZMod n)^e≠1)
    (trueSum : S ∈ Set.Icc L U) (candidate : s ∈ Set.Icc L U)
    (known : g^S=g^target) :
    (g : ZMod n)^s=(g : ZMod n)^target ↔ s=S := by
  have regular : g∉SingleBaseRepeat.repeated n (U-L) := by
    intro bad
    obtain ⟨e,he,h⟩ := SingleBaseRepeat.mem_repeated.mp bad
    obtain ⟨pos,cap⟩ := Finset.mem_Icc.mp he
    apply noGap e pos cap
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val h
  constructor
  · intro hit
    apply interval_injective g regular candidate trueSum
    change g^s=g^S
    rw [known]
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val] using hit
  · rintro rfl
    simpa only [Units.val_pow_eq_pow_val] using congrArg Units.val known

/-- A witnessed prime-order power forces that prime into every annihilator of
the original element. This holds for monoids as well as units. -/
theorem prime_period {M : Type*} [Monoid M] {x : M} {e k r : ℕ} (prime : r.Prime)
    (killed : (x^k)^r=1) (nontrivial : x^k≠1) (ann : x^e=1) : r∣e := by
  letI : Fact r.Prime := ⟨prime⟩
  rw [←orderOf_eq_prime killed nontrivial]
  apply orderOf_dvd_of_pow_eq_one
  rw [←pow_mul,mul_comm k e,pow_mul,ann,one_pow]

/-- Two possibly different local powers certify distinct prime divisors of
the order. Every positive repeat is consequently at least their product. -/
theorem product_period {p q r s k l e g : ℕ}
    (rp : r.Prime) (sp : s.Prime) (ne : r≠s)
    (hr : ((g:ZMod p)^k)^r=1) (nr : (g:ZMod p)^k≠1)
    (hs : ((g:ZMod q)^l)^s=1) (ns : (g:ZMod q)^l≠1)
    (ann : (g:ZMod (p*q))^e=1) : r*s∣e := by
  have project {m : ℕ} (dm : m∣p*q) : (g:ZMod m)^e=1 := by
    simpa only [map_pow,map_natCast,map_one] using congrArg (ZMod.castHom dm (ZMod m)) ann
  exact ((Nat.coprime_primes rp sp).mpr ne).mul_dvd_of_dvd_of_dvd
    (prime_period rp hr nr (project (dvd_mul_right p q)))
    (prime_period sp hs ns (project (dvd_mul_left q p)))

/-- A genuine 12-bit-prime pair, a false sum in the same balanced interval,
and the common power of two. This equality concerns the power test only. -/
theorem base_two_alias :
    Nat.Prime 2351 ∧ Nat.Prime 3761 ∧ 2351*3761=8842111 ∧
    2351+3761=6112 ∧ (6112:ℕ)<6300 ∧
    4*8842111≤(6112:ℕ)^2 ∧ 2*(6300:ℕ)^2≤9*8842111 ∧
    (2:ZMod 8842111)^6112=5844590 ∧ (2:ZMod 8842111)^6300=5844590 := by
  constructor
  · norm_num
  constructor
  · norm_num
  decide +kernel

/-- The local sum sieve at 3 independently rejects 6300. The example therefore
refutes universal injectivity of the powers alone. -/
theorem false_sum_excluded_mod_three :
    ¬AdmissibleSum (8842111:ZMod 3) (6300:ZMod 3) := by
  unfold AdmissibleSum
  decide +kernel

end PrimeFactors.FixedBaseSignature
