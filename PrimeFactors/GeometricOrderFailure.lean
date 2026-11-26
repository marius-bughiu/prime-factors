import PrimeFactors.SingleBaseRepeat
import PrimeFactors.UniformDivisorCount
import PrimeFactors.Fermat
import PrimeFactors.ReducedSlopes

/-! Equal small multiplicative orders under the two reductions of one uniformly
chosen unit. The sample space fixes the two primes; randomness is only over the
unit modulo their product. These counts price the ambiguity after observing two
common positions in a dense interval of width W. -/
namespace PrimeFactors.GeometricOrderFailure

open Finset

/-- Orders capable of occurring at both primes within the square-width cutoff. -/
noncomputable def orders (p q W : ℕ) : Finset ℕ :=
  ((p-1).gcd (q-1)).divisors.filter (fun d => d^2≤W)

noncomputable def localPair {p q : ℕ} (cop : p.Coprime q) :
    (ZMod (p*q))ˣ ≃* (ZMod p)ˣ × (ZMod q)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder cop).toMulEquiv).trans MulEquiv.prodUnits

private noncomputable def oneOrder (p d : ℕ) [NeZero p] : Finset (ZMod p)ˣ :=
  univ.filter fun x => orderOf x=d

/-- Pull the paired local order classes back to units of the original modulus. -/
noncomputable def exceptional {p q : ℕ} [NeZero p] [NeZero q] (cop : p.Coprime q) (W : ℕ) :
    Finset (ZMod (p*q))ˣ :=
  ((orders p q W).biUnion (fun d => oneOrder p d ×ˢ oneOrder q d)).image (localPair cop).symm

theorem mem_exceptional {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (W : ℕ) (u : (ZMod (p*q))ˣ) :
    u∈exceptional cop W ↔
      orderOf (localPair cop u).1=orderOf (localPair cop u).2 ∧
      (orderOf (localPair cop u).1)^2≤W := by
  classical
  let a := (localPair cop u).1
  let b := (localPair cop u).2
  have hp : p.Prime := Fact.out
  have hq : q.Prime := Fact.out
  have pa : orderOf a ∣ p-1 := (Nat.prime_iff_card_units p).mp hp ▸ orderOf_dvd_card
  have qb : orderOf b ∣ q-1 := (Nat.prime_iff_card_units q).mp hq ▸ orderOf_dvd_card
  have pos : 0<p-1 := by have := hp.two_le; omega
  have nz := (Nat.gcd_pos_of_pos_left (q-1) pos).ne'
  constructor
  · intro hu
    obtain ⟨z,hz,eq⟩ := mem_image.mp hu
    have same : z=localPair cop u := by rw [←eq, MulEquiv.apply_symm_apply]
    subst z
    obtain ⟨d,hd,hdz⟩ := mem_biUnion.mp hz
    obtain ⟨l,r⟩ := mem_product.mp hdz
    exact ⟨(mem_filter.mp l).2.trans (mem_filter.mp r).2.symm,
      (mem_filter.mp l).2 ▸ (mem_filter.mp hd).2⟩
  · rintro ⟨eq,width⟩
    change orderOf a = orderOf b at eq
    refine mem_image.mpr ⟨localPair cop u, mem_biUnion.mpr ⟨orderOf a, ?_,?_⟩,
      (localPair cop).symm_apply_apply u⟩
    · exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.dvd_gcd pa (eq ▸ qb),nz⟩,width⟩
    · exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,rfl⟩,
        mem_filter.mpr ⟨mem_univ _,eq.symm⟩⟩

/-- The exact count is the sum of squared totients of common small orders. -/
theorem exact_count {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q) (W : ℕ) :
    (exceptional cop W).card = ∑ d∈orders p q W, d.totient^2 := by
  classical
  rw [exceptional,card_image_of_injective _ (localPair cop).symm.injective,card_biUnion]
  · apply sum_congr rfl
    intro d hd
    have div := Nat.dvd_of_mem_divisors (mem_filter.mp hd).1
    have localCard (t : ℕ) [inst : Fact t.Prime] (div : d∣t-1) : (oneOrder t d).card=d.totient := by
      exact IsCyclic.card_orderOf_eq_totient ((Nat.prime_iff_card_units t).mp inst.out ▸ div)
    rw [card_product,localCard p (div.trans (Nat.gcd_dvd_left ..)),
      localCard q (div.trans (Nat.gcd_dvd_right ..)),pow_two]
  · intro d _ e _ ne
    apply disjoint_left.mpr
    intro z hd he
    exact ne ((mem_filter.mp (mem_product.mp hd).1).2.symm.trans
      (mem_filter.mp (mem_product.mp he).1).2)

/-- One term costs at most W; the number of terms is bounded by the divisor
count of the gcd of the local group sizes. -/
theorem count_le {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q) (W : ℕ) :
    (exceptional cop W).card ≤ ((p-1).gcd (q-1)).divisors.card*W := by
  rw [exact_count]
  calc
    _ ≤ ∑ _d∈orders p q W, W := sum_le_sum fun d hd =>
      (Nat.pow_le_pow_left (Nat.totient_le d) 2).trans (mem_filter.mp hd).2
    _ = (orders p q W).card*W := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (card_le_card (filter_subset ..))

/-- A public Fermat witness has distinct local orders, with no size condition
on those orders and no semiprime balance condition. -/
theorem fermat_witness_orders_ne {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (cop : p.Coprime q) (u : (ZMod (p*q))ˣ) (witness : u^(p*q-1)≠1) :
    orderOf (localPair cop u).1 ≠ orderOf (localPair cop u).2 := by
  intro same
  let a := (localPair cop u).1
  let b := (localPair cop u).2
  have pa : orderOf a ∣ p-1 := (Nat.prime_iff_card_units p).mp hp.out ▸ orderOf_dvd_card
  have qb : orderOf b ∣ q-1 := (Nat.prime_iff_card_units q).mp hq.out ▸ orderOf_dvd_card
  have div := Nat.dvd_gcd pa (same ▸ qb)
  rw [←gcd_predecessor_product hp.out.pos hq.out.pos] at div
  have exp : orderOf a ∣ p*q-1 := div.trans (Nat.gcd_dvd_right ..)
  apply witness
  apply (localPair cop).injective
  rw [map_pow,map_one]
  exact Prod.ext (orderOf_dvd_iff_pow_eq_one.mp exp)
    (orderOf_dvd_iff_pow_eq_one.mp (same ▸ exp))

/-- At least half of all units pass the public witness requirement; the
complementary set is counted by `count_product_predecessor_identity`. -/
theorem half_fermat_witnesses {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (lt : p<q) :
    Fintype.card (ZMod (p*q))ˣ ≤ 2*(univ.filter fun u : (ZMod (p*q))ˣ => u^(p*q-1)≠1).card := by
  classical
  let g := (p-1).gcd (q-1)
  have pp := hp.out.two_le
  have gpos : 0<g := Nat.gcd_pos_of_pos_left _ (by omega)
  have gsmall : g≤p-1 := Nat.gcd_le_left _ (by omega)
  obtain ⟨k,hk⟩ := Nat.gcd_dvd_right (p-1) (q-1)
  change q-1=g*k at hk
  have two : 2≤k := by
    by_contra! t
    interval_cases k <;> simp_all <;> omega
  have qbig : 2*g≤q-1 := by rw [hk,mul_comm]; exact Nat.mul_le_mul_left _ two
  have rate := Nat.mul_le_mul gsmall qbig
  have count := count_product_predecessor_identity hp.out hq.out lt.ne
  have total := SingleBaseRepeat.unit_count hp.out hq.out lt.ne
  have both := Finset.filter_card_add_filter_neg_card_eq_card
    (s:=univ) (fun u : (ZMod (p*q))ˣ => u^(p*q-1)=1)
  rw [card_univ,count] at both
  change g^2 + _ = _ at both
  rw [total] at both ⊢
  nlinarith only [rate,both]

/-- Apply the finite conclusion of the least-prime-outside-subgroup theorem
to the Fermat kernel. The hypothesis names the analytic input explicitly. -/
theorem small_prime_witness {p q B : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (lt : p<q) (outside : SmallPrimeOutside (p*q) B) :
    ∃ a : ℕ, a.Prime ∧ a≤B ∧ ∃ cop : a.Coprime (p*q),
      (ZMod.unitOfCoprime a cop)^(p*q-1)≠1 := by
  classical
  let H := (powMonoidHom (p*q-1) : (ZMod (p*q))ˣ →* (ZMod (p*q))ˣ).ker
  have pos : 0 < (univ.filter (fun u : (ZMod (p*q))ˣ => u^(p*q-1)≠1)).card := by
    have many := half_fermat_witnesses lt
    have allPos : 0<Fintype.card (ZMod (p*q))ˣ := Fintype.card_pos
    omega
  obtain ⟨u,hu⟩ := card_pos.mp pos
  have proper : H≠⊤ := by
    intro top
    have mem : u∈H := top ▸ Subgroup.mem_top u
    exact (mem_filter.mp hu).2 mem
  exact outside H proper

set_option exponentiation.threshold 65536 in
private theorem divisor_bound {g : ℕ} (pos : 0<g) (small : g<2^1024) :
    g.divisors.card<2^142 := by
  apply (Nat.pow_lt_pow_iff_left (by decide : 336≠0)).mp
  calc
    _ < 2^(14882+32*1024) := UniformDivisorCount.below_power_two pos small
    _ < 2^(142*336) := Nat.pow_lt_pow_right (by decide : 1<2) (by decide : 14882+32*1024 < 142*336)
    _ = _ := pow_mul ..

set_option exponentiation.threshold 4096 in
/-- For every fixed pair of distinct 1024-bit primes and its dense balanced
interval, fewer than one in 2^884 units have equal local orders d with d²≤W. -/
theorem dense {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (small : 2^1023≤p) (lt : p<q) (cap : q<2^1024) :
    let W := (9*(p*q)/2).sqrt-ceilSqrt (4*(p*q))
    2^884*(exceptional ((Nat.coprime_primes hp.out hq.out).mpr lt.ne) W).card <
      Fintype.card (ZMod (p*q))ˣ := by
  intro W
  let cop := (Nat.coprime_primes hp.out hq.out).mpr lt.ne
  have neq : p≠2^1023 := fun eq => Nat.Prime.not_prime_pow (by decide : 2≤1023) (eq ▸ hp.out)
  have lo : 2^1023≤p-1 := by omega
  have big : 64≤p := by omega
  have bal : q≤2*p := by omega
  let g := (p-1).gcd (q-1)
  have pos : 0<g := Nat.gcd_pos_of_pos_left _ (by omega)
  have under : g<2^1024 := (Nat.gcd_le_left _ (by omega : 0<p-1)).trans_lt (by omega)
  have count := (count_le cop W).trans (Nat.mul_le_mul_right W (divisor_bound pos under).le)
  let L := ceilSqrt (4*(p*q))
  let U := (9*(p*q)/2).sqrt
  have width : 8*W<q-1 := by
    by_cases nonempty : L≤U
    · have lower : 4*(p*q)≤L^2 := ceilSqrt_le_iff.mp le_rfl
      have upper : 2*U^2≤9*(p*q) := (Nat.mul_le_mul_left 2 (Nat.sqrt_le' _)).trans (Nat.mul_div_le ..)
      exact (SumSignatureProbability.diameter big lt.le bal lower upper nonempty).2
    · change 8*(U-L)<q-1; omega
  have total := SingleBaseRepeat.unit_count hp.out hq.out lt.ne
  rw [total]
  calc
    _ ≤ 2^884*(2^142*W) := Nat.mul_le_mul_left _ count
    _ = 2^1023*(8*W) := by
      rw [←Nat.mul_assoc,←Nat.mul_assoc]
      exact congrArg (·*W) (by decide +kernel : 2^884*2^142=2^1023*8)
    _ < 2^1023*(q-1) := Nat.mul_lt_mul_of_pos_left width (by positivity)
    _ ≤ (p-1)*(q-1) := Nat.mul_le_mul_right _ lo

end PrimeFactors.GeometricOrderFailure
