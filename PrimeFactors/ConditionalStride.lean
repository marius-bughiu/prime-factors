import PrimeFactors.GapStride
import PrimeFactors.DyadicReadout
import PrimeFactors.ResidueCount
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.GroupTheory.Index

namespace PrimeFactors

open scoped Classical

/-- Two partners whose products share the observed word and which have the
same stride residue occupy one class modulo the least common multiple. -/
theorem conditional_partner_unique {Q d p q₁ q₂ : ℕ} (unitP : p.Coprime Q) :
    (p*q₁ ≡ p*q₂ [MOD Q] ∧ q₁ ≡ q₂ [MOD d]) ↔ q₁ ≡ q₂ [MOD Q.lcm d] := by
  constructor
  · rintro ⟨cell,stride⟩
    exact Nat.mod_lcm (cell.cancel_left_of_coprime unitP.symm) stride
  · intro h
    exact ⟨(h.of_dvd (Nat.dvd_lcm_left _ _)).mul_left _, h.of_dvd (Nat.dvd_lcm_right _ _)⟩

/-- Even when the public word and the gap stride share primes, their two
congruences are compatible precisely at the square roots of the observed
word modulo their gcd. The class representative is smaller than their lcm. -/
theorem conditional_partner_class {Q d p a : ℕ} (hQ : Q ≠ 0) (hd : d ≠ 0)
    (unitP : p.Coprime Q) :
    p^2 ≡ a [MOD Q.gcd d] ↔ ∃ b < Q.lcm d, ∀ q,
      (p*q ≡ a [MOD Q] ∧ q ≡ p [MOD d]) ↔ q ≡ b [MOD Q.lcm d] := by
  haveI : NeZero Q := ⟨hQ⟩
  let u := ZMod.unitOfCoprime p unitP
  obtain ⟨c,hc⟩ := ZMod.natCast_zmod_surjective ((↑(u⁻¹) : ZMod Q)*(a : ZMod Q))
  have prod : p*c ≡ a [MOD Q] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    rw [Nat.cast_mul,hc,← ZMod.coe_unitOfCoprime p unitP,← mul_assoc,Units.mul_inv,one_mul]
  have left := Nat.gcd_dvd_left Q d
  have right := Nat.gcd_dvd_right Q d
  constructor
  · intro square
    rw [pow_two] at square
    have compatible : c ≡ p [MOD Q.gcd d] :=
      ((prod.of_dvd left).trans square.symm).cancel_left_of_coprime (unitP.of_dvd_right left).symm
    let b := Nat.chineseRemainder' compatible
    have cell : p*b.val ≡ a [MOD Q] := (b.property.1.mul_left p).trans prod
    refine ⟨b.val,Nat.chineseRemainder'_lt_lcm compatible hQ hd,fun q => ?_⟩
    constructor
    · rintro ⟨h,k⟩
      exact (conditional_partner_unique unitP).mp ⟨h.trans cell.symm,k.trans b.property.2.symm⟩
    · intro h
      obtain ⟨h,k⟩ := (conditional_partner_unique unitP).mpr h
      exact ⟨h.trans cell,k.trans b.property.2⟩
  · rintro ⟨b,_,hb⟩
    obtain ⟨h,k⟩ := (hb b).mpr Nat.ModEq.rfl
    rw [pow_two]
    exact ((k.of_dvd right).symm.mul_left p).trans (h.of_dvd left)

/-- The two prime-progressions denominators in a product-word cell multiply
to the same totient product as the original two moduli. -/
theorem totient_gcd_mul_totient_lcm {Q d : ℕ} (hQ : Q ≠ 0) (hd : d ≠ 0) :
    (Q.gcd d).totient * (Q.lcm d).totient = Q.totient*d.totient := by
  have pf : (Q.lcm d).primeFactors = (Q*d).primeFactors := by
    apply Finset.Subset.antisymm (Nat.primeFactors_mono (Nat.lcm_dvd_mul _ _) (mul_ne_zero hQ hd))
    intro p hp
    obtain ⟨prime,dvd,_⟩ := Nat.mem_primeFactors.mp hp
    refine Nat.mem_primeFactors.mpr ⟨prime,?_,Nat.lcm_ne_zero hQ hd⟩
    rcases prime.dvd_mul.mp dvd with h | h
    · exact h.trans (Nat.dvd_lcm_left _ _)
    · exact h.trans (Nat.dvd_lcm_right _ _)
  have common := Nat.gcd_mul_lcm Q d
  have scaled : (Q*d).totient = Q.gcd d * (Q.lcm d).totient := by
    apply Nat.cast_injective (R := ℚ)
    rw [Nat.cast_mul (Q.gcd d),Nat.totient_eq_mul_prod_factors,Nat.totient_eq_mul_prod_factors,pf,
      ← mul_assoc,← Nat.cast_mul,common]
  have h := Nat.totient_gcd_mul_totient_mul Q d
  rw [scaled] at h
  apply Nat.mul_right_cancel (Nat.gcd_pos_of_pos_left d (Nat.pos_of_ne_zero hQ))
  simpa only [mul_assoc,mul_comm,mul_left_comm] using h

/-- Number of square roots of `a` among units, written in a form suitable
for summing over every possible observation at a prime. -/
noncomputable def strideUnitRoots {G : Type*} [Group G] [Fintype G] [DecidableEq G] (a : G) : ℕ :=
  (Finset.univ.filter (fun x : G => x^2=a)).card

private theorem sum_strideUnitRoots (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    ∑ a : G, strideUnitRoots a = Fintype.card G := by
  classical
  simpa [strideUnitRoots] using (Finset.card_eq_sum_card_fiberwise
    (show Set.MapsTo (fun x : G => x^2) (Finset.univ : Finset G) (Finset.univ : Finset G) from fun _ _ => Finset.mem_univ _)).symm

/-- At an odd prime, every nonempty unit square-root fiber has size two. -/
theorem strideUnitRoots_prime {p : ℕ} [Fact p.Prime] (odd : p ≠ 2) (a : (ZMod p)ˣ) :
    strideUnitRoots a = (if IsSquare (a : ZMod p) then 2 else 0) := by
  classical
  have card : strideUnitRoots a = (squareRootsMod p (a : ZMod p)).card := by
    unfold strideUnitRoots
    apply Finset.card_bij (fun (x : (ZMod p)ˣ) _ => (x : ZMod p))
    · intro x hx
      have h := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) (Finset.mem_filter.mp hx).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨x.ne_zero,Finset.mem_univ _⟩, by simpa using h⟩
    · exact fun _ _ _ _ h => Units.ext h
    · intro r hr
      obtain ⟨hr,h⟩ := Finset.mem_filter.mp hr
      let x := Units.mk0 r (Finset.mem_erase.mp hr).1
      refine ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Units.ext ?_⟩,rfl⟩
      simpa [x] using h
  rw [card]
  split_ifs with h
  · exact card_squareRootsMod_of_square p odd _ a.ne_zero h
  · exact card_squareRootsMod_of_nonsquare p _ h

/-- A unit has at most four square roots modulo any power of two. The
injective count multiplies every root by the initial segment of powers of 5;
squaring distinguishes those translates by the exact exponent period. -/
theorem strideUnitRoots_two_pow_le_four (e : ℕ) (a : (ZMod (2^e))ˣ) :
    strideUnitRoots a ≤ 4 := by
  classical
  let S := Finset.univ.filter (fun x : (ZMod (2^e))ˣ => x^2=a)
  change S.card ≤ 4
  by_cases small : e < 3
  · have h := Finset.card_le_univ S
    rw [ZMod.card_units_eq_totient] at h
    interval_cases e <;> exact h.trans (by decide)
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le' (show 3 ≤ e by omega)
  let u := ZMod.unitOfCoprime 5 (Nat.Coprime.pow_right (j+3) (by decide : Nat.Coprime 5 2))
  let f (v : Fin (2^j) × ↥S) := u^v.1.val*v.2.val
  have inj : Function.Injective f := by
    rintro ⟨i,x⟩ ⟨l,y⟩ h
    change u^i.val*x.val=u^l.val*y.val at h
    have hx := (Finset.mem_filter.mp x.property).2
    have hy := (Finset.mem_filter.mp y.property).2
    have sq := congrArg (fun z : (ZMod (2^(j+3)))ˣ => z^2) h
    dsimp only at sq
    rw [mul_pow,mul_pow,hx,hy,mul_left_inj] at sq
    have hs := congrArg (fun z : (ZMod (2^(j+3)))ˣ => (z : ZMod (2^(j+3)))) sq
    change ((↑(5 : ℕ) : ZMod (2^(j+3)))^i.val)^2 = ((↑(5 : ℕ) : ZMod (2^(j+3)))^l.val)^2 at hs
    rw [← pow_mul,← pow_mul,← Nat.cast_pow,← Nat.cast_pow,ZMod.natCast_eq_natCast_iff] at hs
    have ex := (five_power_modEq_iff (j+1) _ _).mp hs
    rw [pow_succ] at ex
    have eq : i = l := by
      apply Fin.ext
      exact (Nat.ModEq.eq_of_lt_of_lt (ex.mul_right_cancel' (by decide)) i.isLt l.isLt)
    subst l
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel h))
  have count := Fintype.card_le_of_injective f inj
  rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_coe,ZMod.card_units_eq_totient,
    Nat.totient_prime_pow Nat.prime_two (by omega),show j+3-1=j+2 by omega,pow_add 2 j 2] at count
  exact Nat.le_of_mul_le_mul_left (by simpa using count) (by positivity : 0 < 2^j)

/-- Pulling a weight back through a surjective group homomorphism preserves
its exact uniform mean, regardless of the size of the kernel. -/
private theorem pullback_cell_sum {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    (f : G →* H) (onto : Function.Surjective f) (w : H → ℚ) :
    (∑ x : G, w (f x)) * (Fintype.card H) = (Fintype.card G) * ∑ y : H, w y := by
  classical
  let k := (Finset.univ.filter (fun x : G => f x=1)).card
  have fibers (y : H) : (Finset.univ.filter (fun x : G => f x=y)).card = k :=
    MonoidHom.card_fiber_eq_of_mem_range f (onto y) (onto 1)
  have total : Fintype.card G = Fintype.card H * k := by
    simpa only [Finset.card_univ,fibers,Finset.sum_const,smul_eq_mul] using
      Finset.card_eq_sum_card_fiberwise (show Set.MapsTo f (Finset.univ : Finset G) (Finset.univ : Finset H) from fun _ _ => Finset.mem_univ _)
  have ws : ∑ x : G, w (f x) = (k:ℚ) * ∑ y : H, w y := by
    rw [← Finset.sum_fiberwise Finset.univ f,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    calc
      _ = ∑ _x ∈ Finset.univ.filter (fun x : G => f x=y), w y :=
        Finset.sum_congr rfl (fun x hx => congrArg w (Finset.mem_filter.mp hx).2)
      _ = _ := by simp only [Finset.sum_const,fibers,nsmul_eq_mul]
  rw [ws,total,Nat.cast_mul]
  ring

/-- CRT projection of a complete public word onto a list of coprime divisors. -/
noncomputable def strideCellMap {Q : ℕ} {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (cop : Pairwise (Function.onFun Nat.Coprime p)) (divides : (∏ i, p i) ∣ Q) :
    (ZMod Q)ˣ →* ((i : ι) → (ZMod (p i))ˣ) :=
  ((MulEquiv.piUnits).toMonoidHom.comp
      (Units.mapEquiv (ZMod.prodEquivPi p cop).toMulEquiv).toMonoidHom).comp (ZMod.unitsMap divides)

/-- The exact mean multiplicative penalty for any selected odd-prime divisors
of the observed modulus. This is stated for the entire unit group modulo `Q`,
so unselected divisors and higher powers in the observed word are included. -/
theorem conditional_stride_mean {Q : ℕ} [NeZero Q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (cop : Pairwise (Function.onFun Nat.Coprime p))
    (divides : (∏ i, p i) ∣ Q) :
    let f := strideCellMap p cop divides
    (∑ a : (ZMod Q)ˣ, ∏ i, (1 + (strideUnitRoots (f a i) : ℚ)/(2*((p i:ℚ)-1)))) =
      (Q.totient : ℚ) * ∏ i, (1 + 1/(2*((p i:ℚ)-1))) := by
  classical
  let f := strideCellMap p cop divides
  let w (i : ι) (x : (ZMod (p i))ˣ) : ℚ := 1+(strideUnitRoots x:ℚ)/(2*((p i:ℚ)-1))
  let W (x : (i : ι) → (ZMod (p i))ˣ) := ∏ i, w i (x i)
  change ∑ a : (ZMod Q)ˣ, W (f a) = _
  have onto : Function.Surjective f :=
    MulEquiv.piUnits.surjective.comp
      ((Units.mapEquiv (ZMod.prodEquivPi p cop).toMulEquiv).surjective.comp (ZMod.unitsMap_surjective divides))
  have localMean (i : ι) : ∑ x : (ZMod (p i))ˣ, w i x =
      (Fintype.card (ZMod (p i))ˣ : ℚ) * (1+1/(2*((p i:ℚ)-1))) := by
    unfold w
    simp only [div_eq_mul_inv]
    rw [Finset.sum_add_distrib,← Finset.sum_mul, ← Nat.cast_sum,sum_strideUnitRoots]
    simp
    ring
  have mean : ∑ x, W x = (Fintype.card ((i : ι) → (ZMod (p i))ˣ) : ℚ) *
      ∏ i, (1+1/(2*((p i:ℚ)-1))) := by
    unfold W
    rw [← Fintype.prod_sum,Finset.prod_congr rfl (fun i _ => localMean i),Finset.prod_mul_distrib,
      Fintype.card_pi,Nat.cast_prod]
  have all := pullback_cell_sum f onto W
  rw [mean,ZMod.card_units_eq_totient] at all
  apply mul_right_cancel₀ (b := (Fintype.card ((i : ι) → (ZMod (p i))ˣ) : ℚ))
    (by exact_mod_cast Fintype.card_ne_zero)
  linear_combination all


private def advicePrimeTest (n : ℕ) : Bool :=
  (List.range 14).all (fun j => n%(j+2) != 0)

private theorem advicePrimeTest_spec {n : ℕ} (lo : 128 ≤ n) (hi : n < 256) :
    advicePrimeTest n = true ↔ n.Prime := by
  simp only [advicePrimeTest,List.all_eq_true,List.mem_range,bne_iff_ne]
  constructor
  · intro test
    by_contra bad
    have h := Nat.minFac_sq_le_self (by omega : 0 < n) bad
    have hp := (Nat.minFac_prime (show n ≠ 1 by omega)).two_le
    have small : n.minFac < 16 := by
      by_contra! h16
      have sq := Nat.pow_le_pow_left h16 2
      norm_num at sq
      omega
    have reject := test (n.minFac-2) (by omega)
    rw [Nat.sub_add_cancel hp] at reject
    exact reject (Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd n))
  · intro prime j hj h
    have dv := Nat.dvd_of_mod_eq_zero h
    have eq := (Nat.dvd_prime_two_le prime (show 2 ≤ j+2 by omega)).mp dv
    omega

private def advicePrimes := ((List.range 128).map (· + 128)).filter advicePrimeTest

private theorem advicePrimes_values : advicePrimes =
    [131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251] := by
  decide +kernel

private def adviceExamplePairs : List (ℕ × ℕ) :=
  advicePrimes.flatMap fun p => (advicePrimes.filter (p < ·)).map (fun q => (p,q))

private def exampleHit (w : ℕ × ℕ) (m b : ℕ) : Bool :=
  (w.2-w.1)/2 % m == 0 && ((w.1+w.2)/2-b*m^2)^2 < w.1*w.2

private theorem exampleHit_iff {p q m b : ℕ} (pos : 0 < p*q) :
    exampleHit (p,q) m b = true ↔ (q-p)/2 % m = 0 ∧ (p+q)/2 < ceilSqrt (p*q)+b*m^2 := by
  simp only [exampleHit,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  have cutoff : 0 < ceilSqrt (p*q) := by
    by_contra! h
    exact (Nat.not_le_of_gt pos) ((ceilSqrt_le_iff.mp h).trans (by decide : (0 : ℕ)^2 ≤ 0))
  have eq : ((p+q)/2-b*m^2)^2 < p*q ↔ ((p+q)/2-b*m^2) < ceilSqrt (p*q) := by
    simpa only [not_le] using not_congr (ceilSqrt_le_iff (n := p*q) (a := (p+q)/2-b*m^2)).symm
  rw [eq]
  omega

/-- Among all 253 prime pairs in [128,256), the two-slot decision on N mod 3
covers 210 pairs. Two ordinary midpoints cover 168. Every fixed m≥2 is
eligible on at most 123 pairs even before imposing its midpoint bound. -/
theorem conditional_two_slot_example :
    adviceExamplePairs.length = 253 ∧
    (adviceExamplePairs.filter (fun w => exampleHit w 1 2)).length = 168 ∧
    (adviceExamplePairs.filter (fun w => if (w.1*w.2)%3=1 then exampleHit w 3 1
      else exampleHit w 1 2)).length = 210 ∧
    ((List.range 126).all (fun j =>
      (adviceExamplePairs.filter (fun w => (w.2-w.1)/2 % (j+2) == 0)).length ≤ 123)) = true := by
  unfold adviceExamplePairs
  rw [advicePrimes_values]
  set_option maxRecDepth 10000 in
  decide +kernel

end PrimeFactors
