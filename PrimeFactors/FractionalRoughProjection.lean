import PrimeFactors.CoprimePrefixDiscrepancy
import PrimeFactors.FiniteUnitDensity
import PrimeFactors.MultiplierDivisorReach

/-! Count the possible smaller entries that survive a wheel before testing
exact divisibility. The balanced interval is computed from the product alone. -/

namespace PrimeFactors.FractionalRoughProjection

open Finset NegativeCharacterPrimeCover

/-- If `n = x*y` with `x ≤ y < 2*x`, the smaller entry belongs to this public interval. -/
noncomputable def window (n : ℕ) : Finset ℕ := Ioc (n/2).sqrt n.sqrt

/-- This candidate set uses only the product size and the small-prime wheel. -/
noncomputable def candidates (n w : ℕ) : Finset ℕ :=
  (window n).filter (·.Coprime w)

/-- Exact divisibility in the public interval is equivalent to existence of a balanced partner. -/
theorem factor_iff {n x : ℕ} (positive : 0<n) :
    (x∈window n ∧ x∣n) ↔ ∃ y : ℕ, x≤y ∧ y<2*x ∧ x*y=n := by
  change (x∈Ioc (n/2).sqrt n.sqrt ∧ _) ↔ _
  simp only [mem_Ioc,Nat.sqrt_lt',Nat.le_sqrt',Nat.div_lt_iff_lt_mul (by decide : 0<2)]
  constructor
  · rintro ⟨⟨lower,upper⟩,y,rfl⟩
    have xp : 0<x := Nat.pos_of_mul_pos_right positive
    rw [pow_two] at lower upper
    refine ⟨y,Nat.le_of_mul_le_mul_left upper xp,?_ ,rfl⟩
    exact Nat.lt_of_mul_lt_mul_left (by simpa [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using lower : x*y < x*(2*x))
  · rintro ⟨y,order,balance,rfl⟩
    have xp : 0<x := Nat.pos_of_mul_pos_right positive
    refine ⟨⟨?_,by simpa [pow_two] using Nat.mul_le_mul_left x order⟩,dvd_mul_right ..⟩
    simpa [pow_two,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_lt_mul_of_pos_left balance xp

/-- With a partner at most `B-1`, the smaller entry must be at least
`ceil(n/(B-1))`. For positive n this is one above `floor((n-1)/(B-1))`. -/
theorem capped_factor_iff {n x B : ℕ} (positive : 0<n) (bp : 1<B) :
    (x∈Ioc (max (n/2).sqrt ((n-1)/(B-1))) n.sqrt ∧ x∣n) ↔
      ∃ y : ℕ, x≤y ∧ y<2*x ∧ y<B ∧ x*y=n := by
  have denom : 0<B-1 := by omega
  constructor
  · rintro ⟨hx,dv⟩
    obtain ⟨bottom,top⟩ := mem_Ioc.mp hx
    obtain ⟨lo,cap⟩ := max_lt_iff.mp bottom
    obtain ⟨y,order,bal,prod⟩ := (factor_iff positive).mp ⟨mem_Ioc.mpr ⟨lo,top⟩,dv⟩
    have up := (Nat.div_lt_iff_lt_mul denom).mp cap
    have xp : 0<x := by rw [←prod] at positive; exact Nat.pos_of_mul_pos_right positive
    have bound : x*y≤x*(B-1) := by omega
    have := Nat.le_of_mul_le_mul_left bound xp
    exact ⟨y,order,bal,by omega,prod⟩
  · rintro ⟨y,order,bal,cap,prod⟩
    obtain ⟨bounds,dv⟩ := (factor_iff positive).mpr ⟨y,order,bal,prod⟩
    obtain ⟨lo,top⟩ := mem_Ioc.mp bounds
    have up := Nat.mul_le_mul_left x (by omega : y≤B-1)
    exact ⟨mem_Ioc.mpr ⟨max_lt_iff.mpr ⟨lo,(Nat.div_lt_iff_lt_mul denom).mpr (by omega)⟩,top⟩,dv⟩

/-- When the central product is coprime to the wheel, every exact divisor automatically
passes the wheel. The identity applies to any list of proposed smaller entries. -/
theorem exact_divisors (s : Finset ℕ) {n w : ℕ} (clean : n.Coprime w) :
    (s.filter (·.Coprime w)).filter (·∣n) = s.filter (·∣n) := by
  ext x
  simp only [mem_filter]
  exact ⟨fun h => ⟨h.1.1,h.2⟩, fun h => ⟨⟨h.1,clean.coprime_dvd_left h.2⟩,h.2⟩⟩

private theorem interval_count (w a b : ℕ) (ab : a≤b) :
    ((Ioc a b).filter (·.Coprime w)).card + (units w a).card = (units w b).card := by
  have sets : (Ioc a b).filter (·.Coprime w) ∪ units w a = units w b := by
    ext x
    simp [units,mem_Ioc,mem_Icc]; omega
  have dis : Disjoint ((Ioc a b).filter (·.Coprime w)) (units w a) := by
    rw [disjoint_left]; intro x h k
    have ha := (mem_Ioc.mp (mem_filter.mp h).1).1
    have hb := (mem_Icc.mp (mem_filter.mp k).1).2
    omega
  rw [←card_union_of_disjoint dis,sets]

/-- Subtracting two prefix counts costs at most two copies of the divisor count. -/
theorem interval_lower {w a b : ℕ} (wp : 0<w) (ab : a≤b) :
    ((b:ℝ)-a)*(w.totient:ℝ)/w - 2*(w.divisors.card:ℝ) ≤
      (((Ioc a b).filter (·.Coprime w)).card : ℝ) := by
  have lo := (abs_le.mp (CoprimePrefixDiscrepancy.discrepancy_le_divisors b wp)).1
  have hi := (abs_le.mp (CoprimePrefixDiscrepancy.discrepancy_le_divisors a wp)).2
  have count : (((Ioc a b).filter (·.Coprime w)).card : ℝ) + (units w a).card = (units w b).card := by
    exact_mod_cast interval_count w a b ab
  rw [sub_mul,sub_div]
  linarith

private theorem width {n : ℕ} (full : 2^2047≤n) :
    (n/2).sqrt+2^1021≤n.sqrt := by
  let a := (n/2).sqrt
  let b := n.sqrt
  have floor : 4*2^1021≤b := Nat.le_sqrt'.mpr ((by decide +kernel : (4*2^1021)^2≤(2:ℕ)^2047).trans full)
  have left : 2*a^2≤n := by
    have s := Nat.sqrt_le' (n/2)
    dsimp [a]; omega
  have right : n<(b+1)^2 := Nat.lt_succ_sqrt' n
  change a+2^1021 ≤ b
  by_contra! close
  have move : 3*(b+1)≤4*a := by omega
  have sq := Nat.pow_le_pow_left move 2
  nlinarith only [sq,left,right]

private theorem wheel_cap : primorial 1000*1009 < 2^1770 := by
  let big := quotientBudgetPrimes 1000
  let small := quotientBudgetPrimes 991
  have incl : small ⊆ big := filter_subset_filter _ (range_mono (by decide : 991+1≤1000+1))
  have tail : big \ small ⊆ Icc 992 1000 := by
    intro x hx
    obtain ⟨hi,lo⟩ := mem_sdiff.mp hx
    have prime := (mem_filter.mp hi).2
    have bound := mem_range.mp (mem_filter.mp hi).1
    have low : ¬ x<991+1 := fun h => lo (mem_filter.mpr ⟨mem_range.mpr h,prime⟩)
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  have ct := card_le_card tail
  rw [Nat.card_Icc] at ct
  have diff := card_sdiff_add_card_eq_card incl
  have prior : small.card=167 := quotientBudget_primorial_constants.1
  have size : big.card≤176 := by omega
  have upper : primorial 1000 ≤ 1024^big.card := by
    change (∏ x∈big,x) ≤ _
    simpa using Finset.prod_le_prod' (s:=big) (g:=fun _ => 1024)
      (fun x hx => (mem_range.mp (mem_filter.mp hx).1).le.trans (by decide : 1000+1≤1024))
  exact (Nat.mul_le_mul_right 1009 (upper.trans (Nat.pow_le_pow_right (by decide) size))).trans_lt
    (by decide +kernel)

private theorem population {a b w d k e : ℕ} (wp : 0<w) (ab : a≤b)
    (density : w < d*w.totient) (error : w.divisors.card ≤ 2^e)
    (room : d*(k+2*2^e) < b-a) : k < ((Ioc a b).filter (·.Coprime w)).card := by
  have dp : 0<d := by by_contra! hd; simp [show d=0 by omega] at density
  have share : (1:ℝ)/d < (w.totient:ℝ)/w :=
    (div_lt_div_iff₀ (by exact_mod_cast dp) (by exact_mod_cast wp)).mpr
      (by simpa [mul_comm] using (show (w:ℝ)<d*(w.totient:ℝ) by exact_mod_cast density))
  have main := mul_le_mul_of_nonneg_left share.le (sub_nonneg.mpr (show (a:ℝ)≤b by exact_mod_cast ab))
  have lo := interval_lower wp ab
  rw [mul_div_assoc] at lo
  have limit : (k:ℝ) + 2*2^e < ((b:ℝ)-a)*(1/(d:ℝ)) := by
    rw [←div_eq_mul_one_div]
    apply (lt_div_iff₀ (by exact_mod_cast dp)).mpr
    rw [←Nat.cast_sub ab]
    have numeric : (k+2*2^e)*d < b-a := by rwa [mul_comm]
    exact_mod_cast numeric
  have err : (w.divisors.card:ℝ) ≤ 2^e := by exact_mod_cast error
  have result : (k:ℝ) < (((Ioc a b).filter (·.Coprime w)).card : ℝ) := by linarith
  exact_mod_cast result

private theorem divisor_bound {w C e : ℕ} (wp : 0<w) (cap : w≤C)
    (budget : 9^4*C≤(2^e)^4) : w.divisors.card ≤ 2^e := by
  have bound := (MultiplierDivisorReach.fourth_power_bound wp.ne').trans_le
    ((Nat.mul_le_mul_left _ cap).trans budget)
  by_contra! large
  exact (not_le_of_gt bound) (Nat.pow_le_pow_left large.le 4)

/-- For the wheel covering primes through 1000 together with 1009, every full-size
input leaves more than 2^1017 possible smaller entries before divisibility is tested. -/
theorem full_width {n : ℕ} (full : 2^2047≤n) :
    2^1017 < (candidates n (primorial 1000*1009)).card := by
  have wp := Nat.mul_pos (primorial_pos 1000) (by decide : 0<1009)
  have ratio := FiniteUnitDensity.density wp (wheel_cap.trans (by decide +kernel))
  have span := width full
  exact population wp (Nat.sqrt_le_sqrt (Nat.div_le_self ..)) ratio
    (divisor_bound (e:=450) wp wheel_cap.le (by decide +kernel))
    ((by decide +kernel : 14*(2^1017+2*2^450) < (2:ℕ)^1021).trans_le
      (Nat.le_sub_of_add_le (by simpa only [Nat.add_comm] using span)))

/-- Uniform interval bound with both the wheel and any public modulus. This version
can use the actual endpoints when further information narrows the factor interval. -/
theorem joint_interval {a b m k : ℕ} (mp : 0<m) (ms : m<2^2048)
    (span : 196*(k+2*2^960)<b-a) :
    k < ((Ioc a b).filter (·.Coprime ((primorial 1000*1009)*m))).card := by
  let w := primorial 1000*1009
  have wp : 0<w := Nat.mul_pos (primorial_pos 1000) (by decide)
  have ws : w < 2^1770 := wheel_cap
  have wr := FiniteUnitDensity.density wp (ws.trans (by decide +kernel))
  have mr := FiniteUnitDensity.density mp (ms.trans (by decide +kernel))
  have ratio : w*m < 196*(w*m).totient := calc
    w*m < (14*w.totient)*(14*m.totient) := Nat.mul_lt_mul_of_lt_of_lt wr mr
    _ = 196*(w.totient*m.totient) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.totient_super_multiplicative w m)
  have upper := Nat.mul_le_mul ws.le ms.le
  exact population (Nat.mul_pos wp mp) (Nat.sub_pos_iff_lt.mp ((Nat.zero_le _).trans_lt span)).le ratio
    (divisor_bound (e:=960) (Nat.mul_pos wp mp) upper (by decide +kernel)) span

/-- Even after also rejecting entries not invertible modulo any public positive `m`
below 2^2048, more than 2^1013 possible smaller entries survive the two gcd tests. -/
theorem including_modulus {n m : ℕ} (full : 2^2047≤n) (mp : 0<m) (ms : m<2^2048) :
    2^1013 < (candidates n ((primorial 1000*1009)*m)).card := by
  have span := width full
  exact joint_interval mp ms ((by decide +kernel : 196*(2^1013+2*2^960)<(2:ℕ)^1021).trans_le
    (by omega))

/-- The upper bound on the larger factor only raises the lower endpoint by
so much in the lower half of the 2,048-bit input range. -/
private theorem word_width {n : ℕ} (full : 2^2047≤n) (upper : n≤3*2^2046) :
    (n-1)/(2^1024-1) + 2^1020 ≤ n.sqrt := by
  let b := n.sqrt
  let t : ℕ := 2^1024-1
  have lower : 8*2^1020 + 8≤b := Nat.le_sqrt'.mpr ((by decide +kernel :
    (8*2^1020+8)^2 ≤ (2:ℕ)^2047).trans full)
  have top : b+1≤7*2^1021-1 := Nat.sqrt_lt'.mpr (upper.trans_lt (by decide +kernel))
  have right : n<(b+1)^2 := Nat.lt_succ_sqrt' n
  have scale : 8*(b+1)≤7*t := (Nat.mul_le_mul_left 8 top).trans (by decide +kernel : 8*(7*2^1021-1)≤(7:ℕ)*(2^1024-1))
  have a := Nat.mul_le_mul_right (b+1) scale
  have bound : 8*n < t*(7*(b+1)) := by nlinarith only [right,a]
  have base := Nat.mul_div_le n t
  have both : t*(8*(n/t)) < t*(7*(b+1)) := by nlinarith only [Nat.mul_le_mul_left 8 base,bound]
  have small := Nat.lt_of_mul_lt_mul_left both
  have cut : (n-1)/t≤n/t := Nat.div_le_div_right (Nat.sub_le ..)
  change (n-1)/t + 2^1020 ≤ b
  omega

/-- In the lower half of the 2,048-bit input range the conclusion stays exponential
even when both factors are known to be 1,024-bit numbers. -/
theorem capped_word_population {n m : ℕ} (full : 2^2047≤n) (upper : n≤3*2^2046)
    (mp : 0<m) (ms : m<2^2048) :
    2^1012 < ((Ioc (max (n/2).sqrt ((n-1)/(2^1024-1))) n.sqrt).filter
      (·.Coprime ((primorial 1000*1009)*m))).card := by
  have size := width full
  have cap := word_width full upper
  have both : max (n/2).sqrt ((n-1)/(2^1024-1)) + 2^1020 ≤ n.sqrt := by omega
  exact joint_interval mp ms ((by decide +kernel : 196*(2^1012+2*2^960)<(2:ℕ)^1020).trans_le
    (by omega))

end PrimeFactors.FractionalRoughProjection
