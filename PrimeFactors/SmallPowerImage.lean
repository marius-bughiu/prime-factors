import PrimeFactors.PowerImageDenominator
import PrimeFactors.PowerImageSupport
import PrimeFactors.ReducedSlopes

/-! For an arbitrary sparse set of successful powered residues, the finite
sample bound combines an image-size estimate with rational approximation. -/
namespace PrimeFactors.SmallPowerImage

open Finset
set_option maxHeartbeats 800000
set_option exponentiation.threshold 8192

private theorem small_error {p q b : ℕ} (p2 : 2≤p) (q2 : 2≤q) (pW : p<2^1024)
    (qW : q<2^1024) (width : 2^2047≤p*q) (bd : b≤2^510) :
    2*b^2*(p*q-(p-1)*(q-1)) < (p-1)*(q-1) := by
  have eq := PowerImageWidth.offset (p:=p) (q:=q) (by omega) (by omega)
  have dist : p*q-(p-1)*(q-1)<2^1025 := by omega
  have low : 2^2046≤(p-1)*(q-1) := by omega
  calc
    _ ≤ (2*(2^510)^2)*(p*q-(p-1)*(q-1)) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left bd 2))
    _ < (2*(2^510)^2)*2^1025 := Nat.mul_lt_mul_of_pos_left dist (by decide +kernel)
    _ = 2^2046 := by decide +kernel
    _ ≤ _ := low

/-- If powering is effective at reaching a set of at most 2^20
residue pairs, the true totient ratio appears among the convergents. The
exponent may depend on the product, but is fixed across the seed count. -/
theorem recover {p q E : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (pW : p<2^1024) (qW : q<2^1024) (width : 2^2047≤p*q)
    (common : (p-1).gcd (q-1)≤2^80) (ep : 0<E) (en : E≤p*q)
    (S : Finset ((ZMod p)ˣ × (ZMod q)ˣ)) (cap : S.card≤2^20)
    (raw : (p-1)*(q-1)≤PowerImageSupport.successes E S * 2^410) :
    ∃ i, let f := ((E : ℝ)/(p*q : ℕ)).convergent i
      f=(E : ℚ)/((p-1)*(q-1) : ℕ) ∧ (f:ℚ)≠0 := by
  let P := p-1
  let Q := q-1
  have pc := (Nat.prime_iff_card_units p).mp hp.out
  have qc := (Nat.prime_iff_card_units q).mp hq.out
  have pp : 0<P := Nat.sub_pos_of_lt hp.out.one_lt
  have qp : 0<Q := Nat.sub_pos_of_lt hq.out.one_lt
  rw [←pc,←qc] at raw
  have rate := PowerImageSupport.rate E (2^410) S raw
  rw [pc,qc] at rate
  have xp := PoweredOrderCounts.image_pos P E pp
  have yp := PoweredOrderCounts.image_pos Q E qp
  let b := ((E:ℚ)/(P*Q:ℕ)).den
  have div : b ∣ P.gcd Q*(P/P.gcd E*(Q/Q.gcd E)) :=
    PowerImageDenominator.ratio_denominator pp qp
  have gp : 0<P.gcd Q := Nat.gcd_pos_of_pos_left Q pp
  have bd : b≤2^510 := calc
    b ≤ P.gcd Q*(P/P.gcd E*(Q/Q.gcd E)) := Nat.le_of_dvd (Nat.mul_pos gp (Nat.mul_pos xp yp)) div
    _ ≤ 2^80*(2^20*2^410) :=
      Nat.mul_le_mul common (rate.trans (Nat.mul_le_mul_right _ cap))
    _ = _ := by decide +kernel
  have small := small_error hp.out.two_le hq.out.two_le pW qW width bd
  obtain ⟨i,eq⟩ := PowerImageDenominator.convergent (Nat.mul_pos pp qp)
    (Nat.mul_le_mul (Nat.sub_le ..) (Nat.sub_le ..)) en le_rfl small
  exact ⟨i,eq.symm,eq ▸ div_ne_zero (by exact_mod_cast ep.ne')
    (by exact_mod_cast (Nat.mul_pos pp qp).ne')⟩

/-- All positive divisors of the product predecessor have small kernels
when the two prime predecessors have small gcd. This gives a simultaneous
bound for every such exponent and every sparse set of outputs. -/
theorem predecessor {p q E : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (pW : p<2^1024) (qW : q<2^1024) (width : 2^2047≤p*q)
    (common : (p-1).gcd (q-1)≤2^80) (de : E∣p*q-1)
    (S : Finset ((ZMod p)ˣ × (ZMod q)ˣ)) (cap : S.card≤2^20) :
    PowerImageSupport.successes E S * 2^1866 ≤ (p-1)*(q-1) := by
  classical
  have one_side {a b : ℕ} (ap : 0<a) (bp : 0<b) (div : E∣a*b-1) :
      (a-1).gcd E ∣ (a-1).gcd (b-1) := by
    rw [←gcd_predecessor_product ap bp]
    exact Nat.dvd_gcd (Nat.gcd_dvd_left ..) ((Nat.gcd_dvd_right ..).trans div)
  have gpos := Nat.gcd_pos_of_pos_left (q-1) (Nat.sub_pos_of_lt hp.out.one_lt)
  have pker := (Nat.le_of_dvd gpos (one_side hp.out.pos hq.out.pos de)).trans common
  have qdiv := one_side hq.out.pos hp.out.pos (by simpa only [Nat.mul_comm q p] using de)
  rw [Nat.gcd_comm (q-1) (p-1)] at qdiv
  have qker := (Nat.le_of_dvd gpos qdiv).trans common
  have rc : (PowerImageSupport.reachable E S).card≤2^20 :=
    (PowerImageSupport.reachable_card_le E S).trans cap
  have dist := PowerImageWidth.offset hp.out.pos hq.out.pos
  have low : 2^2046≤(p-1)*(q-1) := by omega
  rw [PowerImageSupport.exact_count,(Nat.prime_iff_card_units p).mp hp.out,
    (Nat.prime_iff_card_units q).mp hq.out]
  calc
    _ ≤ (2^80*2^80*2^20)*2^1866 := Nat.mul_le_mul_right _
      (Nat.mul_le_mul (Nat.mul_le_mul pker qker) rc)
    _ = 2^2046 := by decide +kernel
    _ ≤ _ := low

end PrimeFactors.SmallPowerImage
