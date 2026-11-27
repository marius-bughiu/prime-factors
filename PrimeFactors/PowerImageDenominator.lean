import PrimeFactors.ContinuedSquare
import PrimeFactors.PoweredOrderCounts
import PrimeFactors.PowerImageWidth

/-! If a fixed exponent concentrates a uniform seed onto a small image, the
ratio of that exponent to the totient has a correspondingly small denominator.
The estimate below applies to a list of at most 48 winning image elements. -/
namespace PrimeFactors.PowerImageDenominator

/-- The product of the two image indices divides a public multiple of the
original exponent when an upper multiple of the common group divisor is given. -/
theorem kernel_product {P Q E : ℕ} :
    P.gcd E * Q.gcd E ∣ P.gcd Q * E := by
  let a := P.gcd E
  let b := Q.gcd E
  have common : a.gcd b ∣ P.gcd Q := Nat.dvd_gcd
    ((Nat.gcd_dvd_left a b).trans (Nat.gcd_dvd_left P E))
    ((Nat.gcd_dvd_right a b).trans (Nat.gcd_dvd_left Q E))
  have period : a.lcm b ∣ E := Nat.lcm_dvd (Nat.gcd_dvd_right P E) (Nat.gcd_dvd_right Q E)
  change a*b ∣ _
  rw [←Nat.gcd_mul_lcm]
  exact Nat.mul_dvd_mul common period

/-- In lowest terms E/(P*Q) has denominator dividing gcd(P,Q) times
the product of the two image sizes. -/
theorem denominator_dvd {P Q E a b : ℕ} (cop : a.Coprime b)
    (eq : E*b=a*(P*Q)) :
    b ∣ P.gcd Q * ((P/P.gcd E)*(Q/Q.gcd E)) := by
  let X := P/P.gcd E
  let Y := Q/Q.gcd E
  have hp : X * P.gcd E = P := Nat.div_mul_cancel (Nat.gcd_dvd_left P E)
  have hq : Y * Q.gcd E = Q := Nat.div_mul_cancel (Nat.gcd_dvd_left Q E)
  have div : P*Q ∣ E*(P.gcd Q*(X*Y)) := by
    have k := Nat.mul_dvd_mul_left (X*Y) (kernel_product (P:=P) (Q:=Q) (E:=E))
    have split : P*Q=X*Y*(P.gcd E*Q.gcd E) := calc
      P*Q=(X*P.gcd E)*(Y*Q.gcd E) := congrArg₂ Nat.mul hp.symm hq.symm
      _ = _ := by ring
    rw [split]
    convert k using 1
    ring
  obtain ⟨z,hz⟩ := div
  by_cases zero : E=0
  · by_cases prod : P*Q=0
    · rcases Nat.mul_eq_zero.mp prod with h|h <;> simp [h]
    · have az : a=0 := (Nat.mul_eq_zero.mp (by simpa [zero] using eq.symm)).resolve_right prod
      have bo : b=1 := by simpa [az] using cop
      simp [bo]
  · have cancel : a*(P.gcd Q*(X*Y)) = b*z := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero zero)
      calc E*(a*(P.gcd Q*(X*Y))) = a*(E*(P.gcd Q*(X*Y))) := by ring
           _ = (a*(P*Q))*z := by rw [hz]; ring
           _ = E*(b*z) := by rw [←eq]; ring
    exact cop.symm.dvd_of_dvd_mul_left ⟨z,cancel⟩

theorem ratio_denominator {P Q E : ℕ} (p : 0<P) (q : 0<Q) :
    ((E : ℚ)/(P*Q : ℕ)).den ∣ P.gcd Q * ((P/P.gcd E)*(Q/Q.gcd E)) := by
  let F := P*Q
  have fp : 0<F := Nat.mul_pos p q
  let g := E.gcd F
  have gp : 0<g := Nat.gcd_pos_of_pos_right E fp
  have cop : (E/g).Coprime (F/g) := Nat.coprime_div_gcd_div_gcd gp
  have ea : E/g*g=E := Nat.div_mul_cancel (Nat.gcd_dvd_left E F)
  have fb : F/g*g=F := Nat.div_mul_cancel (Nat.gcd_dvd_right E F)
  have eq : E*(F/g)=(E/g)*F := calc
    E*(F/g)=(E/g*g)*(F/g) := congrArg (·*(F/g)) ea.symm
    _ = (E/g)*(F/g*g) := by ring
    _ = _ := congrArg (E/g*·) fb
  have h := denominator_dvd (P:=P) (Q:=Q) cop eq
  change ((E : ℚ)/F).den ∣ _
  have den : ((E : ℚ)/F).den=F/g := by
    rw [show (E : ℚ)/F = Rat.divInt (E : ℤ) (F : ℤ) by simp [Rat.divInt_eq_div],Rat.den_mk]
    simp [g,fp.ne',Int.gcd]
  rwa [den]

/-- Legendre's criterion, applied to a positive exponent and the totient
of a balanced product. The numerator and denominator here are abstract. -/
theorem convergent {N F E b : ℕ} (fp : 0<F) (fn : F≤N) (en : E≤N)
    (bd : (((E : ℚ)/F).den)≤b) (small : 2*b^2*(N-F)<F) :
    ∃ i, (E : ℚ)/F = ((E : ℝ)/N).convergent i := by
  let f : ℚ := (E : ℚ)/F
  have Np : 0<N := fp.trans_le fn
  have er : (E : ℝ)≤N := by exact_mod_cast en
  have fr : (0:ℝ)<F := by exact_mod_cast fp
  have nr : (0:ℝ)<N := by exact_mod_cast Np
  have sub : ((N-F : ℕ):ℝ)=(N:ℝ)-F := Nat.cast_sub fn
  have diff : (f:ℝ)-(E:ℝ)/N = (E:ℝ)/N * ((N-F : ℕ):ℝ)/F := by
    simp only [f,Rat.cast_div,Rat.cast_natCast,sub]
    field_simp
    ring
  have dpos : 0<f.den := f.pos
  have db : 2*f.den^2*(N-F)<F :=
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left bd 2))).trans_lt small
  have close : ((N-F : ℕ):ℝ)/F < 1/(2*(f.den:ℝ)^2) := by
    apply (div_lt_div_iff₀ fr (by positivity)).mpr
    exact_mod_cast (by nlinarith only [db] : (N-F)*(2*f.den^2)<1*F)
  apply Real.exists_rat_eq_convergent
  rw [abs_sub_comm,abs_of_nonneg (by rw [diff]; positivity),diff]
  calc
    (E:ℝ)/N*((N-F:ℕ):ℝ)/F ≤ 1*((N-F:ℕ):ℝ)/F := by
      gcongr
      exact (div_le_one nr).mpr er
    _ < _ := by simpa using close

/-- For the two specific winning order classes, a sufficient probability of
success implies that the exact exponent/totient ratio appears among the
convergents of the exponent/product ratio. -/
theorem rate_convergent {p q E : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (wp : p<2^1024) (wq : q<2^1024) (width : 2^2047≤p*q) (g : (p-1).gcd (q-1)=2)
    (en : E≤p*q)
    (raw : (p-1)*(q-1)≤(Finset.univ.filter (fun z : (ZMod p)ˣ × (ZMod q)ˣ =>
      (orderOf (z.1^E)=7 ∨ orderOf (z.1^E)=14) ∧ orderOf (z.2^E)=8)).card*2^503) :
    ∃ i, (E : ℚ)/((p-1)*(q-1) : ℕ) = ((E : ℝ)/(p*q : ℕ)).convergent i := by
  have pc := (Nat.prime_iff_card_units p).mp hp.out
  have qc := (Nat.prime_iff_card_units q).mp hq.out
  have p2 := hp.out.two_le
  have q2 := hq.out.two_le
  have pp : 0<p-1 := by omega
  have qp : 0<q-1 := by omega
  rw [←pc,←qc] at raw
  have rate := PoweredOrderCounts.trace_rate (ZMod p)ˣ (ZMod q)ˣ E (2^503) raw
  dsimp only at rate
  rw [pc,qc] at rate
  have den := ratio_denominator (E:=E) pp qp
  have small := PowerImageWidth.from_rate p2 q2 wp wq width g
    (PoweredOrderCounts.image_pos _ E pp) (PoweredOrderCounts.image_pos _ E qp)
    (PoweredOrderCounts.trace_cap _ _) rate (by simpa only [Nat.mul_assoc] using den)
  exact convergent (Nat.mul_pos pp qp)
    (Nat.mul_le_mul (Nat.sub_le ..) (Nat.sub_le ..)) en le_rfl small

end PrimeFactors.PowerImageDenominator
