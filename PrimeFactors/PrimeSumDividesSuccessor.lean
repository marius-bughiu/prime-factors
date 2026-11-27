import PrimeFactors.ChebyshevPrimeSample
import PrimeFactors.SmoothSignedPairs
import PrimeFactors.IntermediateShiftedExponent

/-! Count sorted prime pairs whose sum divides one more than their product.
The numerator is bounded by counting odd integer pairs and requires no prime-distribution estimate. -/
namespace PrimeFactors.PrimeSumDividesSuccessor

open Finset MixedPrefixSample
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

theorem remove_common {n a b : ℕ} (np : 0<n) (d : n∣a*b) :
    n/n.gcd a∣b := by
  let g := n.gcd a
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ np
  have ng : g*(n/g)=n := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have ag : g*(a/g)=a := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  have both : g*(n/g)∣g*((a/g)*b) := by rwa [ng,←Nat.mul_assoc,ag]
  exact (Nat.coprime_div_gcd_div_gcd gp).dvd_of_dvd_mul_left
    ((Nat.mul_dvd_mul_iff_left gp).mp both)

private def modulus (s : ℕ) := s/s.gcd 2

/-- With s=(p+q)/2 and a=(p−1)/2, the smaller odd factor is encoded by
a root of a(a+1)=0 modulo s/gcd(s,2), with a below that modulus. -/
theorem half_root {p q : ℕ} (po : Odd p) (qo : Odd q) (lt : p<q) (hit : p+q∣p*q+1) :
    let s := (p+q)/2
    let a := (p-1)/2
    a<s/s.gcd 2 ∧ s/s.gcd 2∣a*(a+1) := by
  let s := (p+q)/2
  let a := (p-1)/2
  obtain ⟨u,hu⟩ := po
  obtain ⟨v,hv⟩ := qo
  have peq : p=2*a+1 := by dsimp only [a]; omega
  have seq : 2*s=p+q := by dsimp only [s]; omega
  have sp : 0<s := by omega
  have eq : (p+q)*p=(p*q+1)+2*(2*(a*(a+1))) := by rw [peq]; ring
  have d := Nat.dvd_sub (dvd_mul_right (p+q) p) hit
  rw [eq,Nat.add_sub_cancel_left,←seq] at d
  have reduced := remove_common sp ((Nat.mul_dvd_mul_iff_left (by decide : 0<2)).mp d)
  have bound : s≤2*(s/s.gcd 2) := calc
    s=s.gcd 2*(s/s.gcd 2) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left s 2)).symm
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_of_dvd (by decide) (Nat.gcd_dvd_right s 2))
  change a<s/s.gcd 2 ∧ _
  exact ⟨by omega,reduced⟩

private theorem same_code {t x y : ℕ} (tp : 0<t) (xt : x<t) (yt : y<t)
    (xr : t∣x*(x+1)) (yr : t∣y*(y+1)) (eq : t.gcd x=t.gcd y) : x=y := by
  let d := t.gcd x
  let e := t/d
  have dx : d∣x := Nat.gcd_dvd_right ..
  have dy : d∣y := by dsimp only [d]; rw [eq]; exact Nat.gcd_dvd_right t y
  have ex : e∣x+1 := remove_common tp xr
  have ey : e∣y+1 := by simpa only [e,d,eq] using remove_common tp yr
  have cop : d.Coprime e :=
    ((Nat.coprime_self_add_right.mpr (Nat.coprime_one_right x)).of_dvd_left dx).of_dvd_right ex
  have product : d*e=t := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have step {a b : ℕ} (al : a<t) (bl : b<t) (da : d∣a) (db : d∣b)
      (ea : e∣a+1) (eb : e∣b+1) : ¬a<b := by
    intro l
    have diff : e∣b-a := by simpa using Nat.dvd_sub eb ea
    have div := cop.mul_dvd_of_dvd_of_dvd (Nat.dvd_sub db da) diff
    rw [product] at div
    have := Nat.le_of_dvd (Nat.sub_pos_of_lt l) div
    omega
  exact Nat.le_antisymm (Nat.le_of_not_gt (step yt xt dy dx ey ex))
    (Nat.le_of_not_gt (step xt yt dx dy ex ey))

private def halfSum (z : ℕ×ℕ) := (z.1+z.2)/2
private def halfPred (p : ℕ) := (p-1)/2

/-- Count any set of qualifying sorted odd pairs, using divisor totals for
the half-sum instead of counting all residue classes modulo p+q. -/
theorem count {pairs : Finset (ℕ×ℕ)} {U : ℕ}
    (valid : ∀ z∈pairs, Odd z.1 ∧ Odd z.2 ∧ z.1<z.2 ∧ z.2≤U ∧ z.1+z.2∣z.1*z.2+1) :
    pairs.card≤∑ s∈Icc 1 U, s.divisors.card := by
  classical
  let code (z : ℕ×ℕ) := (halfSum z,(modulus (halfSum z)).gcd (halfPred z.1))
  let box := (Icc 1 U).biUnion fun s => s.divisors.image (fun d => (s,d))
  have small : pairs.card≤box.card := by
    apply card_le_card_of_injOn code
    · intro z hz
      obtain ⟨op,oq,lt,top,_⟩ := valid z hz
      obtain ⟨u,hu⟩ := op
      obtain ⟨v,hv⟩ := oq
      have low : 0<halfSum z := by dsimp only [halfSum]; omega
      have cap : halfSum z≤U := by dsimp only [halfSum]; omega
      have div : (modulus (halfSum z)).gcd (halfPred z.1)∣halfSum z :=
        (Nat.gcd_dvd_left ..).trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left ..))
      exact mem_biUnion.mpr ⟨halfSum z,mem_Icc.mpr ⟨low,cap⟩,mem_image.mpr
        ⟨_,Nat.mem_divisors.mpr ⟨div,low.ne'⟩,rfl⟩⟩
    · rintro ⟨p,q⟩ h ⟨r,s⟩ h' eq
      obtain ⟨op,oq,lt,_,dv⟩ := valid _ h
      obtain ⟨or',os,lt',_,dv'⟩ := valid _ h'
      obtain ⟨al,ar⟩ := half_root op oq lt dv
      obtain ⟨bl,br⟩ := half_root or' os lt' dv'
      have se : (p+q)/2=(r+s)/2 := congrArg Prod.fst eq
      have de := congrArg Prod.snd eq
      change (((p+q)/2)/((p+q)/2).gcd 2).gcd ((p-1)/2)=
        (((r+s)/2)/((r+s)/2).gcd 2).gcd ((r-1)/2) at de
      simp only at al ar bl br
      rw [←se] at bl br de
      have ae := same_code (by omega) al bl ar br de
      obtain ⟨u,hu⟩ := op
      obtain ⟨v,hv⟩ := oq
      obtain ⟨u',hu'⟩ := or'
      obtain ⟨v',hv'⟩ := os
      dsimp only at hu hv hu' hv' ae
      exact Prod.ext (by omega) (by omega)
  apply small.trans
  apply card_biUnion_le.trans
  exact sum_le_sum fun _ _ => card_image_le

/-- The exceptional event on the repository's uniform sorted prime-pair sample. -/
noncomputable def hits := eligible.filter fun z => z.1+z.2∣z.1*z.2+1

attribute [local irreducible] MixedPrefixSample.primes MixedPrefixSample.ordered
  MixedPrefixSample.sample MixedPrefixSample.eligible hits

private theorem props {z : ℕ×ℕ} (hz : z∈eligible) :
    Odd z.1 ∧ Odd z.2 ∧ z.1<z.2 ∧ z.2≤2^1024 := by
  rw [eligible,sample,mem_filter] at hz
  obtain ⟨both,lt⟩ := hz
  obtain ⟨p,q,_⟩ := (mem_ordered (E:=fun _ => True) (z:=z)).mp both
  rw [primes,mem_filter,mem_Ico] at p q
  obtain ⟨⟨plo,phi⟩,pp⟩ := p
  obtain ⟨⟨qlo,qhi⟩,qp⟩ := q
  have lower : 2<X := by decide +kernel
  have upper : 2*X=2^1024 := by decide +kernel
  exact ⟨pp.odd_of_ne_two (by omega),qp.odd_of_ne_two (by omega),lt,by omega⟩

theorem total_bound {U C : ℕ} (bound : harmonic U≤(C:ℚ)) :
    (∑ s∈Icc 1 U, s.divisors.card)≤C*U := by
  have r := (SmoothSignedPairs.divisor_sum U).trans (mul_le_mul_of_nonneg_left bound (Nat.cast_nonneg U))
  rw [Nat.mul_comm]
  exact_mod_cast r

/-- The count of actual successes at 2048 bits is at most 711·2^1024. -/
theorem hits_count : hits.card≤711*2^1024 := by
  have cap := count (pairs:=hits) (U:=2^1024) (by
    intro z hz
    rw [hits,mem_filter] at hz
    obtain ⟨mem,h⟩ := hz
    obtain ⟨p,q,lt,high⟩ := props (z:=z) mem
    exact ⟨p,q,lt,high,h⟩)
  have upper : harmonic (2^1024)≤(711:ℚ) := by
    have log := harmonic_le_one_add_log (2^1024)
    rw [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow] at log
    have realBound : (harmonic (2^1024):ℝ)≤711 := log.trans (by
      norm_num only [Nat.cast_ofNat]
      linarith only [Real.log_two_lt_d9])
    exact_mod_cast realBound
  exact cap.trans (total_bound (U:=2^1024) (C:=711) upper)

/-- A fraction strictly below 2^-988 can meet the necessary condition for
a nontrivial readout from any divisor of N+1. -/
theorem eligible_fraction : 2^988*hits.card<eligible.card := by
  have count := Nat.mul_le_mul_left (21000000*2^988) hits_count
  have numeric : (21000000*2^988)*(711*2^1024)≤2^2046 := by decide +kernel
  apply Nat.lt_of_mul_lt_mul_left (a:=21000000)
  simpa only [Nat.mul_assoc] using (count.trans numeric).trans_lt ChebyshevPrimeSample.eligible_count

/-- A true intermediate ratio from an E dividing N+1 but not F forces the
prime sum to divide N+1. This separates the structural event from direct E|F hits. -/
theorem forced {p q E : ℕ} (pp : 1<p) (qp : 1<q) (ep : 0<E)
    (div : E∣p*q+1) (hit : IntermediateTotientObstruction.Hit (p*q) E ((p-1)*(q-1)))
    (extra : ¬E∣(p-1)*(q-1)) : p+q∣p*q+1 := by
  have total : (p-1)*(q-1)+(p+q)=p*q+1 := by
    have a : p-1+1=p := by omega
    have b : q-1+1=q := by omega
    nlinarith only [congrArg (fun z => z*(q-1)) a,congrArg (fun z => p*z) b,a]
  have fn : (p-1)*(q-1)<p*q := by omega
  have eq := IntermediateShiftedExponent.forced_gcd ep fn (by omega : 1≤p*q-(p-1)*(q-1))
    div hit extra
  rw [show p*q-(p-1)*(q-1)+1=p+q by omega] at eq
  exact (eq ▸ Nat.gcd_dvd_left E ((p-1)*(q-1))).trans div

open Classical in
/-- Applied to every exponent at once. An arbitrary N-dependent selection
of divisors of N+1 cannot enlarge this nontrivial-hit event. -/
theorem all_exponents_fraction :
    2^988*(eligible.filter (fun z => ∃ E : ℕ, 0<E ∧ E∣z.1*z.2+1 ∧
      IntermediateTotientObstruction.Hit (z.1*z.2) E ((z.1-1)*(z.2-1)) ∧
      ¬E∣(z.1-1)*(z.2-1))).card<eligible.card := by
  classical
  apply (Nat.mul_le_mul_left _ (card_le_card (t:=hits) ?_)).trans_lt eligible_fraction
  intro z hz
  obtain ⟨inside,E,ep,dv,h,extra⟩ := mem_filter.mp hz
  have elo := inside
  rw [eligible,sample,mem_filter] at elo
  obtain ⟨p,q,_⟩ := (mem_ordered (E:=fun _ => True) (z:=z)).mp elo.1
  rw [primes,mem_filter] at p q
  rw [hits,mem_filter]
  exact ⟨inside,forced p.2.one_lt q.2.one_lt ep dv h extra⟩

end PrimeFactors.PrimeSumDividesSuccessor
