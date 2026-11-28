import PrimeFactors.FloorShiftDyadicCenters
import PrimeFactors.CeilingShiftPopulation
import PrimeFactors.SquareRootPhasePopulation

/-! Exact centers at which the full power of two dividing a positive Fermat
square excess gives the remaining distance to the true prime sum. -/
namespace PrimeFactors.CeilingShiftDyadicDistances

open Finset FloorSquareShift

def proposed (n m : ℕ) := 2*m+twoPart (m^2-n)

private theorem twoPart_iff {D j : ℕ} (pos : 0<D) :
    twoPart D=2^j ↔ D ≡ 2^j [MOD 2^(j+1)] := by
  have power : 0<2^j := by positivity
  rw [pow_succ]
  constructor
  · obtain ⟨i,u,odd,form⟩ := Nat.exists_eq_two_pow_mul_odd pos.ne'
    rw [mul_comm (2^i) u] at form
    rw [form,twoPart_odd_mul i odd]
    intro eqn
    obtain rfl : i=j := Nat.pow_right_injective (by decide : 2≤2) eqn
    obtain ⟨t,ht⟩ := odd
    rw [ht,show (2*t+1)*2^i=2^i+(2^i*2)*t by ring]
    simp [Nat.ModEq]
  · intro eqn
    have small : 2^j<2^j*2 := by omega
    have rem : D%(2^j*2)=2^j := Eq.trans eqn (Nat.mod_eq_of_lt small)
    have form := Nat.mod_add_div D (2^j*2)
    rw [rem] at form
    have witness : D=(2*(D/(2^j*2))+1)*2^j := form.symm.trans (by ring)
    rw [witness,twoPart_odd_mul j (show Odd (2*(D/(2^j*2))+1) from ⟨_,rfl⟩)]

private theorem square_mod_eight (d : ℕ) :
    d^2%8 = if d%2=1 then 1 else if d%4=2 then 4 else 0 := by
  have compare : ∀ a : Fin 8, a.val^2%8=if a.val%2=1 then 1 else if a.val%4=2 then 4 else 0 := by decide
  have val := compare ⟨d%8,Nat.mod_lt _ (by decide)⟩
  change (d%8)^2%8=_ at val
  rw [Nat.pow_mod]
  simpa only [Nat.mod_mod_of_dvd _ (by decide : 2∣8),Nat.mod_mod_of_dvd _ (by decide : 4∣8)] using val

private theorem branches {M d D k : ℕ} (dp : 0<D) (odd : Odd (M+d))
    (shape : D+2^(k+1)*M=d^2+(2^k)^2) :
    twoPart D=2^(k+1) ↔
      (k=0 ∧ d%2=1) ∨ (k=1 ∧ d%4=2) ∨ (2≤k ∧ 2^(k+2)∣d^2) := by
  have oddM := Nat.odd_iff.mp odd
  have sq := square_mod_eight d
  rw [twoPart_iff dp]
  rcases k with _|k
  · norm_num [Nat.ModEq] at shape ⊢
    split_ifs at sq <;> omega
  rcases k with _|j
  · norm_num [Nat.ModEq] at shape ⊢
    split_ifs at sq <;> omega
  let k := j+2
  let Q := 2^(k+1)
  have qp : 0<Q := by dsimp [Q]; positivity
  have twice : 2^(k+2)=Q+Q := by dsimp [Q]; rw [show k+2=k+1+1 by omega,pow_succ]; omega
  have big : Q+Q ∣ (2^k)^2 := by
    rw [←twice,←pow_mul]
    exact pow_dvd_pow 2 (by dsimp [k]; omega)
  change D+Q*M=d^2+(2^k)^2 at shape
  change D ≡ Q [MOD 2^(k+2)] ↔ _
  simp only [Nat.add_eq_zero_iff, Nat.reduceEqDiff, Nat.reduceLeDiff, false_and, false_or,
    true_and,and_false]
  change D ≡ Q [MOD 2^(k+2)] ↔ 2^(k+2)∣d^2
  rw [twice]
  have aux : D+Q*M ≡ d^2 [MOD Q+Q] := by
    rw [shape]
    simpa only [Nat.add_zero] using (Nat.modEq_zero_iff_dvd.mpr big).add_left (d^2)
  have Qeven : 2∣Q := by
    dsimp [Q]; rw [pow_succ]; exact dvd_mul_left ..
  by_cases even : d%2=0
  · have mo : Odd M := Nat.odd_iff.mpr (by omega)
    obtain ⟨a,ma⟩ := mo
    have phase : Q*M ≡ Q [MOD Q+Q] := by
      rw [ma,show Q*(2*a+1)=Q+(Q+Q)*a by ring]
      simp [Nat.ModEq]
    have both : D+Q ≡ d^2 [MOD Q+Q] := (phase.add_left D).symm.trans aux
    have zero : Q+Q ≡ 0 [MOD Q+Q] := Nat.modEq_zero_iff_dvd.mpr dvd_rfl
    constructor
    · intro hit
      exact Nat.modEq_zero_iff_dvd.mp (both.symm.trans ((hit.add_right Q).trans zero))
    · intro dv
      exact Nat.ModEq.add_right_cancel' Q (both.trans ((Nat.modEq_zero_iff_dvd.mpr dv).trans zero.symm))
  · have sqodd : d^2%2=1 := by rw [Nat.pow_mod]; rw [show d%2=1 by omega]
    have div2 : 2∣Q+Q := dvd_add Qeven Qeven
    have qm : Q*M ≡ 0 [MOD 2] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left Qeven M)
    have dmod : D ≡ d^2 [MOD 2] := by
      simpa only [Nat.add_zero] using (qm.add_left D).symm.trans (aux.of_dvd div2)
    have bad : ¬ 2∣d^2 := by rw [Nat.dvd_iff_mod_eq_zero]; omega
    refine iff_of_false (fun hit => ?_) (fun dv => bad (div2.trans dv))
    exact bad (Nat.modEq_zero_iff_dvd.mp
      (dmod.symm.trans ((hit.of_dvd div2).trans (Nat.modEq_zero_iff_dvd.mpr Qeven))))

private theorem residue_shape {v d u : ℕ} (factor : d=2^v*u) (odd : Odd u) :
    (d%2=1 ↔ v=0) ∧ (d%4=2 ↔ v=1) := by
  obtain ⟨a,ua⟩ := odd
  rcases v with _|v
  · rw [factor,pow_zero,one_mul,ua]; omega
  rcases v with _|v
  · rw [factor,ua]; norm_num; omega
  · have f : d=4*(2^v*u) := by rw [factor,pow_succ,pow_succ]; ring
    omega

/-- Here m is a proposed midpoint whose square lies above the public
product, at dyadic distance 2^k below the actual factor midpoint. -/
theorem classify {p q m k v u : ℕ} (lt : p<q) (op : Odd p) (oq : Odd q)
    (above : p*q<m^2) (atMid : (p+q)/2=m+2^k)
    (factor : (q-p)/2=2^v*u) (odd : Odd u) :
    proposed (p*q) m=p+q ↔
      (k=0 ∧ v=0) ∨ (k=1 ∧ v=1) ∨ (2≤k ∧ k+2≤2*v) := by
  let M := (p+q)/2
  let d := (q-p)/2
  have sum : 2*M=p+q := by obtain ⟨a,ha⟩ := op; obtain ⟨b,hb⟩ := oq; dsimp [M]; omega
  have gap : p+2*d=q := by obtain ⟨a,ha⟩ := op; obtain ⟨b,hb⟩ := oq; dsimp [d]; omega
  have half : M+d=q := by omega
  have diff : m^2-(p*q)+p*q=m^2 := Nat.sub_add_cancel above.le
  have id : M^2=p*q+d^2 := by
    have mp : M=p+d := by omega
    rw [mp,←gap]; ring
  have shape : m^2-p*q+2^(k+1)*M=d^2+(2^k)^2 := by
    change M=m+2^k at atMid
    rw [atMid] at id ⊢
    rw [show 2^(k+1)=2^k*2 from pow_succ ..]
    nlinarith only [diff,id]
  have raw := branches (Nat.sub_pos_of_lt above) (half.symm ▸ oq) shape
  obtain ⟨low,one⟩ := residue_shape factor odd
  have big : 2^(k+2)∣d^2 ↔ k+2≤2*v := by
    change (q-p)/2=2^v*u at factor
    change d=2^v*u at factor
    rw [factor,mul_pow,←pow_mul]
    have cop := (odd.coprime_two_left.pow_left (k+2)).pow_right 2
    constructor
    · intro dv
      have bound := Nat.le_of_dvd (by positivity : 0<(2:ℕ)^(v*2)) (cop.dvd_of_dvd_mul_right dv)
      have := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp bound
      omega
    · intro le
      exact dvd_mul_of_dvd_left (pow_dvd_pow 2 (by omega : k+2≤v*2)) _
  change d%2=1 ↔ v=0 at low
  change d%4=2 ↔ v=1 at one
  rw [low,one,big] at raw
  have same : p+q=2*m+2^(k+1) := by rw [pow_succ]; omega
  rw [proposed,same,Nat.add_right_inj]; exact raw

private theorem half_pos {p q : ℕ} (lt : p<q) (op : Odd p) (oq : Odd q) : 0<(q-p)/2 := by
  obtain ⟨a,pa⟩ := op
  obtain ⟨b,qb⟩ := oq
  omega

/-- Every successful pre-hit reading has a dyadic distance. -/
theorem distance_of_hit {p q m : ℕ} (op : Odd p) (oq : Odd q)
    (hit : proposed (p*q) m=p+q) : ∃ k, (p+q)/2=m+2^k := by
  obtain ⟨j,hj,_⟩ := FloorShiftDyadicCenters.power_divisor (m^2-p*q)
  obtain ⟨a,pa⟩ := op
  obtain ⟨b,qb⟩ := oq
  rw [proposed,hj] at hit
  cases j with
  | zero => simp only [pow_zero] at hit; omega
  | succ k => exact ⟨k,by rw [pow_succ] at hit; omega⟩

/-- If all four preceding integer midpoints are above sqrt(N), one of
the distances 1, 2 or 4 gives the true sum. -/
theorem short_read {p q : ℕ} (lt : p<q) (op : Odd p) (oq : Odd q)
    (room : 4≤(p+q)/2) (above : p*q<((p+q)/2-4)^2) :
    ∃ m : ℕ, p*q<m^2 ∧ ((p+q)/2-m=1 ∨ (p+q)/2-m=2 ∨ (p+q)/2-m=4) ∧
      proposed (p*q) m=p+q := by
  obtain ⟨v,u,odd,fac⟩ := Nat.exists_eq_two_pow_mul_odd (half_pos lt op oq).ne'
  let k := min v 2
  have digits : (2:ℕ)^k=1 ∨ 2^k=2 ∨ 2^k=4 := by
    have sk : k≤2 := Nat.min_le_right _ _
    interval_cases k <;> decide
  let m := (p+q)/2-2^k
  have mk : (p+q)/2=m+2^k := by dsimp [m]; omega
  have before : p*q<m^2 := above.trans_le (Nat.pow_le_pow_left (by dsimp [m]; omega) 2)
  refine ⟨m,before,by omega,(classify lt op oq before mk fac odd).mpr ?_⟩
  dsimp [k]
  omega

/-- Count the available room from the public first Fermat midpoint.
For a nonsquare product, the square excess there is strictly positive. -/
theorem short_from_ceil {p q : ℕ} (lt : p<q) (op : Odd p) (oq : Odd q)
    (nonsquare : ¬IsSquare (p*q)) (room : ceilSqrt (p*q)+4≤(p+q)/2) :
    ∃ m : ℕ, p*q<m^2 ∧ ((p+q)/2-m=1 ∨ (p+q)/2-m=2 ∨ (p+q)/2-m=4) ∧
      proposed (p*q) m=p+q := by
  apply short_read lt op oq (by omega)
  have b := ceilSqrt_le_iff.mp (by omega : ceilSqrt (p*q)≤(p+q)/2-4)
  exact lt_of_le_of_ne b (fun h => nonsquare ⟨_,by simpa only [sq] using h⟩)

/-- A successful reading jumping at least 2^K requires 2^t to divide
the factor difference whenever 2*t≤K+4. -/
theorem gap_divisor {p q m K t : ℕ} (lt : p<q) (op : Odd p) (oq : Odd q)
    (above : p*q<m^2) (hit : proposed (p*q) m=p+q) (large : 2^K≤(p+q)/2-m)
    (Klo : 2≤K) (level : 2*t≤K+4) : 2^t∣q-p := by
  obtain ⟨k,dist⟩ := distance_of_hit op oq hit
  obtain ⟨v,u,odd,fac⟩ := Nat.exists_eq_two_pow_mul_odd (half_pos lt op oq).ne'
  have kd := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (by simpa only [dist,Nat.add_sub_cancel_left] using large)
  have cases := (classify lt op oq above dist fac odd).mp hit
  have powdvd := pow_dvd_pow 2 (by omega : t≤v+1)
  have gap : q-p=2^(v+1)*u := by
    obtain ⟨a,pa⟩ := op
    obtain ⟨b,qb⟩ := oq
    rw [pow_succ]
    have twice : q-p=2*((q-p)/2) := by omega
    calc _ = 2*((q-p)/2) := twice
         _ = _ := by rw [fac]; ring
  exact gap ▸ dvd_mul_of_dvd_left powdvd u

open MixedPrefixSample
open private PrimeFactors.MixedPrefixSample.mem_sample PrimeFactors.MixedPrefixSample.mem_primes
  from PrimeFactors.MixedPrefixSample
set_option exponentiation.threshold 8192
attribute [local irreducible] eligible MixedPrefixSample.primes

/-- The entire public interval above the square root is granted for each input. -/
noncomputable def longHits (K : ℕ) : Finset (ℕ×ℕ) := by
  classical exact eligible.filter fun z => ∃ m : ℕ, z.1*z.2<m^2 ∧
    proposed (z.1*z.2) m=z.1+z.2 ∧ 2^K≤(z.1+z.2)/2-m

private theorem long_count {K t c : ℕ} (lo : 2≤K) (level : 2*t≤K+4)
    (width : 2^t*2^c=X) : (longHits K).card≤primes.card*2^c := by
  classical
  let menu := (primes ×ˢ range (2^c)).image (fun w => (w.1,w.1+2^t*w.2))
  have sub : longHits K ⊆ menu := by
    rintro ⟨p,q⟩ h
    obtain ⟨el,m,above,hit,large⟩ := mem_filter.mp h
    obtain ⟨op,oq⟩ := CeilingShiftPopulation.odd_factors el
    rw [eligible] at el
    obtain ⟨ord,lt⟩ := PrimeFactors.MixedPrefixSample.mem_sample.mp el
    obtain ⟨pm,qm,_,_,_⟩ := mem_ordered.mp ord
    have low := (PrimeFactors.MixedPrefixSample.mem_primes.mp pm).1.1
    have high := (PrimeFactors.MixedPrefixSample.mem_primes.mp qm).1.2
    dsimp only at above hit large low high lt op oq
    obtain ⟨i,eqn⟩ := gap_divisor lt op oq above hit large lo level
    have below : 2^t*i<2^t*2^c := by rw [width,←eqn]; omega
    exact mem_image.mpr ⟨(p,i),mem_product.mpr ⟨pm,mem_range.mpr (Nat.lt_of_mul_lt_mul_left below)⟩,
      Prod.ext rfl (by dsimp; omega)⟩
  exact (card_le_card sub).trans (card_image_le.trans_eq (by simp only [card_product,card_range]))

private theorem prevalence {K t c e : ℕ} (lo : 2≤K) (level : 2*t≤K+4)
    (width : 2^t*2^c=X) (price : 41056*(2^e*2^c)≤X) :
    2^e*(longHits K).card < eligible.card := by
  apply Nat.lt_of_mul_lt_mul_left (a:=41056)
  calc
    _ ≤ 41056*(2^e*(primes.card*2^c)) := Nat.mul_le_mul_left 41056
      (Nat.mul_le_mul_left _ (long_count lo level width))
    _ = (41056*(2^e*2^c))*primes.card := by ac_rfl
    _ ≤ X*primes.card := Nat.mul_le_mul_right _ price
    _ < _ := SquareRootPhasePopulation.marginal

/-- The denominator is all eligible full-width prime pairs in each bound. -/
theorem full_width :
    2^50*(longHits 128).card < eligible.card ∧ 2^242*(longHits 512).card < eligible.card :=
  ⟨prevalence (t:=66) (c:=957) (by decide) (by decide) (by decide +kernel) (by decide +kernel),
   prevalence (t:=258) (c:=765) (by decide) (by decide) (by decide +kernel) (by decide +kernel)⟩

/-- Distance sixteen succeeds; at distance thirty-two the excess remains
positive and its power of two gives a wrong sum. -/
theorem control : Nat.Prime 523 ∧ Nat.Prime 1019 ∧ 523*1019=532937 ∧ (523+1019)/2=771 ∧
    (1019-523)/2=2^3*31 ∧ 771-755=16 ∧ 771-739=32 ∧
    755^2-532937=37088 ∧ 739^2-532937=13184 ∧
    proposed 532937 755=1542 ∧ proposed 532937 739=1606 ∧ 1606≠523+1019 := by
  have a : twoPart 37088=32 := by
    rw [show 37088=1159*2^5 by decide,twoPart_odd_mul _ (by decide : Odd 1159)]
    decide
  have b : twoPart 13184=128 := by
    rw [show 13184=103*2^7 by decide,twoPart_odd_mul _ (by decide : Odd 103)]
    decide
  refine ⟨by norm_num,by norm_num,by decide,by decide,by decide,by decide,by decide,
    by decide,by decide,?_,?_,by decide⟩
  · rw [proposed,show 755^2-532937=37088 by decide,a]
  · rw [proposed,show 739^2-532937=13184 by decide,b]

end PrimeFactors.CeilingShiftDyadicDistances
