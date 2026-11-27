import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.NumberTheory.Harmonic.Bounds
import PrimeFactors.JacobiSeparation
import PrimeFactors.FrobeniusFixedCounts
import PrimeFactors.BoundedSmoothCount
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Average over group sizes before choosing any discriminant or prime pair.
If the projected group has order r, a uniform element is killed by E
with probability gcd(r,E)/r. Its reciprocal is an integer k. -/
namespace PrimeFactors.SmoothSignedPairs
open Finset

def reduced (P Q : ℕ) := P / P.gcd Q

def residual (P Q E : ℕ) :=
  reduced P Q / (reduced P Q).gcd E

/-- Probability of a local hit for a uniform element of the projected cyclic group. -/
noncomputable def weight (P Q E : ℕ) : ℚ := ((residual P Q E : ℕ) : ℚ)⁻¹

private theorem reconstruct (P Q E : ℕ) :
    P.gcd Q * (reduced P Q).gcd E * residual P Q E = P := by
  rw [residual,mul_assoc,Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)]
  exact Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)

theorem local_fraction {P Q E : ℕ} (hp : 0<P) :
    weight P Q E = ((reduced P Q).gcd E : ℚ) / reduced P Q := by
  have d := Nat.gcd_dvd_left P Q
  have rpos : 0<reduced P Q := Nat.div_pos (Nat.le_of_dvd hp d) (Nat.gcd_pos_of_pos_left _ hp)
  have vpos := Nat.gcd_pos_of_pos_left E rpos
  have kpos : 0<residual P Q E := Nat.div_pos (Nat.le_of_dvd rpos (Nat.gcd_dvd_left ..)) vpos
  have h : residual P Q E * (reduced P Q).gcd E = reduced P Q :=
    Nat.div_mul_cancel (Nat.gcd_dvd_left ..)
  have eq : (residual P Q E : ℚ) * ((reduced P Q).gcd E : ℚ) = reduced P Q := by exact_mod_cast h
  have kn : (residual P Q E : ℚ)≠0 := by exact_mod_cast kpos.ne'
  have vn : ((reduced P Q).gcd E : ℚ)≠0 := by exact_mod_cast vpos.ne'
  unfold weight
  rw [←eq]
  field_simp

/-- Allow an arbitrary public first exponent z with the same gcd as the
other group size. The equality counts exactly the original cyclic group
elements whose projected E-th power is the identity. -/
theorem cyclic_fraction (G : Type*) [Group G] [IsCyclic G] [Fintype G] [DecidableEq G]
    {P Q z E : ℕ} (size : Fintype.card G=P) (same : P.gcd z=P.gcd Q) :
    (((univ.filter (fun u : G => u^(z*E)=1)).card : ℚ)/P = weight P Q E) := by
  have pp : 0<P := size ▸ Fintype.card_pos
  let g := P.gcd z
  let r := P/g
  let c := z/g
  have gp : 0<g := Nat.gcd_pos_of_pos_left z pp
  have eqp : g*r=P := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have eqz : g*c=z := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  have cop : c.Coprime r := (Nat.coprime_div_gcd_div_gcd gp).symm
  have key : (z*E).gcd P=g*(E.gcd r) := calc
    _ = (g*(c*E)).gcd (g*r) := by rw [←mul_assoc,eqz,eqp]
    _ = _ := by rw [Nat.gcd_mul_left,Nat.Coprime.gcd_mul_left_cancel E cop]
  rw [FrobeniusFixedCounts.cyclic_count,size,key,local_fraction pp]
  have eqr : reduced P Q=r := by simp [reduced,r,g,same]
  rw [eqr,Nat.gcd_comm E r,Nat.cast_mul]
  have peq : (g:ℚ)*r=P := by exact_mod_cast eqp
  rw [←peq]
  have gn : (g:ℚ)≠0 := by exact_mod_cast gp.ne'
  exact mul_div_mul_left _ _ gn

/-- For one opposite group size Q, encode the starting size P by its shared
divisor, its smooth part killed by E, and the surviving order k. -/
theorem fixed_other {U B Q E : ℕ} (qp : 0<Q) (smooth : E ∈ Nat.smoothNumbers B) :
    ∑ P ∈ Icc 1 U, weight P Q E ≤
      (Q.divisors.card : ℚ) * (Nat.smoothNumbersUpTo U B).card * harmonic U := by
  classical
  let inputs := Icc 1 U
  let code := fun P : ℕ => (P.gcd Q,(reduced P Q).gcd E,residual P Q E)
  let box := Q.divisors ×ˢ (Nat.smoothNumbersUpTo U B ×ˢ inputs)
  let w := fun v : ℕ × ℕ × ℕ => (v.2.2 : ℚ)⁻¹
  have inside : inputs.image code ⊆ box := by
    intro c hc
    obtain ⟨P,hP,rfl⟩ := mem_image.mp hc
    obtain ⟨pp,pu⟩ := mem_Icc.mp hP
    have rpos : 0<reduced P Q := Nat.div_pos (Nat.le_of_dvd pp (Nat.gcd_dvd_left ..))
      (Nat.gcd_pos_of_pos_left _ pp)
    have vpos := Nat.gcd_pos_of_pos_left E rpos
    have ident := Nat.gcd_dvd_left (reduced P Q) E
    have ru : reduced P Q≤U := (Nat.div_le_self ..).trans pu
    apply mem_product.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right ..,qp.ne'⟩,mem_product.mpr ⟨?_,?_⟩⟩
    · exact Nat.mem_smoothNumbersUpTo.mpr ⟨(Nat.le_of_dvd rpos ident).trans ru,
        Nat.mem_smoothNumbers_of_dvd smooth (Nat.gcd_dvd_right ..)⟩
    · exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd rpos ident) vpos,(Nat.div_le_self ..).trans ru⟩
  have inj : Function.Injective code := by
    intro a b h
    have eq := congrArg (fun v : ℕ × ℕ × ℕ => v.1*v.2.1*v.2.2) h
    simpa only [code,reconstruct] using eq
  calc
    _ = ∑ v ∈ inputs.image code, w v := (sum_image (fun _ _ _ _ eq => inj eq)).symm
    _ ≤ ∑ v ∈ box, w v := sum_le_sum_of_subset_of_nonneg inside (fun _ _ _ => by dsimp [w]; positivity)
    _ = _ := by
      simp [box,inputs,w,sum_product,harmonic_eq_sum_Icc]
      ring

/-- Average divisor count with the exact harmonic majorant. -/
theorem divisor_sum (U : ℕ) : (∑ Q ∈ Icc 1 U, (Q.divisors.card:ℚ)) ≤ U*harmonic U := by
  classical
  let I := Icc 1 U
  have count (q : ℕ) (hq : q∈I) : q.divisors=I.filter (·∣q) := by
    obtain ⟨pos,high⟩ := mem_Icc.mp hq
    ext d
    simp only [Nat.mem_divisors,mem_filter,mem_Icc,I]
    exact ⟨fun h => ⟨⟨Nat.pos_of_dvd_of_pos h.1 pos,(Nat.le_of_dvd pos h.1).trans high⟩,h.1⟩,
      fun h => ⟨h.2,by omega⟩⟩
  have multiples (d : ℕ) : (I.filter (d∣·)).card=U/d := by
    have eq : I=Ioc 0 U := by ext x; simp [I]; omega
    rw [eq,Nat.Ioc_filter_dvd_card_eq_div]
  calc
    _ = ∑ q ∈ I, ∑ d ∈ I, (if d∣q then (1:ℚ) else 0) := by
      apply sum_congr rfl
      intro q hq
      rw [count q hq,←sum_filter]
      simp
    _ = ∑ d ∈ I, ((U/d:ℕ):ℚ) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro d _
      rw [←sum_filter]
      simp [multiples]
    _ ≤ ∑ d ∈ I, (U:ℚ)/d := sum_le_sum (fun _ _ => Nat.cast_div_le)
    _ = _ := by simp [I,harmonic_eq_sum_Icc,mul_sum,div_eq_mul_inv]

/-- Sum of the local hit probabilities over the entire square of possible
group sizes. It therefore also bounds any subset, including shifted primes. -/
theorem mass_bound {U B E : ℕ} (smooth : E∈Nat.smoothNumbers B) :
    (∑ Q ∈ Icc 1 U, ∑ P ∈ Icc 1 U, weight P Q E) ≤
      U*(Nat.smoothNumbersUpTo U B).card*(harmonic U)^2 := by
  have hh : 0≤harmonic U := by rw [harmonic_eq_sum_Icc]; positivity
  calc
    _ ≤ ∑ Q ∈ Icc 1 U, (Q.divisors.card : ℚ) * (Nat.smoothNumbersUpTo U B).card * harmonic U :=
      sum_le_sum fun _ hq => fixed_other (mem_Icc.mp hq).1 smooth
    _ = (∑ Q ∈ Icc 1 U,(Q.divisors.card:ℚ)) * (Nat.smoothNumbersUpTo U B).card * harmonic U := by
      simp only [sum_mul]
    _ ≤ (U*harmonic U)*(Nat.smoothNumbersUpTo U B).card*harmonic U := by
      gcongr
      exact divisor_sum U
    _ = _ := by ring

private theorem image_mass {A : Type*} (inputs : Finset A) (coord : A → ℕ × ℕ)
    {U B E : ℕ} (smooth : E∈Nat.smoothNumbers B)
    (inside : ∀ a∈inputs, coord a∈Icc 1 U ×ˢ Icc 1 U)
    (inj : Set.InjOn coord inputs) :
    (∑ a ∈ inputs, weight (coord a).1 (coord a).2 E) ≤
      U*(Nat.smoothNumbersUpTo U B).card*(harmonic U)^2 := by
  classical
  let w := fun v : ℕ × ℕ => weight v.1 v.2 E
  calc
    _ = ∑ v ∈ inputs.image coord, w v := (sum_image inj).symm
    _ ≤ ∑ v ∈ Icc 1 U ×ˢ Icc 1 U, w v :=
      sum_le_sum_of_subset_of_nonneg (image_subset_iff.mpr inside)
        (fun _ _ _ => by dsimp [w,weight]; positivity)
    _ = ∑ Q ∈ Icc 1 U, ∑ P ∈ Icc 1 U, weight P Q E := by
      rw [sum_product,sum_comm]
    _ ≤ _ := mass_bound smooth

/-- Either coordinate and all four sign choices are allowed, even if the
discriminant is selected after inspecting the product. A uniform trial
conditional on a nonidentity projection costs at most a further factor two
when the two signed group sizes differ. -/
theorem signed_mass (inputs : Finset (ℕ × ℕ)) {U B E : ℕ}
    (smooth : E∈Nat.smoothNumbers B)
    (fits : ∀ v∈inputs, 1<v.1 ∧ v.1<U ∧ 1<v.2 ∧ v.2<U) :
    ∑ v ∈ inputs, ∑ s : Bool, ∑ t : Bool,
      (weight (signedTorusOrder v.1 s) (signedTorusOrder v.2 t) E +
       weight (signedTorusOrder v.2 t) (signedTorusOrder v.1 s) E) ≤
      8*(U*(Nat.smoothNumbersUpTo U B).card*(harmonic U)^2) := by
  let M : ℚ := U*(Nat.smoothNumbersUpTo U B).card*(harmonic U)^2
  have one (s t swap : Bool) :
      ∑ v ∈ inputs, (let p:=signedTorusOrder v.1 s
                     let q:=signedTorusOrder v.2 t
                     if swap then weight q p E else weight p q E) ≤ M := by
    let coord := fun v : ℕ × ℕ =>
      let p:=signedTorusOrder v.1 s
      let q:=signedTorusOrder v.2 t
      if swap then (q,p) else (p,q)
    have range' : ∀ v∈inputs, coord v ∈ Icc 1 U ×ˢ Icc 1 U := by
      intro v hv
      obtain ⟨_,_,_,_⟩ := fits v hv
      cases swap <;> cases s <;> cases t <;> simp [coord,signedTorusOrder] <;> omega
    have unique : Set.InjOn coord inputs := by
      intro v hv w hw eq
      obtain ⟨_,_,_,_⟩ := fits v hv
      obtain ⟨_,_,_,_⟩ := fits w hw
      cases swap <;> cases s <;> cases t <;>
        simp only [coord,signedTorusOrder,Bool.false_eq_true,↓reduceIte,Prod.mk.injEq] at eq <;>
        exact Prod.ext (by omega) (by omega)
    have h := image_mass inputs coord smooth range' unique
    cases swap <;> simpa only [coord,Bool.false_eq_true,↓reduceIte,M] using h
  have bounds (s t : Bool) :
      ∑ v∈inputs, (weight (signedTorusOrder v.1 s) (signedTorusOrder v.2 t) E +
        weight (signedTorusOrder v.2 t) (signedTorusOrder v.1 s) E) ≤ 2*M := by
    rw [sum_add_distrib,two_mul]
    exact add_le_add (one s t false) (one s t true)
  change _ ≤ 8*M
  simp only [Fintype.sum_bool, sum_add_distrib] at bounds ⊢
  linarith only [bounds false false,bounds false true,bounds true false,bounds true true]

/-- An input-dependent smooth exponent can only kill elements already killed
by the universal prime-power schedule at the group-size cap. -/
theorem dominated_by_schedule {P Q E U B : ℕ} (pos : 0<P) (fits : P≤U)
    (smooth : E∈Nat.smoothNumbers (B+1)) :
    weight P Q E ≤ weight P Q (ReducedSmoothReadout.schedule B U).prod := by
  rw [local_fraction pos,local_fraction pos]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  let r := reduced P Q
  have rp : 0<r := Nat.div_pos (Nat.le_of_dvd pos (Nat.gcd_dvd_left ..)) (Nat.gcd_pos_of_pos_left _ pos)
  have div := Nat.gcd_dvd_left r E
  have d := Nat.gcd_pos_of_pos_left E rp
  have small := Nat.mem_smoothNumbers'.mp (Nat.mem_smoothNumbers_of_dvd smooth (Nat.gcd_dvd_right r E))
  apply Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ rp) (Nat.dvd_gcd div ?_)
  exact ReducedSmoothReadout.smooth_dvd_schedule d ((Nat.le_of_dvd rp div).trans
    ((Nat.div_le_self ..).trans fits)) (fun l h hl => Nat.lt_succ_iff.mp (small l h hl))

/-- Every prime power in the universal schedule is itself smooth. -/
theorem smooth_schedule (B U : ℕ) : (ReducedSmoothReadout.schedule B U).prod ∈ Nat.smoothNumbers (B+1) := by
  apply Nat.mem_smoothNumbers'.mpr
  intro l prime div
  let xs := ReducedSmoothReadout.schedule B U
  obtain ⟨e,he,le⟩ := prime.prime.exists_mem_multiset_dvd (s:=(xs:Multiset ℕ)) div
  change e ∈ xs at he
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp he
  simp only [List.mem_filter,List.mem_range,decide_eq_true_eq] at hr
  have eq := (Nat.prime_dvd_prime_iff_eq prime hr.2.1).mp (prime.dvd_of_dvd_pow le)
  exact eq ▸ hr.1

set_option maxRecDepth 4096
set_option exponentiation.threshold 2048

/-- Count all four signed pairs, both coordinates, and a factor of two for
conditioning on a surviving projected element. The hypothesis on the number
of products is the explicit prime-count input to the full-size estimate. -/
theorem full_size (inputs : Finset (ℕ × ℕ))
    (fits : ∀ v∈inputs, 1<v.1 ∧ v.1<2^1024 ∧ 1<v.2 ∧ v.2<2^1024)
    (population : 2^2021 ≤ inputs.card) :
    let E := (ReducedSmoothReadout.schedule 1000 (2^1024)).prod
    2^677*(2*(∑ v ∈ inputs, ∑ s : Bool, ∑ t : Bool,
      (weight (signedTorusOrder v.1 s) (signedTorusOrder v.2 t) E +
       weight (signedTorusOrder v.2 t) (signedTorusOrder v.1 s) E))) < inputs.card := by
  intro E
  have total := signed_mass inputs (smooth_schedule 1000 (2^1024)) fits
  have hi : harmonic (2^1024) ≤ (711:ℚ) := by
    have h := harmonic_le_one_add_log (2^1024)
    rw [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow] at h
    have num : (harmonic (2^1024) : ℝ) ≤ 711 := h.trans (by
      norm_num only [Nat.cast_ofNat]
      linarith only [Real.log_two_lt_d9])
    exact_mod_cast num
  have hpos : 0 ≤ harmonic (2^1024) := by
    rw [harmonic_eq_sum_Icc]
    exact sum_nonneg fun i _ => inv_nonneg.mpr (Nat.cast_nonneg i)
  have sc : ((Nat.smoothNumbersUpTo (2^1024) 1001).card:ℚ) ≤ 2^297 := by
    exact_mod_cast BoundedSmoothCount.smooth_1024.le
  have den : (2:ℚ)^2021 ≤ inputs.card := by exact_mod_cast population
  apply lt_of_lt_of_le _ den
  calc
    _ ≤ 2^677*(2*(8*((2:ℚ)^1024*2^297*711^2))) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (total.trans ?_) (by norm_num)) (by positivity)
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul (mul_le_mul_of_nonneg_left sc (by positivity)) (pow_le_pow_left₀ hpos hi 2)
        (sq_nonneg _) (by positivity)
    _ < _ := by norm_num

end PrimeFactors.SmoothSignedPairs
