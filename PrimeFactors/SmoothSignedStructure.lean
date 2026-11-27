import PrimeFactors.SmoothSignedPairs

/-! Count products for which an entire signed reduced group order is smooth,
even when the two signs can be selected with knowledge of both factors. -/
namespace PrimeFactors.SmoothSignedStructure
open Finset SmoothSignedPairs

set_option exponentiation.threshold 2048
set_option maxRecDepth 2048

/-- Any of the four independent local signs and either reduced group order. -/
def Admits (B : ℕ) (v : ℕ × ℕ) : Prop :=
  ∃ s t : Bool, let P := signedTorusOrder v.1 s
                let Q := signedTorusOrder v.2 t
                reduced P Q ∈ Nat.smoothNumbers B ∨ reduced Q P ∈ Nat.smoothNumbers B

/-- The qualifying first group sizes with second group size fixed at Q. -/
noncomputable def slice (U B Q : ℕ) : Finset ℕ := by
  classical exact (Icc 1 U).filter fun P => reduced P Q ∈ Nat.smoothNumbers B

/-- A smooth reduced size reconstructs P when multiplied by its common
divisor with Q. There are at most tau(Q) choices for that first coordinate. -/
theorem fixed_other {U B Q : ℕ} (pos : 0<Q) :
    (slice U B Q).card ≤ Q.divisors.card*(Nat.smoothNumbersUpTo U B).card := by
  classical
  let code := fun P : ℕ => (P.gcd Q,reduced P Q)
  rw [←card_product]
  apply card_le_card_of_injOn code
  · intro P hP
    obtain ⟨hP,h⟩ := mem_filter.mp hP
    exact mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right ..,pos.ne'⟩,
      Nat.mem_smoothNumbersUpTo.mpr ⟨(Nat.div_le_self ..).trans (mem_Icc.mp hP).2,h⟩⟩
  · intro a _ b _ eq
    have rec (P : ℕ) : (code P).1*(code P).2=P := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
    exact (rec a).symm.trans ((congrArg (fun u : ℕ × ℕ => u.1*u.2) eq).trans (rec b))

private noncomputable def pairs (U B : ℕ) : Finset (ℕ×ℕ) :=
  (Icc 1 U).biUnion fun Q => (slice U B Q).image fun P => (P,Q)

private theorem mem_pairs {U B P Q : ℕ} (p : P∈Icc 1 U) (q : Q∈Icc 1 U)
    (hit : reduced P Q∈Nat.smoothNumbers B) : (P,Q)∈pairs U B :=
  mem_biUnion.mpr ⟨Q,q,mem_image.mpr ⟨P,mem_filter.mpr ⟨p,hit⟩,rfl⟩⟩

private theorem count_pairs (U B : ℕ) :
    ((pairs U B).card:ℚ) ≤ U*harmonic U*(Nat.smoothNumbersUpTo U B).card := by
  classical
  have upper : (pairs U B).card ≤ (∑ Q ∈ Icc 1 U,Q.divisors.card)*(Nat.smoothNumbersUpTo U B).card := by
    rw [sum_mul]
    apply (card_biUnion_le).trans
    exact sum_le_sum fun Q hQ => card_image_le.trans (fixed_other (mem_Icc.mp hQ).1)
  calc
    _ ≤ (∑ Q ∈ Icc 1 U,(Q.divisors.card:ℚ))*(Nat.smoothNumbersUpTo U B).card := by exact_mod_cast upper
    _ ≤ _ := mul_le_mul_of_nonneg_right (divisor_sum U) (Nat.cast_nonneg _)

private def undo (s : Bool) (P : ℕ) := if s then P+1 else P-1

private theorem undo_order {p : ℕ} (h : 1<p) (s : Bool) : undo s (signedTorusOrder p s) = p := by
  cases s <;> simp [undo,signedTorusOrder]
  omega

private theorem reduce_scale {k : ℕ} (pos : 0<k) (x y : ℕ) :
    reduced (k*x) (k*y)=reduced x y := by
  unfold reduced
  rw [Nat.gcd_mul_left,Nat.mul_div_mul_left _ _ pos]

private theorem orient {B U k p q : ℕ} (pos : 0<k) (hp : 1<p) (hq : 1<q)
    (s t : Bool) (a : signedTorusOrder p s∈Icc 1 (k*U)) (b : signedTorusOrder q t∈Icc 1 (k*U))
    (da : k∣signedTorusOrder p s) (db : k∣signedTorusOrder q t)
    (hit : reduced (signedTorusOrder p s) (signedTorusOrder q t)∈Nat.smoothNumbers B) :
    ∃ z∈pairs U B, (undo s (k*z.1),undo t (k*z.2))=(p,q) := by
  obtain ⟨x,he⟩ := da
  obtain ⟨y,hf⟩ := db
  rw [he] at a
  rw [hf] at b
  rw [he,hf,reduce_scale pos] at hit
  have interval (v : ℕ) (h : k*v∈Icc 1 (k*U)) : v∈Icc 1 U := by
    obtain ⟨hl,hu⟩ := mem_Icc.mp h
    exact mem_Icc.mpr ⟨Nat.pos_of_mul_pos_left hl, Nat.le_of_mul_le_mul_left hu pos⟩
  exact ⟨(x,y),mem_pairs (interval _ a) (interval _ b) hit, by simp [←he,←hf,undo_order hp,undo_order hq]⟩

private theorem cover {F : Type*} [Fintype F] {S : Finset (ℕ×ℕ)} (T : Finset (ℕ×ℕ))
    (decode : F → ℕ×ℕ → ℕ×ℕ) (hits : ∀ v∈S, ∃ f w, w∈T ∧ decode f w=v) :
    S.card ≤ Fintype.card F*T.card := by
  classical
  have incl : S ⊆ univ.biUnion (fun f : F => T.image (decode f)) := by
    intro v hv
    obtain ⟨f,w,hw,eq⟩ := hits v hv
    exact mem_biUnion.mpr ⟨f,mem_univ _,mem_image.mpr ⟨w,hw,eq⟩⟩
  exact (card_le_card incl).trans (card_biUnion_le_card_mul _ _ _ (fun _ _ => card_image_le))

private def decoded (k : ℕ) (f : Bool×Bool) (z : ℕ×ℕ) := (undo f.1 (k*z.1),undo f.2 (k*z.2))

private theorem witness {B U k p q : ℕ} (pos : 0<k)
    (hp : 1<p) (hq : 1<q)
    (rowp : ∀ s, signedTorusOrder p s∈Icc 1 (k*U) ∧ k∣signedTorusOrder p s)
    (rowq : ∀ t, signedTorusOrder q t∈Icc 1 (k*U) ∧ k∣signedTorusOrder q t)
    (h : Admits B (p,q)) :
    ∃ f z, z∈pairs U B ∧ (decoded k f z=(p,q) ∨ decoded k f z=(q,p)) := by
  obtain ⟨s,t,hit|hit⟩ := h
  · obtain ⟨z,hz,eq⟩ := orient pos hp hq s t (rowp s).1 (rowq t).1 (rowp s).2 (rowq t).2 hit
    exact ⟨(s,t),z,hz,Or.inl eq⟩
  · obtain ⟨z,hz,eq⟩ := orient pos hq hp t s (rowq t).1 (rowp s).1 (rowq t).2 (rowp s).2 hit
    exact ⟨(t,s),z,hz,Or.inr eq⟩

/-- Without an ordering or a parity restriction, four sign choices and
two possible orientations cost a factor of eight. -/
theorem signed_count {U B : ℕ} (S : Finset (ℕ×ℕ))
    (fits : ∀ v∈S, 1<v.1 ∧ v.1<U ∧ 1<v.2 ∧ v.2<U)
    (hits : ∀ v∈S, Admits B v) :
    (S.card:ℚ) ≤ 8*(U*harmonic U*(Nat.smoothNumbersUpTo U B).card) := by
  have bound (p : ℕ) (lo : 1<p) (hi : p<U) (s : Bool) :
      signedTorusOrder p s∈Icc 1 (1*U) ∧ 1∣signedTorusOrder p s := by
    cases s <;> simp [signedTorusOrder] <;> omega
  let decode := fun (f : (Bool×Bool)×Bool) (z : ℕ×ℕ) =>
    if f.2 then (decoded 1 f.1 z).swap else decoded 1 f.1 z
  have cnt := cover (S:=S) (pairs U B) decode (by
    intro v hv
    obtain ⟨p,ph,q,qh⟩ := fits v hv
    obtain ⟨f,z,hz,a|a⟩ := witness (by decide : 0<1) p q (bound _ p ph) (bound _ q qh) (hits v hv)
    · exact ⟨(f,false),z,hz,a⟩
    · exact ⟨(f,true),z,hz,by simp [decode,a]⟩)
  have old : S.card≤8*(pairs U B).card := by simpa using cnt
  exact (show (S.card:ℚ) ≤ 8*((pairs U B).card:ℚ) by exact_mod_cast old).trans
    (mul_le_mul_of_nonneg_left (count_pairs U B) (by norm_num))

private theorem harmonic_cap (j : ℕ) (le : j≤1024) : harmonic (2^j)≤(711:ℚ) := by
  have h := harmonic_le_one_add_log (2^j)
  rw [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow] at h
  have j' : (j:ℝ)≤1024 := by exact_mod_cast le
  have l := mul_le_mul (a:=(j:ℝ)) (c:=Real.log 2) j' Real.log_two_lt_d9.le
    (Real.log_nonneg (by norm_num)) (by norm_num)
  exact_mod_cast h.trans (show 1+(j:ℝ)*Real.log 2≤711 by linarith only [l])

/-- Applies to any recorded successes and any independently supplied lower
bound on the eligible population. -/
theorem full_size (S : Finset (ℕ×ℕ)) {population : ℕ} (den : 2^2021≤population)
    (fits : ∀ v∈S, 1<v.1 ∧ v.1<2^1024 ∧ 1<v.2 ∧ v.2<2^1024)
    (hits : ∀ v∈S, Admits 1001 v) : 2^687*S.card<population := by
  have count := signed_count S fits hits
  have hi := harmonic_cap 1024 le_rfl
  have room : ((Nat.smoothNumbersUpTo (2^1024) 1001).card:ℚ)≤2^297 := by
    exact_mod_cast BoundedSmoothCount.smooth_1024.le
  suffices (2:ℚ)^687*S.card<2^2021 by exact (show 2^687*S.card<2^2021 by exact_mod_cast this).trans_le den
  calc
    _ ≤ (2:ℚ)^687*(8*((2:ℚ)^1024*711*2^297)) := by
      apply mul_le_mul_of_nonneg_left (count.trans _) (by positivity)
      simp only [Nat.cast_pow,Nat.cast_ofNat]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (mul_le_mul_of_nonneg_left hi (by positivity)) room (Nat.cast_nonneg _) (by positivity))
        (by norm_num)
    _ < _ := by norm_num

/-- For two odd factors both neighboring sizes are even. Divide the sizes
by two before encoding their ratio. If the inputs are canonically ordered,
sorting the decoded pair recovers the input in either orientation. -/
theorem sorted_odd_count {U B : ℕ} (S : Finset (ℕ×ℕ))
    (fits : ∀ v∈S, 1<v.1 ∧ v.1<v.2 ∧ v.2<2*U ∧ Odd v.1 ∧ Odd v.2)
    (hits : ∀ v∈S, Admits B v) :
    (S.card:ℚ) ≤ 4*(U*harmonic U*(Nat.smoothNumbersUpTo U B).card) := by
  have bound (p : ℕ) (lo : 1<p) (hi : p<2*U) (odd : Odd p) (s : Bool) :
      signedTorusOrder p s∈Icc 1 (2*U) ∧ 2∣signedTorusOrder p s := by
    obtain ⟨k,hk⟩ := odd
    cases s <;> simp only [signedTorusOrder,Bool.false_eq_true,↓reduceIte,mem_Icc] <;> omega
  let decode := fun (f : Bool×Bool) (z : ℕ×ℕ) =>
    let v := decoded 2 f z
    (min v.1 v.2,max v.1 v.2)
  have cnt := cover (S:=S) (pairs U B) decode (by
    intro v hv
    obtain ⟨lo,lt,hi,op,oq⟩ := fits v hv
    obtain ⟨f,z,hz,a|a⟩ := witness (by decide : 0<2) lo (lo.trans lt)
      (bound _ lo (lt.trans hi) op) (bound _ (lo.trans lt) hi oq) (hits v hv)
    · exact ⟨f,z,hz,by simp [decode,a,min_eq_left lt.le,max_eq_right lt.le]⟩
    · exact ⟨f,z,hz,by simp [decode,a,min_eq_right lt.le,max_eq_left lt.le]⟩)
  have nat : S.card≤4*(pairs U B).card := by simpa using cnt
  exact (show (S.card:ℚ) ≤ 4*((pairs U B).card:ℚ) by exact_mod_cast nat).trans
    (mul_le_mul_of_nonneg_left (count_pairs U B) (by norm_num))

/-- The fixed bounded prime-power schedule kills the whole reduced cyclic
group exactly in the structural case, including the trivial group. -/
theorem reduced_dvd_iff {P Q B U : ℕ} (pos : 0<P) (fit : P≤U) :
    reduced P Q ∣ (ReducedSmoothReadout.schedule B U).prod ↔
      reduced P Q ∈ Nat.smoothNumbers (B+1) := by
  constructor
  · exact Nat.mem_smoothNumbers_of_dvd (smooth_schedule B U)
  · intro h
    exact ReducedSmoothReadout.smooth_dvd_schedule
      (Nat.div_pos (Nat.le_of_dvd pos (Nat.gcd_dvd_left ..)) (Nat.gcd_pos_of_pos_left _ pos))
      ((Nat.div_le_self ..).trans fit)
      (fun p prime dv => Nat.lt_succ_iff.mp (Nat.mem_smoothNumbers'.mp h p prime dv))

/-- With the natural increasing order on distinct odd prime factors, the
qualifying proportion in the same population is below 2⁻⁶⁸⁹. -/
theorem full_size_sorted (S : Finset (ℕ×ℕ)) {population : ℕ} (den : 2^2021≤population)
    (fits : ∀ v∈S, v.1.Prime ∧ v.2.Prime ∧ 2<v.1 ∧ v.1<v.2 ∧ v.2<2^1024)
    (hits : ∀ v∈S, Admits 1001 v) : 2^689*S.card<population := by
  have count := sorted_odd_count (U:=2^1023) S (by
    intro v hv
    obtain ⟨p,q,lo,lt,hi⟩ := fits v hv
    exact ⟨by omega,lt,by rwa [show 2*2^1023=2^1024 by decide +kernel],
      p.odd_of_ne_two (by omega),q.odd_of_ne_two (by omega)⟩) hits
  have incl : Nat.smoothNumbersUpTo (2^1023) 1001 ⊆ Nat.smoothNumbersUpTo (2^1024) 1001 := by
    intro n hn
    obtain ⟨size,sm⟩ := Nat.mem_smoothNumbersUpTo.mp hn
    exact Nat.mem_smoothNumbersUpTo.mpr ⟨size.trans (by decide +kernel),sm⟩
  have room : ((Nat.smoothNumbersUpTo (2^1023) 1001).card:ℚ)≤2^297 := by
    exact_mod_cast (card_le_card incl).trans BoundedSmoothCount.smooth_1024.le
  have hi := harmonic_cap 1023 (by decide)
  suffices (2:ℚ)^689*S.card<2^2021 by exact (show 2^689*S.card<2^2021 by exact_mod_cast this).trans_le den
  calc
    _ ≤ (2:ℚ)^689*(4*((2:ℚ)^1023*711*2^297)) := by
      apply mul_le_mul_of_nonneg_left (count.trans _) (by positivity)
      simp only [Nat.cast_pow,Nat.cast_ofNat]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (mul_le_mul_of_nonneg_left hi (by positivity)) room (Nat.cast_nonneg _) (by positivity))
        (by norm_num)
    _ < _ := by norm_num

/-- Extract the structural family from an actual population before counting. -/
noncomputable def qualifying (inputs : Finset (ℕ×ℕ)) (B : ℕ) := by
  classical exact inputs.filter (Admits B)

theorem population_fraction (inputs : Finset (ℕ×ℕ)) (den : 2^2021 ≤ inputs.card)
    (fits : ∀ v∈inputs, v.1.Prime ∧ v.2.Prime ∧ 2<v.1 ∧ v.1<v.2 ∧ v.2<2^1024) :
    2^689*(qualifying inputs 1001).card < inputs.card := by
  classical
  exact full_size_sorted _ den (fun v hv => fits v (mem_filter.mp hv).1)
    (fun _ hv => (mem_filter.mp hv).2)

/-- At 1577 none of the eight reduced sizes is a power of two. Even so,
one signed projected element reaches the identity modulo 19 on doubling. -/
theorem accidental_example : ¬ Admits 3 (19,83) ∧ Nat.Prime 19 ∧ Nat.Prime 83 ∧
    19*83=1577 ∧ jacobiSym 3 1577 = -1 ∧
    let u := ((608,1335) : ZMod 1577 × ZMod 1577)
    let v := quadraticPower (3:ZMod 1577) u (1577+1)
    let w := quadraticPower (3:ZMod 1577) v 2
    u.1^2-3*u.2^2=1 ∧ (2*v.1-2).val.gcd 1577=1 ∧ (2*w.1-2).val.gcd 1577=19 := by
  refine ⟨?_,by norm_num,by norm_num,by decide,by norm_num,?_⟩
  · rintro ⟨s,t,h⟩
    let a : Bool → ℕ := fun split => if split then 3 else 5
    let b : Bool → ℕ := fun split => if split then 41 else 7
    have cert (s t : Bool) :
        (a s).Prime ∧ 3≤a s ∧ a s ∣ reduced (signedTorusOrder 19 s) (signedTorusOrder 83 t) ∧
        (b t).Prime ∧ 3≤b t ∧ b t ∣ reduced (signedTorusOrder 83 t) (signedTorusOrder 19 s) := by
      cases s <;> cases t <;> decide +kernel
    obtain ⟨ap,al,ad,bp,bl,bd⟩ := cert s t
    obtain h|h := h
    · exact (not_lt_of_ge al) (Nat.mem_smoothNumbers'.mp h _ ap ad)
    · exact (not_lt_of_ge bl) (Nat.mem_smoothNumbers'.mp h _ bp bd)
  · have v : quadraticPower (3:ZMod 1577) (608,1335) 1578=(1215,1368) := by
      simp (config := { decide := true }) only [quadraticPower, Nat.reduceDiv, Nat.reduceMod,
        Nat.reduceEqDiff, ↓reduceDIte, ↓reduceIte]
    have w : quadraticPower (3:ZMod 1577) (1215,1368) 2=(305,1501) := by
      simp (config := { decide := true }) only [quadraticPower, Nat.reduceDiv, Nat.reduceMod,
        Nat.reduceEqDiff, ↓reduceDIte, ↓reduceIte]
    change (608:ZMod 1577)^2-3*1335^2=1 ∧
      (2*(quadraticPower 3 (608,1335) 1578 : ZMod 1577 × ZMod 1577).1-2).val.gcd 1577=1 ∧
      (2*(quadraticPower 3 (quadraticPower 3 (608,1335) 1578) 2 : ZMod 1577 × ZMod 1577).1-2).val.gcd 1577=19
    rw [v,w]
    decide +kernel

end PrimeFactors.SmoothSignedStructure
