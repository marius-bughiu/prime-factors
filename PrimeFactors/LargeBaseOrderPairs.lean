import PrimeFactors.SmoothSignedPairs

/-! Population bounds for large local orders in a smooth predecessor sweep.
The local order and the smooth exponent may both vary with the input pair. -/
namespace PrimeFactors.LargeBaseOrderPairs
open Finset

/-- The large-order condition with shifted coordinates P=p−1 and Q=q−1.
Mathlib's smoothness bound is strict, so use B=1001 for primes up to 1000. -/
def Hit (B T P Q : ℕ) : Prop := ∃ m E : ℕ, T ≤ m ∧ m ∣ P ∧
  E ∈ Nat.smoothNumbers B ∧ m ∣ ((P+1)*(Q+1)-1)*E

/-- Each shifted pair is counted once, irrespective of the number of witnesses. -/
noncomputable def admissible (U B T : ℕ) : Finset (ℕ × ℕ) := by
  classical exact (Icc 1 U ×ˢ Icc 1 U).filter fun v => Hit B T v.1 v.2

theorem mem_admissible {U B T P Q : ℕ} : (P,Q) ∈ admissible U B T ↔
    (1 ≤ P ∧ P ≤ U) ∧ (1 ≤ Q ∧ Q ≤ U) ∧ Hit B T P Q := by
  classical simp [admissible,and_assoc]

private theorem predecessor_dvd_iff {P Q m E : ℕ} (hP : m ∣ P) :
    m ∣ ((P+1)*(Q+1)-1)*E ↔ m ∣ Q*E := by
  have exp : (P+1)*(Q+1) = (P*(Q+1)+Q)+1 := by ring
  rw [exp,Nat.add_sub_cancel,Nat.add_mul]
  exact (Nat.dvd_add_iff_right ((hP.mul_right (Q+1)).mul_right E)).symm

private theorem cancel_gcd {m E Q : ℕ} (mp : 0<m) : m ∣ Q*E ↔ m / m.gcd E ∣ Q := by
  let g := m.gcd E
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ mp
  have mEq : g*(m/g)=m := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have eEq : g*(E/g)=E := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  have eq : Q*E = g*(Q*(E/g)) := by rw [mul_left_comm g Q,eEq]
  rw [eq,←mEq,Nat.mul_dvd_mul_iff_left gp]
  rw [mEq]
  exact ⟨(Nat.coprime_div_gcd_div_gcd gp).dvd_of_dvd_mul_right,fun h => dvd_mul_of_dvd_left h _⟩

/-- The part of the local order left after applying E must divide q−1. -/
theorem residue_dvd_other {P Q m E : ℕ} (mp : 0<m) (hP : m ∣ P)
    (hN : m ∣ ((P+1)*(Q+1)-1)*E) : m / m.gcd E ∣ Q :=
  (cancel_gcd mp).mp ((predecessor_dvd_iff hP).mp hN)

/-- Exact finite criterion for the ambient family: the least required exponent
for a divisor m of P is m/gcd(m,Q); it must itself be smooth. -/
theorem hit_iff_smooth_quotient {B T P Q : ℕ} (tp : 0 < T) (pp : 0 < P) :
    Hit B T P Q ↔ ∃ m ∈ P.divisors, T ≤ m ∧ m / m.gcd Q ∈ Nat.smoothNumbers B := by
  constructor
  · rintro ⟨m,E,large,div,smooth,killed⟩
    refine ⟨m,Nat.mem_divisors.mpr ⟨div,pp.ne'⟩,large,Nat.mem_smoothNumbers_of_dvd smooth ?_⟩
    exact (cancel_gcd (tp.trans_le large)).mp
      ((mul_comm E Q) ▸ (predecessor_dvd_iff div).mp killed)
  · rintro ⟨m,hm,large,smooth⟩
    have div := (Nat.mem_divisors.mp hm).1
    refine ⟨m,m / m.gcd Q,large,div,smooth,(predecessor_dvd_iff div).mpr ?_⟩
    rw [mul_comm]
    exact (cancel_gcd (tp.trans_le large)).mpr dvd_rfl

/-- Every genuine local fixed-base hit supplies a witness to the count. -/
theorem of_power {p q a B T E : ℕ} [Fact p.Prime] (qp : 0<q)
    (unit : (a : ZMod p) ≠ 0) (large : T ≤ orderOf (a : ZMod p))
    (smooth : E ∈ Nat.smoothNumbers B) (killed : (a : ZMod p)^((p*q-1)*E) = 1) :
    Hit B T (p-1) (q-1) := by
  have pp := (Fact.out : p.Prime).pos
  refine ⟨_,E,large,orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one unit),smooth,?_⟩
  rw [Nat.sub_add_cancel pp,Nat.sub_add_cancel qp]
  exact orderOf_dvd_of_pow_eq_one killed

/-- Encode each admissible P by its cofactor j, a smooth d, and a divisor k of Q.
The lower bound on the local order gives j≤⌊U/T⌋. -/
theorem encode {U B T P Q : ℕ} (tp : 0<T) (hp : P ∈ Icc 1 U)
    (hit : Hit B T P Q) : ∃ j d k : ℕ, j ∈ Icc 1 (U/T) ∧
      d ∈ Nat.smoothNumbersUpTo U B ∧ k ∣ Q ∧ 0 < k ∧ T ≤ d*k ∧ P = j*d*k := by
  obtain ⟨m,E,large,hP,smooth,hN⟩ := hit
  obtain ⟨pp,pu⟩ := mem_Icc.mp hp
  let d := m.gcd E
  have mp : 0 < m := tp.trans_le large
  have dp : 0 < d := Nat.gcd_pos_of_pos_left _ mp
  have dm : d ∣ m := Nat.gcd_dvd_left ..
  have dk : d*(m/d) = m := Nat.mul_div_cancel' dm
  have jm : (P/m)*m = P := Nat.div_mul_cancel hP
  refine ⟨P/m,d,m/d,mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd pp hP) mp,?_⟩,
    Nat.mem_smoothNumbersUpTo.mpr ⟨(Nat.le_of_dvd mp dm).trans ((Nat.le_of_dvd pp hP).trans pu),
      Nat.mem_smoothNumbers_of_dvd smooth (Nat.gcd_dvd_right ..)⟩,
    residue_dvd_other mp hP hN,Nat.div_pos (Nat.le_of_dvd mp dm) dp,by rw [dk]; exact large,?_⟩
  · apply (Nat.le_div_iff_mul_le tp).mpr
    exact (Nat.mul_le_mul_left (P/m) large).trans (jm.le.trans pu)
  · rw [mul_assoc,dk,jm]

private theorem fixed_other {U B T Q : ℕ} (tp : 0<T) (qp : 0 < Q) :
    (letI := Classical.propDecidable
     ((Icc 1 U).filter fun P => Hit B T P Q).card) ≤
        (U/T)*(Nat.smoothNumbersUpTo U B).card*Q.divisors.card := by
  classical
  let box := (Icc 1 (U/T) ×ˢ Nat.smoothNumbersUpTo U B) ×ˢ Q.divisors
  let decode := fun v : (ℕ × ℕ) × ℕ => v.1.1*v.1.2*v.2
  have sub : ((Icc 1 U).filter fun P => Hit B T P Q) ⊆ box.image decode := by
    intro P h
    obtain ⟨j,d,k,hj,hd,hk,_,_,eq⟩ := encode tp (mem_filter.mp h).1 (mem_filter.mp h).2
    exact mem_image.mpr ⟨((j,d),k),mem_product.mpr ⟨mem_product.mpr ⟨hj,hd⟩,
      Nat.mem_divisors.mpr ⟨hk,qp.ne'⟩⟩,eq.symm⟩
  exact (card_le_card sub).trans (card_image_le.trans_eq (by simp [box,Nat.card_Icc]))

/-- A harmonic majorant for the entire family of large local orders.
The exponent is allowed to depend on both hidden primes. -/
theorem count_harmonic (U B T : ℕ) (tp : 0<T) :
    ((admissible U B T).card : ℚ) ≤ (U/T : ℕ)*(Nat.smoothNumbersUpTo U B).card*
      (U : ℚ)*harmonic U := by
  classical
  let I := Icc 1 U
  let S := (Nat.smoothNumbersUpTo U B).card
  have count : (admissible U B T).card = ∑ Q ∈ I, (I.filter fun P => Hit B T P Q).card := by
    rw [admissible,card_eq_sum_ones,sum_filter,sum_product,sum_comm]
    apply sum_congr rfl
    intro Q _
    rw [card_eq_sum_ones,sum_filter]
  calc
    _ = ∑ Q ∈ I, ((I.filter fun P => Hit B T P Q).card : ℚ) := by exact_mod_cast count
    _ ≤ ∑ Q ∈ I, ((U/T : ℕ):ℚ)*S*Q.divisors.card := by
      apply sum_le_sum
      intro Q hQ
      exact_mod_cast fixed_other (B:=B) tp (mem_Icc.mp hQ).1
    _ = ((U/T : ℕ):ℚ)*S*∑ Q ∈ I,(Q.divisors.card:ℚ) := by rw [mul_sum]
    _ ≤ ((U/T : ℕ):ℚ)*S*((U:ℚ)*harmonic U) := by
      gcongr
      exact SmoothSignedPairs.divisor_sum U
    _ = _ := by dsimp [S]; ring

private noncomputable def rectangle (U d k : ℕ) : Finset (ℕ × ℕ) :=
  ((Ioc 0 U).filter (d*k ∣ ·)) ×ˢ ((Ioc 0 U).filter (k ∣ ·))

private theorem reciprocal_tail {K U : ℕ} (kp : 0 < K) :
    ∑ k ∈ Icc K U, 1/(k : ℚ)^2 ≤ (2:ℚ)/K := by
  classical
  by_cases fits : K ≤ U
  · let f (k : ℕ) : ℚ := -(1/(k:ℚ))
    have telescopes : ∑ k ∈ Icc K U, (f (k+1)-f k) = f (U+1)-f K := by
      rw [←Nat.Ico_succ_right]
      exact sum_Ico_sub _ (by omega)
    have lower (k : ℕ) (hk : k ∈ Icc K U) : (1 : ℚ) ≤ k := by
      exact_mod_cast kp.trans_le (mem_Icc.mp hk).1
    calc
      _ ≤ ∑ k ∈ Icc K U, 2*(f (k+1)-f k) := by
        apply sum_le_sum
        intro k hk
        have h := lower k hk
        dsimp [f]
        push_cast
        have h₁ : (0:ℚ) < k := by linarith
        have h₂ : (0:ℚ) < k+1 := by linarith
        calc
          1/(k:ℚ)^2 ≤ 2/(((k:ℚ)+1)*k) := by
            apply (div_le_div_iff₀ (sq_pos_of_pos h₁) (mul_pos h₂ h₁)).mpr
            nlinarith [mul_nonneg h₁.le (sub_nonneg.mpr h)]
          _ = _ := by field_simp
      _ = 2*(f (U+1)-f K) := by rw [←mul_sum,telescopes]
      _ ≤ _ := by
        dsimp [f]
        push_cast
        have h : 0 ≤ 1/((U:ℚ)+1) := by positivity
        simp only [div_eq_mul_inv,one_mul] at h ⊢
        linarith
  · rw [Icc_eq_empty fits,sum_empty]
    positivity

private theorem count_smooth_divisor {U T d : ℕ} (tp : 0<T) (dp : 0<d) :
    ∑ k ∈ Icc ((T-1)/d+1) U, ((rectangle U d k).card : ℚ) ≤ 2*(U:ℚ)^2/((max T d:ℕ):ℚ) := by
  let K := (T-1)/d+1
  have kp : 0<K := Nat.zero_lt_succ _
  have tk : T ≤ d*K := by
    have := Nat.lt_mul_div_succ (T-1) dp
    dsimp [K]
    omega
  change ∑ k ∈ Icc K U, _ ≤ _
  calc
    _ ≤ ∑ k ∈ Icc K U, (U:ℚ)^2/d * (1/(k:ℚ)^2) := by
      apply sum_le_sum
      intro k hk
      simp only [rectangle,card_product,Nat.Ioc_filter_dvd_card_eq_div,Nat.cast_mul]
      calc
        _ ≤ ((U:ℚ)/(d*k))*(U/k) := by
          apply mul_le_mul (by simpa only [Nat.cast_mul] using (Nat.cast_div_le (α:=ℚ) (m:=U) (n:=d*k)))
            (Nat.cast_div_le (α:=ℚ)) (Nat.cast_nonneg _) (by positivity)
        _ = _ := by ring
    _ = (U:ℚ)^2/d * ∑ k ∈ Icc K U, (1/(k:ℚ)^2) := by rw [mul_sum]
    _ ≤ (U:ℚ)^2/d * (2/K) := by
      apply mul_le_mul_of_nonneg_left (reciprocal_tail kp) (by positivity)
    _ = 2*(U:ℚ)^2/(d*K) := by ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (by positivity)
      · exact_mod_cast tp.trans_le (le_max_left T d)
      · exact_mod_cast max_le tk (Nat.le_mul_of_pos_right d kp)

/-- Retain the larger of d and T in the divisor tail. -/
theorem count_max_rat (U B T : ℕ) (tp : 0<T) :
    ((admissible U B T).card : ℚ) ≤ 2*(U:ℚ)^2 *
      ∑ d ∈ Nat.smoothNumbersUpTo U B, (1:ℚ)/(max T d:ℕ) := by
  classical
  let S := Nat.smoothNumbersUpTo U B
  let grid (d : ℕ) := (Icc ((T-1)/d+1) U).biUnion (rectangle U d)
  have sub : admissible U B T ⊆ S.biUnion grid := by
    intro v hv
    obtain ⟨box,hit⟩ := mem_filter.mp hv
    obtain ⟨hP,hQ⟩ := mem_product.mp box
    obtain ⟨j,d,k,_,hd,hk,_,large,eq⟩ := encode tp hP hit
    have dp := Nat.pos_of_ne_zero (Nat.mem_smoothNumbersUpTo.mp hd).2.1
    have low : (T-1)/d < k := (Nat.div_lt_iff_lt_mul dp).mpr (by rw [mul_comm]; omega)
    have ppos := (mem_Icc.mp hP).1
    have qpos := (mem_Icc.mp hQ).1
    apply mem_biUnion.mpr
    refine ⟨d,hd,mem_biUnion.mpr ⟨k,mem_Icc.mpr ⟨low,(Nat.le_of_dvd qpos hk).trans (mem_Icc.mp hQ).2⟩,?_⟩⟩
    exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_Ioc.mpr (mem_Icc.mp hP),⟨j,by rw [eq]; ring⟩⟩,
      mem_filter.mpr ⟨mem_Ioc.mpr (mem_Icc.mp hQ),hk⟩⟩
  have count : (admissible U B T).card ≤ ∑ d ∈ S, ∑ k ∈ Icc ((T-1)/d+1) U, (rectangle U d k).card :=
    (card_le_card sub).trans (card_biUnion_le.trans (sum_le_sum fun _ _ => card_biUnion_le))
  calc
    _ ≤ ∑ d ∈ S, ∑ k ∈ Icc ((T-1)/d+1) U, ((rectangle U d k).card : ℚ) := by exact_mod_cast count
    _ ≤ ∑ d ∈ S, 2*(U:ℚ)^2/(max T d:ℕ) := sum_le_sum fun _ hd =>
      count_smooth_divisor tp (Nat.pos_of_ne_zero (Nat.mem_smoothNumbersUpTo.mp hd).2.1)
    _ = _ := by rw [mul_sum]; simp [S,div_eq_mul_inv]

/-- Real-valued version for applying a Rankin bound to the smooth-divisor sum. -/
theorem count_max (U B T : ℕ) (tp : 0<T) :
    ((admissible U B T).card : ℝ) ≤ 2*(U:ℝ)^2 *
      ∑ d ∈ Nat.smoothNumbersUpTo U B, (1:ℝ)/(max T d:ℕ) := by
  have h := (Rat.cast_le (K:=ℝ)).mpr (count_max_rat U B T tp)
  push_cast at h ⊢
  exact h

/-- Counting multiples of dk in the first coordinate and of k in the second
removes the harmonic factor. For each smooth d, k starts at ceil(T/d).
This bounds the union over all possible orders and all smooth exponents. -/
theorem count_tail (U B T : ℕ) (tp : 0<T) :
    ((admissible U B T).card : ℚ) ≤ 2*(Nat.smoothNumbersUpTo U B).card*(U:ℚ)^2/T := by
  apply (count_max_rat U B T tp).trans
  have bound : (∑ d ∈ Nat.smoothNumbersUpTo U B, (1:ℚ)/(max T d:ℕ)) ≤
      ∑ _ ∈ Nat.smoothNumbersUpTo U B, (1:ℚ)/T := by
    apply sum_le_sum
    intro d _
    exact div_le_div_of_nonneg_left zero_le_one (by exact_mod_cast tp) (by exact_mod_cast le_max_left T d)
  calc
    _ ≤ 2*(U:ℚ)^2*∑ _ ∈ Nat.smoothNumbersUpTo U B, (1:ℚ)/T :=
      mul_le_mul_of_nonneg_left bound (by positivity)
    _ = _ := by simp; ring

end PrimeFactors.LargeBaseOrderPairs
