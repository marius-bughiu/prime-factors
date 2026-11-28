import PrimeFactors.EqualityPatternSampling

/-! Collision counts among independent uniform draws, observed through equality alone. -/

namespace PrimeFactors.EqualityCollisionEstimator

open Finset

/-- Number of occurrences of a label in the word. -/
noncomputable def occupancy {m t : ℕ} (w : Fin t → Fin m) (a : Fin m) : ℕ :=
  ∑ i, if w i = a then 1 else 0

/-- Number of unordered pairs of distinct positions with equal labels. The head
contributes exactly one pair for each matching position in the tail. -/
noncomputable def collisions {m : ℕ} : {t : ℕ} → (Fin t → Fin m) → ℕ
  | 0, _ => 0
  | _ + 1, w => collisions (Fin.tail w) + occupancy (Fin.tail w) (w 0)

/-- The statistic has the same value whenever the two equality transcripts agree. -/
theorem observed {m n t : ℕ} (w : Fin t → Fin m) (v : Fin t → Fin n)
    (h : EqualityPatternSampling.transcript w = EqualityPatternSampling.transcript v) :
    collisions w = collisions v := by
  have same := (EqualityPatternSampling.transcript_eq_iff w v).mp h
  clear h
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [collisions]
    congr 1
    · exact ih _ _ (fun i j => same i.succ j.succ)
    · unfold occupancy
      exact sum_congr rfl fun i _ => if_congr (same i.succ 0) rfl rfl

/-- The uniform average over all m^t ordered words, i.e. draws with replacement. -/
noncomputable def mean (m t : ℕ) (f : (Fin t → Fin m) → ℝ) : ℝ :=
  (∑ w, f w) / (m : ℝ)^t

private theorem occ_cons {m t : ℕ} (a b : Fin m) (w : Fin t → Fin m) :
    occupancy (Fin.cons a w) b = (if a = b then 1 else 0) + occupancy w b := by
  unfold occupancy
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

private theorem occupancy_total {m t : ℕ} (w : Fin t → Fin m) :
    ∑ a, (occupancy w a : ℝ) = t := by
  simp only [occupancy, Nat.cast_sum]
  rw [sum_comm]
  simp

private theorem occupancy_squares {m t : ℕ} (w : Fin t → Fin m) :
    ∑ a, (occupancy w a : ℝ)^2 = (t : ℝ) + 2 * collisions w := by
  induction t with
  | zero => simp [occupancy,collisions]
  | succ t ih =>
    let v := Fin.tail w
    have occ (b : Fin m) : (occupancy w b : ℝ)^2 =
        (occupancy v b : ℝ)^2 + (if w 0 = b then 1 + 2 * (occupancy v b : ℝ) else 0) := by
      have expand := occ_cons (w 0) b v
      rw [show Fin.cons (w 0) v = w from Fin.cons_self_tail w] at expand
      rw [expand]
      split_ifs <;> push_cast <;> ring
    rw [sum_congr rfl (fun b _ => occ b),sum_add_distrib,ih]
    simp [collisions,v]
    ring

private theorem split_mean {m t : ℕ} (f : (Fin (t+1) → Fin m) → ℝ) :
    mean m (t+1) f = mean m t (fun w => (∑ a, f (Fin.cons a w)) / m) := by
  unfold mean
  rw [←(Fin.consEquiv (fun _ : Fin (t+1) => Fin m)).sum_comp f,Fintype.sum_prod_type,
    sum_comm,←sum_div,pow_succ]
  change (∑ w : Fin t → Fin m, ∑ a : Fin m, f (Fin.cons a w)) / _ = _
  rw [div_div,mul_comm]

private theorem mean_const {m t : ℕ} (pos : 0 < m) (c : ℝ) :
    mean m t (fun _ => c) = c := by
  simp [mean, show (m : ℝ) ≠ 0 by exact_mod_cast pos.ne']

private theorem mean_add {m t : ℕ} (f g : (Fin t → Fin m) → ℝ) :
    mean m t (fun w => f w + g w) = mean m t f + mean m t g := by
  simp [mean,sum_add_distrib,add_div]

private theorem mean_mul {m t : ℕ} (a : ℝ) (f : (Fin t → Fin m) → ℝ) :
    mean m t (fun w => a * f w) = a * mean m t f := by
  simp [mean,←mul_sum,mul_div_assoc]

private theorem pairs_succ (t : ℕ) :
    ((t+1).choose 2 : ℝ) = (t.choose 2 : ℝ) + t := by
  rw [Nat.choose_succ_succ]
  simp [add_comm]

private theorem twice_pairs (t : ℕ) : 2 * (t.choose 2 : ℝ) = (t : ℝ) * (t-1) := by
  induction t with
  | zero => norm_num
  | succ t ih =>
    rw [pairs_succ,Nat.cast_succ]
    linarith

/-- Exact first moment and variance of the number of colliding unordered pairs. -/
theorem moments {m : ℕ} (pos : 0 < m) (t : ℕ) :
    mean m t (fun w => (collisions w : ℝ)) = (t.choose 2 : ℝ) / m ∧
    mean m t (fun w => ((collisions w : ℝ) - (t.choose 2 : ℝ) / m)^2) =
      (t.choose 2 : ℝ) * (m-1) / (m : ℝ)^2 := by
  have mp : (m : ℝ) ≠ 0 := by exact_mod_cast pos.ne'
  induction t with
  | zero => simp [mean,collisions]
  | succ t ih =>
    let B : ℝ := t.choose 2
    let M : ℝ := m
    let T : ℝ := t
    have nz : M ≠ 0 := mp
    have bt : 2 * B = T * (T-1) := twice_pairs t
    have first (w : Fin t → Fin m) :
        (∑ a : Fin m, (collisions (Fin.cons a w) : ℝ)) / M =
        (collisions w : ℝ) + T / M := by
      simp only [collisions, Fin.tail_cons, Fin.cons_zero, Nat.cast_add, sum_add_distrib,
        occupancy_total,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
      dsimp only [M,T]
      field_simp
      ring
    have second (w : Fin t → Fin m) :
        (∑ a : Fin m, ((collisions (Fin.cons a w) : ℝ) - (B+T)/M)^2) / M =
          ((collisions w : ℝ) - B/M)^2 + (2/M)*(collisions w : ℝ) + (T/M - (T/M)^2) := by
      let c : ℝ := (collisions w : ℝ) - (B+T)/M
      have expand (a : Fin m) : ((collisions (Fin.cons a w) : ℝ) - (B+T)/M)^2 =
          c^2 + (2*c)*(occupancy w a : ℝ) + (occupancy w a : ℝ)^2 := by
        simp only [collisions, Fin.tail_cons, Fin.cons_zero, Nat.cast_add, c]
        ring
      rw [sum_congr rfl (fun a _ => expand a),sum_add_distrib,sum_add_distrib,
        ←mul_sum,occupancy_total,occupancy_squares]
      simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
      dsimp only [c,M,T,B]
      field_simp
      ring
    rw [pairs_succ]
    constructor
    · rw [split_mean]
      change mean m t (fun w => (∑ a, (collisions (Fin.cons a w) : ℝ)) / M) = (B+T)/M
      simp_rw [first]
      rw [mean_add,ih.1,mean_const pos]
      exact (add_div ..).symm
    · rw [split_mean]
      change mean m t (fun w => (∑ a, ((collisions (Fin.cons a w) : ℝ) - (B+T)/M)^2) / M) =
        (B+T)*(M-1)/M^2
      simp_rw [second]
      rw [mean_add,mean_add,mean_mul,mean_const pos]
      change mean m t (fun w => ((collisions w : ℝ) - (t.choose 2 : ℝ) / m)^2) + _ + _ = _
      rw [ih.1,ih.2]
      change B*(M-1)/M^2 + (2/M)*(B/M) + (T/M - (T/M)^2) = _
      calc
        _ = (B*(M-1) + 2*B + T*M - T^2)/M^2 := by field_simp; ring
        _ = _ := by congr 1; linear_combination bt

private theorem mean_le {m t : ℕ} {f g : (Fin t → Fin m) → ℝ}
    (h : ∀ w, f w ≤ g w) : mean m t f ≤ mean m t g :=
  div_le_div_of_nonneg_right (sum_le_sum (fun w _ => h w)) (by positivity)

/-- Probability of an event in the uniform experiment. -/
noncomputable def probability (m t : ℕ) (p : (Fin t → Fin m) → Prop) : ℝ :=
  open Classical in mean m t (fun w => if p w then 1 else 0)

private theorem accuracy {m t : ℕ} (pos : 0 < m) (f : (Fin t → Fin m) → ℝ)
    (good : (Fin t → Fin m) → Prop) (μ r : ℝ) (radius : 0 < r)
    (miss : ∀ w, ¬ good w → r^2 ≤ (f w-μ)^2)
    (budget : 4 * mean m t (fun w => (f w-μ)^2) ≤ r^2) :
    3/4 ≤ probability m t good := by
  classical
  have bound : mean m t (fun _ => r^2) ≤
      mean m t (fun w => r^2*(if good w then 1 else 0) + (f w-μ)^2) := by
    apply mean_le
    intro w
    by_cases h : good w
    · simp [h,sq_nonneg]
    · simpa [h] using miss w h
  rw [mean_const pos,mean_add,mean_mul] at bound
  unfold probability
  apply le_of_mul_le_mul_left _ (sq_pos_of_pos radius)
  linarith only [budget,bound]

/-- The midpoint of the expected collision counts under the two candidate
alphabet sizes. At equality the decision favors the smaller alphabet. -/
noncomputable def threshold (m n t : ℕ) : ℝ :=
  ((t.choose 2 : ℝ) / m + (t.choose 2 : ℝ) / n) / 2

/-- A collision-count test for two specified possible alphabet sizes. If the
increment is at least a square root and at most the smaller alphabet size,
12m draws suffice for probability at least 3/4 under each hypothesis. -/
theorem distinguish {m d : ℕ} (pos : 0 < m) (gap : m ≤ d^2) (cap : d ≤ m) :
    let t := 12*m
    let k := threshold m (m+d) t
    3/4 ≤ probability m t (fun w => k ≤ (collisions w : ℝ)) ∧
    3/4 ≤ probability (m+d) t (fun w => (collisions w : ℝ) < k) := by
  let t := 12*m
  let M : ℝ := m
  let D : ℝ := d
  let B : ℝ := t.choose 2
  let x := B/M
  let y := B/(M+D)
  let r := (x-y)/2
  let k := (x+y)/2
  have mp : 0 < M := by dsimp [M]; exact_mod_cast pos
  have mone : 1 ≤ M := by dsimp [M]; exact_mod_cast (show 1 ≤ m by omega)
  have dp : 0 < D := by
    dsimp [D]
    exact_mod_cast (show 0 < d by cases d <;> simp_all)
  have np : 0 < M+D := by positivity
  have d2 : M ≤ D^2 := by dsimp [M,D]; exact_mod_cast gap
  have dm : D ≤ M := by dsimp [M,D]; exact_mod_cast cap
  have ts : (t : ℝ) = 12*M := by simp [t,M]
  have Bsize : 64*M^2 ≤ B := by
    have bt := twice_pairs t
    rw [ts] at bt
    change 2*B = _ at bt
    nlinarith only [bt,mul_nonneg mp.le (sub_nonneg.mpr mone),mp]
  have bp : 0 < B := lt_of_lt_of_le (by positivity : 0 < 64*M^2) Bsize
  have r_eq : r = B*D/(2*M*(M+D)) := by
    dsimp only [r,x,y]
    field_simp
    ring
  have rp : 0 < r := by rw [r_eq]; positivity
  have sqm : (M+D)^2 ≤ (2*M)^2 := by
    apply pow_le_pow_left₀ np.le (by linarith) 2
  have scale : 16*M*(M+D)^2 ≤ B*D^2 := by
    calc
      _ ≤ 16*M*(2*M)^2 := by gcongr
      _ = (64*M^2)*M := by ring
      _ ≤ B*D^2 := mul_le_mul Bsize d2 mp.le bp.le
  have spread : 4*(B/M) ≤ r^2 := by
    rw [r_eq,div_pow,←mul_div_assoc,div_le_div_iff₀]
    · have scaled := mul_le_mul_of_nonneg_left scale (mul_nonneg bp.le mp.le)
      nlinarith only [scaled]
    · positivity
    · positivity
  have var_le (n : ℝ) (hn : 0<n) (order : M≤n) : B*(n-1)/n^2 ≤ B/M := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hn) mp).mpr
    have small := mul_le_mul_of_nonneg_right order hn.le
    nlinarith only [mul_le_mul_of_nonneg_left small bp.le,mul_nonneg bp.le mp.le]
  have va := (moments pos t).2
  have vb := (moments (show 0<m+d by omega) t).2
  rw [Nat.cast_add] at vb
  change mean m t (fun w => ((collisions w : ℝ)-x)^2) = B*(M-1)/M^2 at va
  change mean (m+d) t (fun w => ((collisions w : ℝ)-y)^2) = B*(M+D-1)/(M+D)^2 at vb
  have cut : threshold m (m+d) t = k := by simp [threshold,k,x,y,B,M,D]
  change 3/4 ≤ probability m t (fun w => threshold m (m+d) t ≤ (collisions w : ℝ)) ∧
    3/4 ≤ probability (m+d) t (fun w => (collisions w : ℝ) < threshold m (m+d) t)
  rw [cut]
  constructor
  · apply accuracy pos (fun w => (collisions w : ℝ)) _ x r rp
    · intro w h
      change ¬ k ≤ _ at h
      have low : r ≤ x - (collisions w : ℝ) := by dsimp only [r,k] at *; linarith only [h]
      calc
        _ ≤ (x - (collisions w : ℝ))^2 := pow_le_pow_left₀ rp.le low 2
        _ = _ := by ring
    · rw [va]
      exact (mul_le_mul_of_nonneg_left (var_le M mp le_rfl) (by norm_num)).trans spread
  · apply accuracy (by omega) (fun w => (collisions w : ℝ)) _ y r rp
    · intro w h
      change ¬ _ < k at h
      have high : r ≤ (collisions w : ℝ) - y := by dsimp only [r,k] at *; linarith only [h]
      exact pow_le_pow_left₀ rp.le high 2
    · rw [vb]
      exact (mul_le_mul_of_nonneg_left (var_le (M+D) np (by linarith)) (by norm_num)).trans spread

end PrimeFactors.EqualityCollisionEstimator
