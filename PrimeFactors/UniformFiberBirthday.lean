import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! Counts for independent, uniform samples with replacement and equal-sized fibers. -/

namespace PrimeFactors.UniformFiberBirthday

variable {A B C : Type*}

/-- Choosing a word of seeds amounts to choosing an admissible word of outputs
and one seed in each indicated fiber. -/
private def liftWordEquiv (f : A → B) {m : ℕ} (P : (Fin m → B) → Prop) :
    {w : Fin m → A // P (f ∘ w)} ≃
      Σ e : {v : Fin m → B // P v}, (i : Fin m) → {a : A // f a = e.1 i} := by
  let g (w : {w : Fin m → A // P (f ∘ w)}) : {v : Fin m → B // P v} := ⟨f ∘ w.1, w.2⟩
  refine (Equiv.sigmaFiberEquiv g).symm.trans (Equiv.sigmaCongrRight fun e => ?_)
  refine ⟨fun w i => ⟨w.1.1 i, congrFun (congrArg Subtype.val w.2) i⟩, ?_, ?_, ?_⟩
  · intro s
    have he : f ∘ (fun i => (s i).1) = e.1 := funext fun i => (s i).2
    exact ⟨⟨fun i => (s i).1, (congrArg P he).mpr e.2⟩, Subtype.ext he⟩
  · intro w; rfl
  · intro w; rfl

/-- Every event on uniform output words has exactly k^m seed lifts per word. -/
theorem event_card [Fintype A] [Fintype B] (f : A → B) {k m : ℕ}
    (regular : ∀ b, Nat.card {a : A // f a = b} = k) (P : (Fin m → B) → Prop) :
    Nat.card {w : Fin m → A // P (f ∘ w)} = Nat.card {v : Fin m → B // P v} * k^m := by
  classical
  rw [Nat.card_congr (liftWordEquiv f P), Nat.card_eq_fintype_card, Fintype.card_sigma]
  have h (b : B) : Fintype.card {a : A // f a = b} = k := by
    simpa only [Nat.card_eq_fintype_card] using regular b
  simp [Fintype.card_pi, h, Nat.card_eq_fintype_card]

private def injectiveEquiv (D E : Type*) :
    {w : D → E // Function.Injective w} ≃ (D ↪ E) where
  toFun w := ⟨w.1,w.2⟩
  invFun e := ⟨e,e.injective⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem injective_card [Fintype B] (m : ℕ) :
    Nat.card {w : Fin m → B // Function.Injective w} = (Fintype.card B).descFactorial m := by
  classical
  rw [Nat.card_congr (injectiveEquiv _ _), Nat.card_eq_fintype_card,
    Fintype.card_embedding_eq, Fintype.card_fin]

/-- Exact count of words with distinct outputs. The codomain may be chosen
to be the range of the regular map. -/
theorem distinct_card [Fintype A] [Fintype B] (f : A → B) {k m : ℕ}
    (regular : ∀ b, Nat.card {a : A // f a = b} = k) :
    Nat.card {w : Fin m → A // Function.Injective (f ∘ w)} =
      (Fintype.card B).descFactorial m * k^m := by
  rw [event_card f regular (fun w => Function.Injective w), injective_card]

/-- A pair of positions whose labels agree in exactly one coordinate. -/
def ProperPair {m : ℕ} (w : Fin m → B × C) : Prop := ∃ i j, i ≠ j ∧
  (((w i).1 = (w j).1 ∧ (w i).2 ≠ (w j).2) ∨
   ((w i).2 = (w j).2 ∧ (w i).1 ≠ (w j).1))

private def bothEquiv (B C : Type*) (m : ℕ) :
    {w : Fin m → B × C // Function.Injective (Prod.fst ∘ w) ∧ Function.Injective (Prod.snd ∘ w)} ≃
    {u : Fin m → B // Function.Injective u} × {v : Fin m → C // Function.Injective v} where
  toFun w := (⟨Prod.fst ∘ w.1,w.2.1⟩, ⟨Prod.snd ∘ w.1,w.2.2⟩)
  invFun uv := ⟨fun i => (uv.1.1 i, uv.2.1 i), uv.1.2, uv.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Distinct joint labels guarantee either a proper pair or injectivity in
both coordinates. The resulting bound also counts successes when computing
individual gcds, even if different pairs collide at the two primes. -/
theorem proper_count_bound [Fintype B] [Fintype C] (m : ℕ) :
    (Fintype.card B * Fintype.card C).descFactorial m ≤
      Nat.card {w : Fin m → B × C // ProperPair w} +
      (Fintype.card B).descFactorial m * (Fintype.card C).descFactorial m := by
  classical
  let both (w : Fin m → B × C) := Function.Injective (Prod.fst ∘ w) ∧ Function.Injective (Prod.snd ∘ w)
  have classify {w : Fin m → B × C} (hw : Function.Injective w) (h : ¬both w) : ProperPair w := by
    by_contra hno
    apply h
    constructor
    · intro i j eqn
      by_contra diff
      have snd : (w i).2 ≠ (w j).2 := fun hs => diff (hw (Prod.ext eqn hs))
      exact hno ⟨i,j,diff, Or.inl ⟨eqn,snd⟩⟩
    · intro i j eqn
      by_contra diff
      have fst : (w i).1 ≠ (w j).1 := fun hf => diff (hw (Prod.ext hf eqn))
      exact hno ⟨i,j,diff, Or.inr ⟨eqn,fst⟩⟩
  let split (w : {v : Fin m → B × C // Function.Injective v}) :
      {v : Fin m → B × C // ProperPair v} ⊕ {v : Fin m → B × C // both v} :=
    if h : both w.1 then Sum.inr ⟨w.1,h⟩ else Sum.inl ⟨w.1,classify w.2 h⟩
  have inj : Function.Injective split := by
    intro u v h
    have forget := congrArg (Sum.elim (fun w => w.1) (fun w => w.1)) h
    apply Subtype.ext
    simpa [split, apply_dite] using forget
  have bound := Nat.card_le_card_of_injective split inj
  rw [injective_card, Fintype.card_prod, Nat.card_sum, Nat.card_congr (bothEquiv B C m),
    Nat.card_prod, injective_card, injective_card] at bound
  exact bound

/-- A proper pair rules out injectivity in both coordinates, so successes
and words injective in both coordinates count disjoint subsets. -/
theorem proper_count_upper [Fintype B] [Fintype C] (m : ℕ) :
    Nat.card {w : Fin m → B × C // ProperPair w} +
      (Fintype.card B).descFactorial m * (Fintype.card C).descFactorial m ≤
        (Fintype.card B * Fintype.card C)^m := by
  classical
  let both (w : Fin m → B × C) := Function.Injective (Prod.fst ∘ w) ∧ Function.Injective (Prod.snd ∘ w)
  have disjoint {w : Fin m → B × C} (h : ProperPair w) (no : both w) : False := by
    obtain ⟨i,j,ne,e|e⟩ := h
    · exact ne (no.1 e.1)
    · exact ne (no.2 e.1)
  let forget : {w : Fin m → B × C // ProperPair w} ⊕ {w : Fin m → B × C // both w} →
      (Fin m → B × C) := Sum.elim Subtype.val Subtype.val
  have inj : Function.Injective forget := by
    rintro (u|u) (v|v) h
    · exact congrArg Sum.inl (Subtype.ext h)
    · change u.1 = v.1 at h
      exact (disjoint u.2 ((congrArg both h).mpr v.2)).elim
    · change u.1 = v.1 at h
      exact (disjoint v.2 ((congrArg both h).mp u.2)).elim
    · exact congrArg Sum.inr (Subtype.ext h)
  have bound := Nat.card_le_card_of_injective forget inj
  rw [Nat.card_sum, Nat.card_congr (bothEquiv B C m), Nat.card_prod,
    injective_card, injective_card, Nat.card_eq_fintype_card (α := Fin m → B × C),
    Fintype.card_fun, Fintype.card_prod, Fintype.card_fin] at bound
  exact bound

/-- Probability that m independent uniform labels from d possibilities are distinct. -/
noncomputable def distinctProbability (d m : ℕ) : ℝ := (d.descFactorial m : ℝ) / (d : ℝ)^m

private theorem probability_nonneg (d m : ℕ) : 0 ≤ distinctProbability d m := by
  unfold distinctProbability
  positivity

private theorem probability_le_one {d : ℕ} (hd : 0 < d) (m : ℕ) :
    distinctProbability d m ≤ 1 := by
  unfold distinctProbability
  rw [div_le_one (by positivity)]
  exact_mod_cast d.descFactorial_le_pow m

private theorem probability_step {d m : ℕ} (hd : 0 < d) (hm : m ≤ d) :
    distinctProbability d (m+1) = distinctProbability d m * (1 - m/(d:ℝ)) := by
  unfold distinctProbability
  rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hm, pow_succ]
  have h : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp
  ring

/-- The exact no-collision probability lies below the elementary exponential birthday bound. -/
theorem distinct_probability_upper {d m : ℕ} (hd : 0 < d) (hm : m ≤ d) :
    distinctProbability d m ≤ Real.exp (-(m:ℝ)*(m-1)/(2*d)) := by
  induction m with
  | zero => simp [distinctProbability]
  | succ m ih =>
    have hmd : m ≤ d := by omega
    have dp : 0 < (d:ℝ) := by exact_mod_cast hd
    have hfactor : 0 ≤ 1 - (m:ℝ)/d := sub_nonneg.mpr ((div_le_one dp).mpr (by exact_mod_cast hmd))
    rw [probability_step hd hmd]
    calc
      _ ≤ Real.exp (-(m:ℝ)*(m-1)/(2*d)) * Real.exp (-(m:ℝ)/d) := by
        apply mul_le_mul (ih hmd) _ hfactor (Real.exp_pos _).le
        convert Real.add_one_le_exp (-(m:ℝ)/d) using 1; ring
      _ = _ := by rw [← Real.exp_add, Nat.cast_succ]; congr 1; field_simp; ring

/-- Subtracting the pairwise union bound gives a lower bound on the chance
of distinct joint labels. -/
theorem distinct_probability_lower {d m : ℕ} (hd : 0 < d) (hm : m ≤ d) :
    1 - (m:ℝ)*(m-1)/(2*d) ≤ distinctProbability d m := by
  induction m with
  | zero => simp [distinctProbability]
  | succ m ih =>
    have hmd : m ≤ d := by omega
    have dp : 0 < (d:ℝ) := by exact_mod_cast hd
    have nonneg : 0 ≤ (m:ℝ)/d := by positivity
    have step := mul_le_mul_of_nonneg_right (probability_le_one hd m) nonneg
    have eqn : 1 - ((m:ℝ)+1)*((m+1)-1)/(2*d) = 1 - (m:ℝ)*(m-1)/(2*d) - m/d := by
      field_simp; ring
    rw [probability_step hd hmd, Nat.cast_succ, eqn]
    linarith [ih hmd]

/-- A lower bound for a proper collision with independent uniform prime coordinates. -/
theorem proper_probability_lower [Fintype B] [Fintype C] (m : ℕ)
    (hb : 0 < Fintype.card B) (hc : 0 < Fintype.card C) :
    distinctProbability (Fintype.card B * Fintype.card C) m -
      distinctProbability (Fintype.card B) m * distinctProbability (Fintype.card C) m ≤
      (Nat.card {w : Fin m → B × C // ProperPair w} : ℝ) /
        ((Fintype.card B * Fintype.card C : ℕ) : ℝ)^m := by
  have cnt := proper_count_bound (B := B) (C := C) m
  have cnt' : (((Fintype.card B * Fintype.card C).descFactorial m : ℕ) : ℝ) ≤
      (Nat.card {w : Fin m → B × C // ProperPair w} : ℝ) +
      ((Fintype.card B).descFactorial m : ℝ) * ((Fintype.card C).descFactorial m : ℝ) := by
    exact_mod_cast cnt
  unfold distinctProbability
  rw [div_mul_div_comm, Nat.cast_mul, mul_pow, ← sub_div]
  apply div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- The complementary upper bound for the probability of a proper pair. -/
theorem proper_probability_upper [Fintype B] [Fintype C] (m : ℕ)
    (hb : 0 < Fintype.card B) (hc : 0 < Fintype.card C) :
    (Nat.card {w : Fin m → B × C // ProperPair w} : ℝ) /
        ((Fintype.card B * Fintype.card C : ℕ) : ℝ)^m ≤
      1 - distinctProbability (Fintype.card B) m * distinctProbability (Fintype.card C) m := by
  have cnt := proper_count_upper (B := B) (C := C) m
  have cnt' : (Nat.card {w : Fin m → B × C // ProperPair w} : ℝ) +
      ((Fintype.card B).descFactorial m : ℝ) * ((Fintype.card C).descFactorial m : ℝ) ≤
      (((Fintype.card B * Fintype.card C : ℕ):ℝ))^m := by exact_mod_cast cnt
  unfold distinctProbability
  rw [div_mul_div_comm, Nat.cast_mul, mul_pow, le_sub_iff_add_le, ← add_div]
  apply (div_le_one (by positivity)).mpr
  simpa [Nat.cast_mul, mul_pow] using cnt'

private theorem exp_threshold : Real.exp (-((2999:ℝ)/1000)) < 499/10000 := by
  have h := Real.sum_le_exp_of_nonneg (x := (2999:ℝ)/1000) (by norm_num) 10
  have hsum : 10000/(499:ℝ) < ∑ i ∈ Finset.range 10, ((2999:ℝ)/1000)^i / i.factorial := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hval := hsum.trans_le h
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_lt_iff₀ (Real.exp_pos _)).mpr
  linarith

set_option exponentiation.threshold 2050 in
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
/-- At m=2^511, for two label spaces of the sizes guaranteed by regular
twelve-to-one maps on 1024-bit primes, the chance of a proper pair exceeds 95%. -/
theorem full_size_bound {d e : ℕ} (dlo : 2^1019 ≤ d) (elo : 2^1019 ≤ e)
    (dhi : 12*d ≤ 2^1024) (ehi : 12*e ≤ 2^1024) :
    (95:ℝ)/100 < distinctProbability (d*e) (2^511) -
      distinctProbability d (2^511) * distinctProbability e (2^511) := by
  let m : ℕ := 2^511
  change _ < distinctProbability (d*e) m - distinctProbability d m * distinctProbability e m
  have dm : m ≤ d := (by norm_num [m] : m ≤ 2^1019).trans dlo
  have em : m ≤ e := (by norm_num [m] : m ≤ 2^1019).trans elo
  have mpos : 0 < m := by norm_num [m]
  have dp := mpos.trans_le dm
  have ep := mpos.trans_le em
  have de := Nat.mul_pos dp ep
  have dem : m ≤ d*e := dm.trans (Nat.le_mul_of_pos_right _ ep)
  have localRate (n : ℕ) (npos : 0 < n) (cap : 12*n ≤ 2^1024) :
      (2999:ℝ)/2000 ≤ (m:ℝ)*(m-1)/(2*n) := by
    have h : (12:ℝ)*n ≤ 2^1024 := by exact_mod_cast cap
    apply (le_div_iff₀ (by positivity)).mpr
    norm_num [m] at h ⊢
    linarith
  have productUpper := mul_le_mul (distinct_probability_upper dp dm)
    (distinct_probability_upper ep em) (probability_nonneg e m) (Real.exp_pos _).le
  rw [← Real.exp_add] at productUpper
  have expBound : -(m:ℝ)*(m-1)/(2*d) + -(m:ℝ)*(m-1)/(2*e) ≤ -(2999/1000) := by
    calc
      _ = -((m:ℝ)*(m-1)/(2*d) + m*(m-1)/(2*e)) := by ring
      _ ≤ -((2999:ℝ)/2000 + 2999/2000) := neg_le_neg (add_le_add (localRate d dp dhi) (localRate e ep ehi))
      _ = _ := by norm_num
  have upper := productUpper.trans_lt ((Real.exp_le_exp.mpr expBound).trans_lt exp_threshold)
  have dR : (2:ℝ)^1019 ≤ d := by exact_mod_cast dlo
  have eR : (2:ℝ)^1019 ≤ e := by exact_mod_cast elo
  have prodLower := mul_le_mul dR eR (by positivity) (by positivity)
  have jointRate : (m:ℝ)*(m-1)/(2*(d*e:ℕ)) ≤ 1/10000 := by
    rw [Nat.cast_mul]
    apply (div_le_iff₀ (by positivity)).mpr
    norm_num [m] at prodLower ⊢
    linarith only [prodLower]
  have lower := distinct_probability_lower de dem
  linarith only [lower, upper, jointRate]

/-- Fraction of independent uniform joint output words containing a pair
that agrees in exactly one coordinate. -/
theorem full_size_proper_probability [Fintype B] [Fintype C]
    (dlo : 2^1019 ≤ Fintype.card B) (elo : 2^1019 ≤ Fintype.card C)
    (dhi : 12*Fintype.card B ≤ 2^1024) (ehi : 12*Fintype.card C ≤ 2^1024) :
    (95:ℝ)/100 < (Nat.card {w : Fin (2^511) → B × C // ProperPair w} : ℝ) /
        ((Fintype.card B * Fintype.card C : ℕ) : ℝ)^(2^511 : ℕ) := by
  exact (full_size_bound dlo elo dhi ehi).trans_le
    (proper_probability_lower _ ((by norm_num : 0 < 2^1019).trans_le dlo)
      ((by norm_num : 0 < 2^1019).trans_le elo))

/-- The size of a uniform-fiber seed space is its output size times its common fiber size. -/
theorem seed_card [Fintype A] [Fintype B] (f : A → B) {k : ℕ}
    (regular : ∀ b, Nat.card {a : A // f a = b} = k) :
    Fintype.card A = Fintype.card B * k := by
  classical
  rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv f), Fintype.card_sigma]
  have h (b : B) : Fintype.card {a : A // f a = b} = k := by
    simpa only [Nat.card_eq_fintype_card] using regular b
  simp [h]

/-- Excluding at most thirteen residues of a 1024-bit prime and partitioning
the remaining seeds into twelve-element fibers gives the required image bounds. -/
theorem image_bounds_of_twelve [Fintype A] [Fintype B] (f : A → B)
    (regular : ∀ b, Nat.card {a : A // f a = b} = 12) {p : ℕ}
    (lo : 2^1023 ≤ p) (hi : p < 2^1024) (small : Fintype.card A ≤ p)
    (many : p ≤ Fintype.card A + 13) :
    2^1019 ≤ Fintype.card B ∧ 12 * Fintype.card B ≤ 2^1024 := by
  have size := seed_card f regular
  norm_num at lo hi ⊢
  omega

/-- Uniform-fiber maps preserve probabilities of all events on the output words. -/
theorem event_probability [Fintype A] [Fintype B] (f : A → B) {k m : ℕ}
    (regular : ∀ b, Nat.card {a : A // f a = b} = k) (hk : 0 < k)
    (P : (Fin m → B) → Prop) :
    (Nat.card {w : Fin m → A // P (f ∘ w)} : ℝ) / (Fintype.card A : ℝ)^m =
      (Nat.card {v : Fin m → B // P v} : ℝ) / (Fintype.card B : ℝ)^m := by
  rw [event_card f regular P, seed_card f regular, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, mul_pow]
  have h : ((k:ℝ)^m) ≠ 0 := by positivity
  exact mul_div_mul_right _ _ h

private def productFiberEquiv {D : Type*} (f : A → B) (g : D → C) (b : B) (c : C) :
    {z : A × D // (f z.1, g z.2) = (b,c)} ≃ {a : A // f a = b} × {t : D // g t = c} where
  toFun z := (⟨z.1.1,congrArg Prod.fst z.2⟩, ⟨z.1.2,congrArg Prod.snd z.2⟩)
  invFun z := ⟨(z.1.1,z.2.1), Prod.ext z.1.2 z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A sample in the product seed space has independent uniform output coordinates. -/
theorem product_fibers {D : Type*} (f : A → B) (g : D → C) {k l : ℕ}
    (hf : ∀ b, Nat.card {a : A // f a = b} = k)
    (hg : ∀ c, Nat.card {a : D // g a = c} = l) (v : B × C) :
    Nat.card {z : A × D // (f z.1, g z.2) = v} = k*l := by
  rcases v with ⟨b,c⟩
  rw [Nat.card_congr (productFiberEquiv f g b c), Nat.card_prod, hf, hg]

/-- The full-size probability bound on independent, uniform regular seeds
with replacement, expressed directly as a ratio of seed-word counts. -/
theorem full_size_seed_probability {D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → B) (g : D → C) {k l : ℕ} (hk : 0 < k) (hl : 0 < l)
    (hf : ∀ b, Nat.card {a : A // f a = b} = k)
    (hg : ∀ c, Nat.card {a : D // g a = c} = l)
    (dlo : 2^1019 ≤ Fintype.card B) (elo : 2^1019 ≤ Fintype.card C)
    (dhi : 12*Fintype.card B ≤ 2^1024) (ehi : 12*Fintype.card C ≤ 2^1024) :
    (95:ℝ)/100 <
      (Nat.card {w : Fin (2^511) → A × D // ProperPair (fun i => (f (w i).1,g (w i).2))} : ℝ) /
        ((Fintype.card A * Fintype.card D : ℕ) : ℝ)^(2^511 : ℕ) := by
  let F (z : A × D) := (f z.1,g z.2)
  have eqn := event_probability F (product_fibers f g hf hg) (Nat.mul_pos hk hl)
    (m := 2^511) (fun w => ProperPair w)
  rw [Fintype.card_prod, Fintype.card_prod] at eqn
  exact (full_size_proper_probability dlo elo dhi ehi).trans_eq eqn.symm

set_option exponentiation.threshold 2050 in
set_option maxRecDepth 8192 in
/-- With the identity labels, even after excluding up to thirteen residues at
each 1024-bit prime, the same 2^511 uniform seed samples have success at most 7/16. -/
theorem full_size_plain_probability [Fintype B] [Fintype C]
    (bsize : 2^1023 ≤ Fintype.card B + 13) (csize : 2^1023 ≤ Fintype.card C + 13) :
    (Nat.card {w : Fin (2^511) → B × C // ProperPair w} : ℝ) /
        ((Fintype.card B * Fintype.card C : ℕ) : ℝ)^(2^511 : ℕ) ≤ 7/16 := by
  let m : ℕ := 2^511
  have enough {n : ℕ} (large : 2^1023 ≤ n+13) : 0 < n ∧ m ≤ n := by
    norm_num [m] at large ⊢
    omega
  have survive {n : ℕ} (large : 2^1023 ≤ n+13) : (3:ℝ)/4 ≤ distinctProbability n m := by
    obtain ⟨hpos,hm⟩ := enough large
    have rate : (m:ℝ)*(m-1)/(2*n) ≤ 1/4 := by
      have h : (2:ℝ)^1023 ≤ n+13 := by exact_mod_cast large
      apply (div_le_iff₀ (by positivity)).mpr
      norm_num [m] at h ⊢
      linarith only [h]
    linarith only [distinct_probability_lower hpos hm, rate]
  have both := mul_le_mul (survive bsize) (survive csize) (by norm_num) (probability_nonneg _ _)
  exact (proper_probability_upper m (enough bsize).1 (enough csize).1).trans (by linarith)

end PrimeFactors.UniformFiberBirthday
