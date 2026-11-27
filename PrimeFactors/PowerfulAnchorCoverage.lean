import PrimeFactors.SquareAnchorCoverage

/-! Count all squareful anchors (numbers of the form a²b³) in the
complementary-divisor prime-sum readout, with the anchor and divisor freely chosen. -/
namespace PrimeFactors.PowerfulAnchorCoverage

open Finset MixedPrefixSample SquareAnchorCoverage
set_option exponentiation.threshold 8192
set_option maxRecDepth 8192

def Powerful (m : ℕ) : Prop := ∃ a b : ℕ, m = a^2*b^3

private theorem exponent_decomposition {e : ℕ} (ne : e ≠ 1) :
    e = 2*((e-3*(e%2))/2) + 3*(e%2) := by omega

/-- Every positive number whose prime exponents are never one admits the
square-times-cube representation, including primes with exponent zero. -/
theorem of_factorization {m : ℕ} (pos : 0 < m) (h : ∀ p, m.factorization p ≠ 1) :
    Powerful m := by
  let S := m.factorization.support
  refine ⟨∏ p ∈ S, p^((m.factorization p-3*(m.factorization p%2))/2),
    ∏ p ∈ S, p^(m.factorization p%2), ?_⟩
  calc
    m = ∏ p ∈ S, p^m.factorization p := (Nat.factorization_prod_pow_eq_self pos.ne').symm
    _ = ∏ p ∈ S, (p^((m.factorization p-3*(m.factorization p%2))/2))^2 *
          (p^(m.factorization p%2))^3 := by
      apply prod_congr rfl
      intro p _
      conv_lhs => rw [exponent_decomposition (h p)]
      rw [pow_add, pow_mul', pow_mul']
    _ = _ := by simp only [prod_mul_distrib, prod_pow]

theorem of_perfect_power (x k : ℕ) (order : 2 ≤ k) : Powerful (x^k) := by
  refine ⟨x^((k-3*(k%2))/2), x^(k%2), ?_⟩
  conv_lhs => rw [exponent_decomposition (by omega : k ≠ 1)]
  rw [pow_add, pow_mul', pow_mul']

private def shell (U i : ℕ) : Finset (ℕ×ℕ) :=
  Ico (4^i) (4^i*4) ×ˢ Icc 1 (U/8^i)

/-- Each shell restricts b first and then the number of possibilities for a. -/
private theorem in_shell {a b U K : ℕ} (pa : 0 < a) (pb : 0 < b) (bk : b < 4^K)
    (size : a^2*b^3 ≤ U^2) : ∃ i ∈ range K, (b,a) ∈ shell U i := by
  let i := Nat.log 4 b
  have lb : 4^i ≤ b := Nat.pow_log_le_self 4 pb.ne'
  have scale : ((8:ℕ)^i)^2 = ((4:ℕ)^i)^3 := by
    rw [pow_right_comm (8:ℕ) i 2, pow_right_comm (4:ℕ) i 3]
    rfl
  have sq : (a*8^i)^2 ≤ U^2 := by
    rw [mul_pow, scale]
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left lb 3)).trans size
  refine ⟨i, mem_range.mpr (Nat.log_lt_of_lt_pow pb.ne' bk), mem_product.mpr
    ⟨mem_Ico.mpr ⟨lb, ?_⟩, mem_Icc.mpr ⟨pa, ?_⟩⟩⟩
  · simpa only [pow_succ] using Nat.lt_pow_succ_log_self (by decide : 1 < 4) b
  · exact (Nat.le_div_iff_mul_le (by positivity)).mpr ((Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp sq)

private theorem shell_count (U i : ℕ) : (shell U i).card ≤ 3*(U/2^i) := by
  have size : 4^i*(U/8^i) ≤ U/2^i := by
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    calc
      _ = (U/8^i)*((4:ℕ)*2)^i := by rw [mul_pow]; ring
      _ ≤ _ := Nat.div_mul_le_self U (8^i)
  simpa [shell, Nat.card_Ico, Nat.card_Icc, show (4:ℕ)^i*4-4^i = 3*4^i by omega,
    Nat.mul_assoc] using (Nat.mul_le_mul_left 3 size)

/-- A finite set of positive powerful anchors with b < 4^K and m ≤ U²
has at most 6U members. K contributes no logarithmic loss. -/
theorem anchor_count (s : Finset ℕ) (U K : ℕ)
    (params : ∀ m ∈ s, ∃ a b : ℕ, 0<a ∧ 0<b ∧ b<4^K ∧ m=a^2*b^3 ∧ m≤U^2) :
    s.card ≤ 6*U := by
  let boxes := (range K).biUnion (shell U)
  have sub : s ⊆ boxes.image (fun z => z.2^2*z.1^3) := by
    intro m hm
    obtain ⟨a,b,pa,pb,bk,eq,bound⟩ := params m hm
    obtain ⟨i,ik,mem⟩ := in_shell pa pb bk (eq ▸ bound)
    exact mem_image.mpr ⟨(b,a), mem_biUnion.mpr ⟨i,ik,mem⟩, eq.symm⟩
  have count : boxes.card ≤ ∑ i ∈ range K, 3*(U/2^i) :=
    card_biUnion_le.trans (sum_le_sum (fun i _ => shell_count U i))
  have geom : ∑ i ∈ range K, U/2^i ≤ U*2 := by simpa using Nat.geom_sum_le (by decide : 2 ≤ 2) U K
  rw [← mul_sum] at count
  exact (card_le_card sub).trans (card_image_le.trans (count.trans
    ((Nat.mul_le_mul_left 3 geom).trans_eq (by ring))))

open Classical in
noncomputable def anchors := (Ico 1 (2^2049)).filter Powerful

def readable (z : ℕ×ℕ) : Prop :=
  ∃ m g : ℕ, Powerful m ∧ g∣m ∧ predProduct z + g = m

open Classical in
noncomputable def pairs := eligible.filter readable

attribute [local irreducible] pairs anchors MixedPrefixSample.eligible MixedPrefixSample.sample
  MixedPrefixSample.ordered MixedPrefixSample.primes

private abbrev U : ℕ := 3*2^1023

private theorem anchors_count : anchors.card ≤ 6*U := by
  classical
  apply anchor_count _ _ 1025
  intro m hm
  rw [anchors, mem_filter, mem_Ico] at hm
  obtain ⟨⟨mp,top⟩,a,b,eq⟩ := hm
  have pa : 0<a := Nat.pos_of_ne_zero (fun h => by subst a; simp at eq; omega)
  have pb : 0<b := Nat.pos_of_ne_zero (fun h => by subst b; simp at eq; omega)
  have bm : b≤m := by
    rw [eq]
    exact (Nat.le_self_pow (by decide : 3 ≠ 0) b).trans (Nat.le_mul_of_pos_left _ (pow_pos pa 2))
  refine ⟨a,b,pa,pb, bm.trans_lt (top.trans_le (by decide +kernel)),eq,?_⟩
  exact top.le.trans (by decide +kernel : 2^2049 ≤ U^2)

private theorem pred_bounds {z : ℕ×ℕ} (inside : z ∈ eligible) :
    0 < predProduct z ∧ predProduct z < 2^2048 := by
  rw [eligible, sample, mem_filter] at inside
  obtain ⟨p,q,_⟩ := (mem_ordered.mp inside.1)
  rw [primes,mem_filter,mem_Ico] at p q
  have size : 2*X=2^1024 := by decide +kernel
  have pp := p.2.one_lt
  have qp := q.2.one_lt
  rw [size] at p q
  refine ⟨Nat.mul_pos (by omega) (by omega),?_⟩
  rw [show (2:ℕ)^2048=2^1024*2^1024 by decide +kernel]
  exact Nat.mul_lt_mul_of_lt_of_le (by omega : z.1-1<2^1024)
    (by omega : z.2-1≤2^1024) (by positivity)

private theorem mem_anchors {m : ℕ} : m ∈ anchors ↔ (1 ≤ m ∧ m < 2^2049) ∧ Powerful m := by
  classical
  rw [anchors, mem_filter, mem_Ico]

private theorem subset_anchors : pairs ⊆ eligible.filter
    (fun z => predProduct z ∈ anchors.biUnion valuesAt) := by
  classical
  intro z hz
  rw [pairs,mem_filter] at hz
  obtain ⟨inside,m,g,power,dvd,eq⟩ := hz
  obtain ⟨pos,bound⟩ := pred_bounds inside
  have positive : 0 < m := by omega
  have lim := (anchor_limit pos eq dvd).2.2
  have cap : m<2^2049 := lim.trans_lt (by
    simpa only [show (2:ℕ)^2049=2*2^2048 by decide +kernel] using Nat.mul_lt_mul_of_pos_left bound (by decide : 0<2))
  have mem := mem_anchors.mpr ⟨⟨positive,cap⟩,power⟩
  have v : predProduct z ∈ valuesAt m := by
    rw [valuesAt]
    exact mem_image.mpr ⟨g,Nat.mem_divisors.mpr ⟨dvd,positive.ne'⟩,by omega⟩
  exact mem_filter.mpr ⟨inside,mem_biUnion.mpr ⟨m,mem,v⟩⟩

private theorem covered_count : pairs.card ≤ anchors.card*2^480 :=
  (card_le_card subset_anchors).trans (menu_capacity anchors (fun _ hm => (mem_anchors.mp hm).1.2))

private theorem scale_count {s c n : ℕ} (population : 2^2046 < 21000000*n)
    (found : s ≤ c*2^480) (dict : c ≤ 6*U) : 2^514*s < n := by
  have small : 21000000*2^514*(6*U*2^480) ≤ 2^2046 := by decide +kernel
  apply Nat.lt_of_mul_lt_mul_left (a := 21000000)
  have size := found.trans (Nat.mul_le_mul_right _ dict)
  calc
    21000000*(2^514*s) ≤ 21000000*2^514*(6*U*2^480) := by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ size
    _ < _ := small.trans_lt population

/-- Uniform over all eligible unordered prime pairs, every squareful number
at every signed distance, and every divisor of the chosen squareful number. -/
theorem all_powerful_frequency : 2^514*pairs.card < eligible.card :=
  scale_count ChebyshevPrimeSample.eligible_count covered_count anchors_count

/-- This nonsquare cube permits a divisor readout on a pair that every
square anchor misses. The finite check covers all possible square roots. -/
theorem cube_example : Nat.Prime 257 ∧ Nat.Prime 331 ∧ 257*331 = 85067 ∧
    Powerful (44^3) ∧ 704 ∣ 44^3 ∧ predProduct (257,331)+704=44^3 ∧
    ¬ IsSquare (44^3 : ℕ) ∧ ¬ SquareAnchorCoverage.readable (257,331) := by
  refine ⟨by decide, by decide, by decide, of_perfect_power 44 3 (by decide),
    by decide, by decide, ?_, ?_⟩
  · rintro ⟨v,h⟩
    have up : v≤291 := by
      by_contra! hv
      have := Nat.mul_le_mul hv hv
      omega
    have := Nat.mul_le_mul up up
    omega
  · rintro ⟨r,g,dvd,eq⟩
    change 84480+g = r^2 at eq
    have hin := anchor_limit (by decide : 0<84480) eq dvd
    have rbound : r < 412 := by
      by_contra! large
      have := Nat.pow_le_pow_left large 2
      omega
    have compiled : ∀ i ∈ range 412, ¬(84480 < i^2 ∧ 84480 % (i^2-84480)=0) := by
      decide +kernel
    apply compiled r (mem_range.mpr rbound)
    exact ⟨by omega,by rw [←eq,Nat.add_sub_cancel_left]; exact Nat.mod_eq_zero_of_dvd hin.2.1⟩

end PrimeFactors.PowerfulAnchorCoverage
