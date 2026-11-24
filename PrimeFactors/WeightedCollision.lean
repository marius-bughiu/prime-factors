import Mathlib.Tactic.ReduceModChar
import PrimeFactors.Multiplier
import PrimeFactors.PowerSignature

namespace PrimeFactors

/-- A weighted exponent is known modulo the order of a unit at the smaller
prime. Its product-derived exponent is asymmetric in the two weights. -/
theorem weighted_power_at_prime {p : ℕ} (hp : p.Prime) (q a b : ℕ) (v : (ZMod p)ˣ) :
    v ^ (a * p + b * q) = v ^ (a + b * (p * q)) := by
  letI : Fact p.Prime := ⟨hp⟩
  have frob : v ^ p = v := Units.ext (by simpa only [Units.val_pow_eq_pow_val] using ZMod.pow_card (v : ZMod p))
  rw [show a * p + b * q = p * a + b * q by ring,
    show a + b * (p * q) = a + p * (b * q) by ring]
  simp only [pow_add, pow_mul, frob]

/-- One baby table serves every rational multiplier window. Both table entries
are computed modulo the given product; their reductions agree modulo p. -/
theorem exists_weighted_collision {p q K m : ℕ} (hp : p.Prime)
    (ordered : p ≤ q) (balanced : q ≤ 2 * p) (hK : 0 < K) (hm : 0 < m)
    (u : (ZMod (p * q))ˣ) :
    ∃ a b i j : ℕ, 0 < b ∧ b ≤ K ∧ b ≤ a ∧ a ≤ 2 * b ∧ i < m ∧
      j ≤ (p * q).sqrt / (2 * b * (K + 1)^2) / m ∧
      let c := ceilSqrt (4 * a * b * (p * q))
      let π := ZMod.unitsMap (dvd_mul_right p q)
      c + m * j + i = a * p + b * q ∧
      π (u ^ i) = π (u ^ (a + b * (p * q)) / (u ^ c * (u ^ m) ^ j)) := by
  obtain ⟨a, b, hb, hbK, hba, hab, lo, hi⟩ := exists_balanced_multiplier_window hp.pos ordered balanced hK
  let c := ceilSqrt (4 * a * b * (p * q))
  let d := a * p + b * q - c
  change c ≤ a * p + b * q at lo
  change a * p + b * q ≤ c + _ at hi
  have bd : d ≤ (p * q).sqrt / (2 * b * (K + 1)^2) := by dsimp [d]; omega
  have add : c + m * (d / m) + d % m = a * p + b * q := by
    have := Nat.mod_add_div d m
    dsimp [d] at *
    omega
  refine ⟨a, b, d % m, d / m, hb, hbK, hba, hab, Nat.mod_lt _ hm,
    Nat.div_le_div_right bd, add, ?_⟩
  simp only [map_pow, map_div, map_mul]
  apply (power_table_match_iff _ _ _ _ _ _).mpr
  rw [add]
  exact weighted_power_at_prime hp _ _ _ _

/-- The giant table includes exactly one entry per window per block,
including its last (possibly incomplete) block. -/
noncomputable def weightedGiantCount (n K m : ℕ) : ℕ :=
  ∑ i ∈ Finset.range K, (i + 2) * (1 + n.sqrt / (2 * (i + 1) * (K + 1)^2) / m)

/-- The balanced construction has O(K²) giant entries when sqrt(n) ≤ (K+1)^5
and uses (K+1)^2 babies. No prime factor occurs in the construction parameters. -/
theorem weightedGiantCount_le {n K : ℕ} (scale : n.sqrt ≤ (K + 1)^5) :
    weightedGiantCount n K ((K+1)^2) ≤ 2 * K * (K+1) := by
  unfold weightedGiantCount
  calc
    _ ≤ ∑ _i ∈ Finset.range K, 2 * (K+1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiK := Finset.mem_range.mp hi
      let h := (K+1)^2
      let w := n.sqrt / (2 * (i+1) * h) / h
      have hw : w * (2 * (i+1) * h * h) ≤ (K+1)^5 := by
        dsimp only [w]
        rw [Nat.div_div_eq_div_mul]
        exact (Nat.div_mul_le_self _ _).trans scale
      have granularity : ((i+2) * w) * (h*h) ≤ (K+1) * (h*h) := calc
        _ ≤ (2 * (i+1) * w) * (h*h) := by gcongr; omega
        _ = w * (2 * (i+1) * h * h) := by ring
        _ ≤ (K+1)^5 := hw
        _ = _ := by dsimp only [h]; ring
      have hpos : 0 < h := by dsimp [h]; positivity
      have := Nat.le_of_mul_le_mul_right granularity (Nat.mul_pos hpos hpos)
      change (i+2) * (1+w) ≤ 2 * (K+1)
      rw [Nat.mul_add, Nat.mul_one]
      omega
    _ = _ := by simp; ring

/-- Number of values in a cyclic group whose order might spoil baby-step
uniqueness. This finite union bound gives a factor-independent random base
selection policy once applied to the uniform projection to (Z/pZ)ˣ. -/
theorem count_short_order_le {G : Type*} [Group G] [Fintype G] [DecidableEq G] [IsCyclic G]
    (m : ℕ) :
    (Finset.univ.filter (fun u : G => orderOf u ≤ m)).card ≤ ∑ i ∈ Finset.range m, (i+1) := by
  classical
  let roots := fun i : ℕ => Finset.univ.filter (fun u : G => u^(i+1) = 1)
  calc
    _ ≤ ((Finset.range m).biUnion roots).card := by
      apply Finset.card_le_card
      intro u hu
      have bound := (Finset.mem_filter.mp hu).2
      have pos := orderOf_pos u
      refine Finset.mem_biUnion.mpr ⟨orderOf u - 1, Finset.mem_range.mpr (by omega), ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [Nat.sub_add_cancel (by omega : 1 ≤ orderOf u), pow_orderOf_eq_one]⟩
    _ ≤ _ := (Finset.card_biUnion_le).trans <| Finset.sum_le_sum fun i _ =>
      IsCyclic.card_pow_eq_one_le (Nat.succ_pos i)

/-- Even with one block per slope, the admissible pairs alone cost quadratically in K. -/
private theorem slope_count_le_giants (n K m : ℕ) :
    K ^ 2 ≤ 2 * weightedGiantCount n K m := by
  have floor : K^2 ≤ 2 * ∑ i ∈ Finset.range K, (i+2) := by
    induction K with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      nlinarith
  apply floor.trans
  apply Nat.mul_le_mul_left
  apply Finset.sum_le_sum
  intro i _
  change i + 2 ≤ (i+2) * (1+_)
  exact Nat.le_mul_of_pos_right _ (Nat.add_pos_left Nat.zero_lt_one _)

/-- Matching lower bound for these explicit table lengths. Rechoosing the
stride and slope cutoff cannot reduce their joint exponent below one fifth. -/
theorem weighted_table_lower {n K m : ℕ} (hk : 0 < K) (hm : 0 < m) :
    n < 128 * (weightedGiantCount n K m + m)^5 := by
  let g := weightedGiantCount n K m
  let s := g + m
  let h := (K+1)^2
  have coverage : K * (n.sqrt + 1) ≤ 2 * h * m * g := by
    have term (i : ℕ) : n.sqrt + 1 ≤ (2*h*m) * ((i+2)*(1+n.sqrt/(2*(i+1)*h)/m)) := by
      let d := 2 * (i+1) * h * m
      have hd : 0 < d := by dsimp [d, h]; positivity
      have next : n.sqrt < (n.sqrt / d + 1) * d :=
        (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self _)
      rw [Nat.div_div_eq_div_mul]
      change n.sqrt + 1 ≤ (2*h*m) * ((i+2)*(1+n.sqrt/d))
      calc
        _ ≤ (n.sqrt / d + 1) * d := by omega
        _ = (2*h*m) * ((i+1)*(1+n.sqrt/d)) := by dsimp only [d]; ring
        _ ≤ _ := by gcongr; omega
    simpa [g, weightedGiantCount, Finset.mul_sum, h, Nat.mul_comm K] using
      Finset.sum_le_sum (s := Finset.range K) (fun i _ => term i)
  have scale : 2 * h ≤ K * (8*K) := by
    have bound := Nat.pow_le_pow_left (by omega : K + 1 ≤ 2 * K) 2
    dsimp [h]; nlinarith
  have root : n.sqrt + 1 ≤ 8 * K * m * g := by
    apply Nat.le_of_mul_le_mul_left _ hk
    calc
      K * (n.sqrt + 1) ≤ _ := coverage
      _ ≤ (K * (8*K)) * m * g := by gcongr
      _ = _ := by ring
  have sq := Nat.pow_le_pow_left root 2
  have area : K^2 ≤ 2*g := slope_count_le_giants n K m
  have gs : g ≤ s := by dsimp [s]; omega
  have ms : m ≤ s := by dsimp [s]; omega
  calc
    n < (n.sqrt + 1)^2 := by simpa [pow_two] using Nat.lt_succ_sqrt n
    _ ≤ (8 * K * m * g)^2 := sq
    _ = 64 * K^2 * m^2 * g^2 := by ring
    _ ≤ 64 * (2*s) * s^2 * s^2 := by gcongr; exact area.trans (Nat.mul_le_mul_left _ gs)
    _ = _ := by change _ = 128 * s^5; ring

/-- Distinct representatives colliding modulo a hidden divisor directly reveal
a proper gcd. Equal representatives require the separate weighted-square test. -/
theorem weighted_collision_proper_gcd {n p x y : ℕ} (hp : 1 < p) (factor : p ∣ n)
    (hx : x < n) (hy : y < n) (apart : x ≠ y) (matchAt : x ≡ y [MOD p]) :
    1 < Nat.gcd (Nat.dist x y) n ∧ Nat.gcd (Nat.dist x y) n < n := by
  have dpos : 0 < Nat.dist x y := Nat.pos_of_ne_zero (by
    intro h
    exact apart (Nat.eq_of_dist_eq_zero h))
  have factors : p ∣ Nat.dist x y := by
    rcases le_total x y with h | h
    · rw [Nat.dist_eq_sub_of_le h]
      exact (Nat.modEq_iff_dvd' h).mp matchAt
    · rw [Nat.dist_eq_sub_of_le_right h]
      exact (Nat.modEq_iff_dvd' h).mp matchAt.symm
  have small : Nat.dist x y < n := by
    rcases le_total x y with h | h
    · rw [Nat.dist_eq_sub_of_le h]; omega
    · rw [Nat.dist_eq_sub_of_le_right h]; omega
  exact ⟨hp.trans_le (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ dpos) (Nat.dvd_gcd factors factor)),
    (Nat.le_of_dvd dpos (Nat.gcd_dvd_left _ _)).trans_lt small⟩

/-- A collision invisible to a sort modulo the product. With weights (3,2),
base 2, stride 9 and block 0, the observed residues are 16 and 23443. -/
theorem weighted_collision_example :
    (2 : ZMod 34387) ^ (3 + 2 * 34387 - 909) = 23443 ∧
    (2 : ZMod 34387) ^ 4 = 16 ∧
    Nat.gcd (23443 - 16) 34387 = 137 ∧ 137 * 251 = 34387 := by
  constructor
  · change (2 : ZMod 34387)^67868 = 23443
    norm_num
    reduce_mod_char
  · norm_num

end PrimeFactors
