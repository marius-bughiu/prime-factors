import PrimeFactors.ReducedSlopes
import Mathlib.Data.Nat.Squarefree
import PrimeFactors.ExceptionalWeights

namespace PrimeFactors

/-- If all supplied units lose their order after taking the Q-th power, the
number of distinct products below the hidden prime bounds gcd(p-1,Q).
The k-prime products are only counted; the search never enumerates them. -/
theorem wideModulus_order_obstruction {p k Q H Y : ℕ} (hp : p.Prime)
    (pos : 0 < H) (small : Y ^ k < p)
    (P : Finset ℕ) (primes : ∀ a ∈ P, a.Prime) (size : ∀ a ∈ P, a ≤ Y)
    (b : ℕ → (ZMod p)ˣ) (lift : ∀ a ∈ P, (b a : ZMod p) = (a : ZMod p))
    (killed : ∀ a ∈ P, (b a ^ Q) ^ H = 1) :
    P.card.choose k ≤ (p - 1).gcd Q * H := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let F := P.powersetCard k
  let image (s : Finset ℕ) := ∏ a ∈ s, b a
  have sub {s : Finset ℕ} (hs : s ∈ F) : s ⊆ P := (Finset.mem_powersetCard.mp hs).1
  have bounded {s : Finset ℕ} (hs : s ∈ F) : ∏ a ∈ s, a < p := by
    calc
      ∏ a ∈ s, a ≤ ∏ _a ∈ s, Y := Finset.prod_le_prod' (fun a ha => size a (sub hs ha))
      _ = Y ^ k := by simp [(Finset.mem_powersetCard.mp hs).2]
      _ < p := small
  have valImage {s : Finset ℕ} (hs : s ∈ F) :
      ((image s : (ZMod p)ˣ) : ZMod p).val = ∏ a ∈ s, a := by
    have eq : ((image s : (ZMod p)ˣ) : ZMod p) = ((∏ a ∈ s, a : ℕ) : ZMod p) := by
      change (Units.coeHom (ZMod p)) (∏ a ∈ s, b a) = _
      rw [map_prod, Nat.cast_prod]
      exact Finset.prod_congr rfl fun a ha => lift a (sub hs ha)
    rw [eq, ZMod.val_natCast_of_lt (bounded hs)]
  have inj : Set.InjOn image (↑F) := by
    intro x hx y hy he
    have eq : (∏ a ∈ x, a) = ∏ a ∈ y, a := by
      rw [← valImage hx, ← valImage hy, he]
    have fx := Nat.primeFactors_prod (s := x) (fun a ha => primes a (sub hx ha))
    have fy := Nat.primeFactors_prod (s := y) (fun a ha => primes a (sub hy ha))
    rw [← fx, ← fy, eq]
  let g := (p-1).gcd Q
  have gd : 0 < g := Nat.gcd_pos_of_pos_left Q (by have := hp.two_le; omega)
  have hit {s : Finset ℕ} (hs : s ∈ F) : image s ^ (g * H) = 1 := by
    have kn : image s ^ (Q*H) = 1 := by
      simp only [image, ← Finset.prod_pow]
      exact Finset.prod_eq_one fun a ha => by simpa [pow_mul] using killed a (sub hs ha)
    have oc : orderOf (image s) ∣ p-1 := (Nat.prime_iff_card_units p).mp hp ▸ orderOf_dvd_card
    have d₁ := dvd_gcd_mul_of_dvd_mul (orderOf_dvd_iff_pow_eq_one.mpr kn)
    apply orderOf_dvd_iff_pow_eq_one.mp
    exact d₁.trans (mul_dvd_mul (gcd_dvd_gcd oc (dvd_refl Q)) (dvd_refl H))
  have contained : F.image image ⊆ Finset.univ.filter (fun x : (ZMod p)ˣ => x ^ (g*H) = 1) := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hit hs⟩
  calc
    _ = F.card := Finset.card_powersetCard _ _ |>.symm
    _ = (F.image image).card := (Finset.card_image_of_injOn inj).symm
    _ ≤ _ := (Finset.card_le_card contained).trans (IsCyclic.card_pow_eq_one_le (mul_pos gd pos))

/-- The failure of the powered-order search places the actual prime in a
progression from a list computable using Q alone. -/
theorem wideModulus_order_or_progression {p k Q H Y D : ℕ} (hp : p.Prime)
    (pos : 0 < H) (small : Y ^ k < p)
    (P : Finset ℕ) (primes : ∀ a ∈ P, a.Prime) (size : ∀ a ∈ P, a ≤ Y)
    (b : ℕ → (ZMod p)ˣ) (lift : ∀ a ∈ P, (b a : ZMod p) = (a : ZMod p))
    (many : D * H < P.card.choose k) :
    (∃ a ∈ P, (b a ^ Q) ^ H ≠ 1) ∨
      ∃ d : ℕ, d ∣ Q ∧ D < d ∧ ∃ j : ℕ, p = 1+d*j := by
  by_cases allKilled : ∀ a ∈ P, (b a ^ Q) ^ H = 1
  · right
    have count := wideModulus_order_obstruction hp pos small P primes size b lift allKilled
    have large : D < (p-1).gcd Q := by
      by_contra! le
      exact (not_lt_of_ge (count.trans (Nat.mul_le_mul_right H le))) many
    obtain ⟨j, hj⟩ := Nat.gcd_dvd_left (p-1) Q
    exact ⟨_, Nat.gcd_dvd_right .., large, j, by have := hp.two_le; omega⟩
  · push_neg at allKilled
    exact Or.inl allKilled

/-- With a single balanced interval, one box works for all signs of the
weights. In particular no derivative estimate or shared sign is needed. -/
theorem wideModulus_signed_trace {p q u v s U : ℝ}
    (hp : |p| ≤ s) (hq : |q| ≤ 2*s) (hu : |u| ≤ U) (hv : |v| ≤ U) :
    |u*q+v*p| ≤ 3*s*U := by
  calc
    _ ≤ |u*q| + |v*p| := abs_add_le ..
    _ = |u| * |q| + |v| * |p| := by rw [abs_mul, abs_mul]
    _ ≤ U*(2*s)+U*s := add_le_add (mul_le_mul hu hq (abs_nonneg _) ((abs_nonneg _).trans hu))
      (mul_le_mul hv hp (abs_nonneg _) ((abs_nonneg _).trans hv))
    _ = _ := by ring

end PrimeFactors
