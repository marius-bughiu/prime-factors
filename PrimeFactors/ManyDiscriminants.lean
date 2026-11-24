import PrimeFactors.DiscriminantPencil
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.ModEq

namespace PrimeFactors

/-- The classical congruence of squares from any positive-side Fermat relation. -/
theorem midpoint_relation_modEq (n : ℕ) (ms : List ℕ) (side : ∀ a ∈ ms, n ≤ a^2) :
    Nat.ModEq n (ms.prod^2) ((ms.map (fun a => a^2-n)).prod) := by
  induction ms with
  | nil => simp [Nat.ModEq]
  | cons a as ih =>
    have ha := side a (List.mem_cons_self ..)
    have one : Nat.ModEq n (a^2) (a^2-n) := by
      apply Nat.ModEq.symm
      apply (Nat.modEq_iff_dvd' (Nat.sub_le _ _)).2
      rw [Nat.sub_sub_self ha]
    simpa only [List.prod_cons, List.map_cons, mul_pow] using
      one.mul (ih fun v hv => side v (List.mem_cons_of_mem _ hv))

/-- A reduced midpoint product strictly between r and n-r rules out both
trivial square roots, without assuming primality of the supplied input. -/
theorem midpoint_relation_split {n r : ℕ} (ms : List ℕ) (side : ∀ a ∈ ms, n ≤ a^2)
    (square : (ms.map (fun a => a^2-n)).prod = r^2)
    (lower : r < ms.prod % n) (upper : ms.prod % n + r < n) :
    let g := n.gcd (ms.prod % n - r)
    1 < g ∧ g < n ∧ g ∣ n := by
  let x := ms.prod % n
  have congruence := ((Nat.mod_modEq ms.prod n).pow 2).trans (midpoint_relation_modEq n ms side)
  rw [square] at congruence
  have divides := (Nat.modEq_iff_dvd' (Nat.pow_le_pow_left lower.le 2)).mp congruence.symm
  change n ∣ x^2-r^2 at divides
  have identity : x^2-r^2=(x-r)*(x+r) := by
    rw [Nat.sq_sub_sq, mul_comm]
  rw [identity] at divides
  change r < x at lower
  change x+r < n at upper
  have dpos : 0 < x-r := by omega
  have npos : 0 < n := by omega
  change 1 < n.gcd (x-r) ∧ n.gcd (x-r) < n ∧ n.gcd (x-r) ∣ n
  have bound := Nat.le_of_dvd dpos (Nat.gcd_dvd_right n (x-r))
  refine ⟨lt_of_not_ge ?_, bound.trans_lt (by omega), Nat.gcd_dvd_left n (x-r)⟩
  intro small
  have positive := Nat.gcd_pos_of_pos_left (x-r) npos
  have cop : n.Coprime (x-r) := show n.gcd (x-r) = 1 by omega
  exact (Nat.not_dvd_of_pos_of_lt (by omega) upper) (cop.dvd_of_dvd_mul_left divides)

/-- A condition on the product, starting midpoint and window width certifies
that every three-term square relation in the window gives a proper split.
One can take m = ceilSqrt n and d = m²-n. -/
theorem triple_window_split {n m d K R t i j k r : ℕ} (start : m^2 = n+d)
    (rootCap : (d+2*m*K+K^2)^3 ≤ R^2)
    (left : t*n+R < m*d)
    (right : m*d + (3*d*K+3*m*K^2+K^3) + R < (t+1)*n)
    (hi : i ≤ K) (hj : j ≤ K) (hk : k ≤ K)
    (square : ((m+i)^2-n)*((m+j)^2-n)*((m+k)^2-n) = r^2) :
    let g := n.gcd (((m+i)*(m+j)*(m+k))%n-r)
    1 < g ∧ g < n ∧ g ∣ n := by
  let L := d+2*m*K+K^2
  let E := d*(i+j+k)+m*(i*j+i*k+j*k)+i*j*k
  let V := m*d+E
  have ds (w : ℕ) : (m+w)^2 = n + (d+2*m*w+w^2) := by nlinarith only [start]
  have dCap (w : ℕ) (hw : w ≤ K) : (m+w)^2-n ≤ L := by
    rw [ds, Nat.add_sub_cancel_left]
    dsimp [L]
    gcongr
    omega
  have rCap : r ≤ R := by
    apply Nat.mul_self_le_mul_self_iff.mp
    rw [← pow_two, ← pow_two, ← square]
    apply (Nat.mul_le_mul (Nat.mul_le_mul (dCap i hi) (dCap j hj)) (dCap k hk)).trans
    simpa only [L, pow_succ, pow_zero, one_mul] using rootCap
  have eCap : E ≤ 3*d*K+3*m*K^2+K^3 := by
    calc
      E ≤ d*(K+K+K)+m*(K*K+K*K+K*K)+K*K*K := by dsimp [E]; gcongr
      _ = _ := by ring
  have low : t*n+R < V := by dsimp [V]; omega
  have up : V+R < t*n+n := by dsimp [V]; rw [Nat.add_mul, one_mul] at right; omega
  have val : V-t*n+t*n = V := Nat.sub_add_cancel (by omega)
  have expand : (m+i)*(m+j)*(m+k) = V+n*(m+i+j+k) := by
    rw [show (m+i)*(m+j)*(m+k) =
      m^2*(m+i+j+k) + m*(i*j+i*k+j*k) + i*j*k by ring, start]
    dsimp [V,E]
    ring
  have red : ((m+i)*(m+j)*(m+k))%n = V-t*n := by
    rw [expand, Nat.add_mul_mod_self_left]
    calc
      V%n = ((V-t*n)+t*n)%n := congrArg (· % n) val.symm
      _ = V-t*n := by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have side : ∀ a ∈ [m+i,m+j,m+k], n ≤ a^2 := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> rw [ds] <;> omega
  have split := midpoint_relation_split (n := n) (r := r) [m+i,m+j,m+k] side
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ← mul_assoc] at split
  exact split square (red ▸ (by omega)) (red ▸ (by omega))

/-- Checking the product-only gate at the first three midpoints certifies
that their square product must give a proper divisor of 723889. -/
theorem triple_window_723889 :
    let g := Nat.gcd 723889 ((851*852*853)%723889-48360)
    1 < g ∧ g < 723889 ∧ g ∣ 723889 := by
  apply triple_window_split (m := 851) (d := 312) (K := 2) (R := 226890)
    (t := 0) (i := 0) (j := 1) (k := 2) <;> decide

theorem triple_factor_723889 :
    (312*2015*3720:ℕ) = 48360^2 ∧ Nat.gcd 723889 ((851*852*853)%723889-48360) = 709 ∧
    723889 = 709*1021 ∧ Nat.Prime 709 ∧ Nat.Prime 1021 := by
  refine ⟨by decide, by decide, by decide, by norm_num, by norm_num⟩

/-- Possible inputs supporting two distinct positive Fermat discriminants
dividing r². The paired divisors and the midpoint distance determine the input. -/
noncomputable def relationInputs (r : ℕ) : Finset ℕ :=
  (r^2).divisors.biUnion fun d => (r^2).divisors.biUnion fun e =>
    (e-d).divisors.image fun k => (((e-d)/k-k)/2)^2-d

/-- This witness enumeration covers relations of any length, with or without
repetitions, provided at least two midpoint positions are distinct. -/
theorem mem_relationInputs {n r a c : ℕ} (ms : List ℕ) (hr : 0 < r)
    (ma : a ∈ ms) (mc : c ∈ ms) (side : n < a^2) (ordered : a < c)
    (square : (ms.map (fun v => v^2-n)).prod = r^2) :
    n ∈ relationInputs r := by
  let d := a^2-n
  let e := c^2-n
  let k := c-a
  have ac := Nat.pow_lt_pow_left ordered (show 2 ≠ 0 by decide)
  have steppos : 0 < k := Nat.sub_pos_of_lt ordered
  have epos : d < e := by dsimp [d,e]; omega
  have difference : e-d = k*(c+a) := by
    dsimp [d,e,k]
    rw [show c^2-n-(a^2-n) = c^2-a^2 by omega, Nat.sq_sub_sq, mul_comm]
  have recover : (e-d)/k = c+a := by rw [difference, Nat.mul_div_cancel_left _ steppos]
  have witness (v : ℕ) (hv : v ∈ ms) : v^2-n ∈ (r^2).divisors := by
    apply Nat.mem_divisors.mpr
    refine ⟨?_, by positivity⟩
    rw [← square]
    exact List.dvd_prod (List.mem_map.mpr ⟨v,hv,rfl⟩)
  apply Finset.mem_biUnion.mpr
  refine ⟨d, witness a ma, Finset.mem_biUnion.mpr ⟨e, witness c mc, ?_⟩⟩
  apply Finset.mem_image.mpr
  refine ⟨k, Nat.mem_divisors.mpr ⟨⟨c+a,difference⟩, Nat.sub_ne_zero_of_lt epos⟩, ?_⟩
  rw [recover, show (c+a-k)/2 = a by dsimp [k]; omega]
  exact Nat.sub_sub_self side.le

/-- For a fixed square root, count candidate inputs by the choices of two
divisors of r² and one divisor of their difference. -/
theorem card_relationInputs_le {r T : ℕ}
    (divisorBound : ∀ j ≤ r^2, j.divisors.card ≤ T) :
    (relationInputs r).card ≤ (r^2).divisors.card ^ 2 * T := by
  unfold relationInputs
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _d ∈ (r^2).divisors, (r^2).divisors.card * T := by
      apply Finset.sum_le_sum
      intro d _
      apply Finset.card_biUnion_le.trans
      calc
        _ ≤ ∑ _e ∈ (r^2).divisors, T := by
          apply Finset.sum_le_sum
          intro e he
          exact Finset.card_image_le.trans <| divisorBound (e-d) ((Nat.sub_le ..).trans (Nat.divisor_le he))
        _ = _ := by simp
    _ = _ := by simp [pow_two, Nat.mul_assoc]

/-- A three-term primitive relation has the negative trivial congruence even
at parity-compatible midpoints of a balanced semiprime. -/
theorem trivial_triple_20099 :
    20099 = 101*199 ∧ Nat.Prime 101 ∧ Nat.Prime 199 ∧
    ([142,144,148].map (fun a : ℕ => a^2-20099)) = [65,637,1805] ∧
    (65*637*1805:ℕ) = 8645^2 ∧
    (142*144*148:ℕ)%20099 + 8645 = 20099 ∧
    Nat.gcd 20099 (142*144*148 - 8645) = 1 ∧
    [65,637,1805].all (fun j : ℕ => j.sqrt^2 != j) = true := by
  refine ⟨by decide, by norm_num, by norm_num, by decide, by decide, by decide, by decide, ?_⟩
  norm_num [List.all]

/-- A four-term relation can give the positive trivial congruence while every
one- and two-term subproduct is nonsquare. -/
theorem trivial_quadruple_96673 :
    96673 = 277*349 ∧ Nat.Prime 277 ∧ Nat.Prime 349 ∧
    ([315,317,319,323].map (fun a : ℕ => a^2-96673)) = [2552,3816,5088,7656] ∧
    (2552*3816*5088*7656:ℕ) = 19476864^2 ∧
    (315*317*319*323:ℕ)%96673 = 19476864%96673 ∧
    Nat.gcd 96673 (315*317*319*323 + 19476864) = 1 ∧
    [2552,3816,5088,7656,2552*3816,2552*5088,2552*7656,3816*5088,3816*7656,5088*7656].all
      (fun j : ℕ => j.sqrt^2 != j) = true := by
  refine ⟨by decide, by norm_num, by norm_num, by decide, by decide, by decide, by decide, ?_⟩
  norm_num [List.all]

end PrimeFactors
