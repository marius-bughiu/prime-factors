import PrimeFactors.CyclotomicPeriods
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

namespace PrimeFactors

/-- `split = true` selects the split quadratic algebra with group order `r-1`. -/
def signedTorusOrder (r : ℕ) (split : Bool) : ℕ := if split then r - 1 else r + 1

def torusSign (split : Bool) : ℤ := if split then 1 else -1

/-- The public Jacobi symbol selects the correct global exponent without either local sign. -/
theorem jacobi_torus_exponent (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime]
    (D : ℤ) (s t : Bool) (left : legendreSym p D = torusSign s)
    (right : legendreSym q D = torusSign t) :
    (if jacobiSym D (p * q) = 1 then p * q - 1 else p * q + 1) =
      signedTorusOrder (p * q) (s == t) := by
  rw [jacobiSym.mul_right' D hp.out.ne_zero hq.out.ne_zero,
    ← jacobiSym.legendreSym.to_jacobiSym p, ← jacobiSym.legendreSym.to_jacobiSym q, left, right]
  cases s <;> cases t <;> simp [torusSign, signedTorusOrder]

/-- Frobenius acts on a square root by the local Legendre symbol, including in a split algebra. -/
theorem quadratic_frobenius {p : ℕ} [Fact p.Prime] (odd : Odd p) {R : Type*} [CommRing R]
    [Algebra (ZMod p) R] [CharP R p] (D : ℤ) (w : R)
    (root : w ^ 2 = algebraMap (ZMod p) R (D : ZMod p)) (a b : ZMod p) :
    (algebraMap (ZMod p) R a + algebraMap (ZMod p) R b * w) ^ p =
      algebraMap (ZMod p) R a +
        algebraMap (ZMod p) R b * (algebraMap (ZMod p) R (legendreSym p D : ZMod p) * w) := by
  have hw : w ^ p = algebraMap (ZMod p) R (legendreSym p D : ZMod p) * w := by
    calc
      w ^ p = w ^ (2 * (p / 2) + 1) := by
        have h := Nat.odd_iff.mp odd
        congr 1; omega
      _ = (w ^ 2) ^ (p / 2) * w := by rw [pow_succ, pow_mul]
      _ = _ := by rw [root, ← map_pow, ← legendreSym.eq_pow]
  rw [add_pow_char _ _ p, mul_pow, ← map_pow, ← map_pow, ZMod.pow_card, ZMod.pow_card, hw]

/-- A norm-one unit is killed by `p-1` or `p+1` according to the local sign. -/
theorem norm_one_signed_power {p : ℕ} [hp : Fact p.Prime] (odd : Odd p) {R : Type*} [CommRing R]
    [Algebra (ZMod p) R] [CharP R p] (D : ℤ) (s : Bool) (hs : legendreSym p D = torusSign s)
    (w : R) (root : w ^ 2 = algebraMap (ZMod p) R (D : ZMod p)) (a b : ZMod p) (u : Rˣ)
    (value : (u : R) = algebraMap (ZMod p) R a + algebraMap (ZMod p) R b * w)
    (conjugate : (↑(u⁻¹) : R) = algebraMap (ZMod p) R a - algebraMap (ZMod p) R b * w) :
    u ^ signedTorusOrder p s = 1 := by
  have hf := quadratic_frobenius odd D w root a b
  rw [← value, hs] at hf
  cases s with
  | false =>
    change u ^ (p + 1) = 1
    have h : u ^ p = u⁻¹ := by
      apply Units.ext
      simpa [torusSign, conjugate, sub_eq_add_neg] using hf
    rw [pow_succ, h, inv_mul_cancel]
  | true =>
    change u ^ (p - 1) = 1
    have h : u ^ p = u := by
      apply Units.ext
      simpa [torusSign, ← value] using hf
    apply mul_right_cancel (b := u)
    simpa [← pow_succ, Nat.sub_add_cancel hp.out.one_le] using h

private theorem gcd_of_sum_multiple {A E Q z : ℕ} (sum : E + Q = A * z) :
    A.gcd E = A.gcd Q := by
  apply Nat.dvd_antisymm
  · refine Nat.dvd_gcd (Nat.gcd_dvd_left ..) ((Nat.dvd_add_iff_right (Nat.gcd_dvd_right ..)).mpr ?_)
    rw [sum]
    exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left ..) z
  · refine Nat.dvd_gcd (Nat.gcd_dvd_left ..) ((Nat.dvd_add_iff_left (Nat.gcd_dvd_right ..)).mpr ?_)
    rw [sum]
    exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left ..) z

/-- The known exponent has exactly the same gcd with each local group size as does
the group size at the other prime. This covers all four splitting patterns. -/
theorem signedTorus_gcd {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (s t : Bool) :
    (signedTorusOrder p s).gcd (signedTorusOrder (p*q) (s == t)) =
      (signedTorusOrder p s).gcd (signedTorusOrder q t) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  have pred : (a+1)*(b+1)-1 = a*(b+1)+b := by rw [Nat.add_mul, one_mul]; omega
  cases s <;> cases t <;> simp only [signedTorusOrder,
    Bool.false_eq_true, ↓reduceIte, Bool.true_beq, Bool.false_beq, Bool.not_true,
    Bool.not_false, Nat.succ_sub_one, pred]
  · apply gcd_of_sum_multiple (z := b + 1)
    simp only [Nat.succ_eq_add_one]
    ring
  · apply gcd_of_sum_multiple (z := b + 1)
    simp only [Nat.succ_eq_add_one]
    ring
  · rw [show (a+1)*(b+1)+1 = (b+1+1)+a*(b+1) by ring, Nat.gcd_add_mul_left_right]
  · rw [Nat.add_comm (a*(b+1)) b, Nat.gcd_add_mul_left_right]

/-- The residual local period is bounded by a cofactor, even when the shared divisor
was never supplied. The input `killed` is supplied by the norm-one Frobenius law. -/
theorem signedTorus_residual {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (s t : Bool)
    {G : Type*} [Group G] (u : G) (killed : u ^ signedTorusOrder p s = 1) :
    orderOf (u ^ signedTorusOrder (p*q) (s == t)) ∣
      signedTorusOrder p s / (signedTorusOrder p s).gcd (signedTorusOrder q t) := by
  let P := signedTorusOrder p s
  let E := signedTorusOrder (p*q) (s == t)
  let g := P.gcd E
  rw [← signedTorus_gcd hp hq]
  obtain ⟨c, hc⟩ : g ∣ E := Nat.gcd_dvd_right ..
  apply orderOf_dvd_of_pow_eq_one
  change (u ^ E) ^ (P / g) = 1
  have exp : E * (P / g) = P * c := by
    calc
      E * (P / g) = (P / g * g) * c := by rw [hc]; ring
      _ = _ := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_left ..)]
  rw [← pow_mul, exp, pow_mul, killed, one_pow]

/-- The two remaining periods are coprime, so a whole-modulus collision can be refined. -/
theorem signedTorus_coprime {p q : ℕ} (hp : 1 < p) (hq : 1 < q) (s t : Bool)
    {G H : Type*} [Group G] [Group H] (u : G) (v : H)
    (hu : u ^ signedTorusOrder p s = 1) (hv : v ^ signedTorusOrder q t = 1) :
    (orderOf (u ^ signedTorusOrder (p*q) (s == t))).Coprime
      (orderOf (v ^ signedTorusOrder (p*q) (s == t))) := by
  apply Nat.Coprime.of_dvd (signedTorus_residual (by omega) (by omega) s t u hu)
  · simpa [Nat.mul_comm q p, Bool.beq_comm (a := t) (b := s), Nat.gcd_comm (signedTorusOrder q t)] using
      signedTorus_residual (by omega : 0 < q) (by omega : 0 < p) t s v hv
  · apply Nat.coprime_div_gcd_div_gcd
    apply Nat.gcd_pos_of_pos_left
    cases s <;> simp [signedTorusOrder]
    omega

/-- Exact number of local cyclic-group inputs killed by the public exponent.
The probability calculation for independent, uniform CRT components follows by multiplication. -/
theorem signedTorus_killed_count {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (s t : Bool)
    (G : Type*) [Group G] [IsCyclic G] [Fintype G] [DecidableEq G]
    (size : Fintype.card G = signedTorusOrder p s) :
    (Finset.univ.filter (fun u : G => u ^ signedTorusOrder (p*q) (s == t) = 1)).card =
      (signedTorusOrder p s).gcd (signedTorusOrder q t) := by
  let E := signedTorusOrder (p*q) (s == t)
  let g := (Fintype.card G).gcd E
  have same : Finset.univ.filter (fun u : G => u ^ E = 1) = Finset.univ.filter (fun u : G => u ^ g = 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ← orderOf_dvd_iff_pow_eq_one]
    exact ⟨fun h => Nat.dvd_gcd orderOf_dvd_card h, fun h => h.trans (Nat.gcd_dvd_right ..)⟩
  change (Finset.univ.filter (fun u : G => u ^ E = 1)).card = _
  rw [same, ← sum_card_orderOf_eq_card_pow_eq_one (Nat.gcd_pos_of_pos_left E Fintype.card_pos).ne']
  calc
    _ = ∑ i ∈ g.divisors, i.totient := Finset.sum_congr rfl fun i hi =>
      IsCyclic.card_orderOf_eq_totient ((Nat.dvd_of_mem_divisors hi).trans (Nat.gcd_dvd_left ..))
    _ = g := Nat.sum_totient _
    _ = _ := by simp only [g, E, size, signedTorus_gcd hp hq]

private theorem nonkernel_card {S : Type*} [Fintype S] (f : S → Prop) [DecidablePred f]
    {g : ℕ} (h : (Finset.univ.filter f).card = g) :
    (Finset.univ.filter fun x => ¬ f x).card = Fintype.card S - g := by
  have both := Finset.filter_card_add_filter_neg_card_eq_card (s := Finset.univ) f
  rw [Finset.card_univ, h] at both
  omega

/-- Count seeds for which precisely one local component is killed. A scalar norm gcd
then gives a factor immediately. The two local kernel sizes are supplied by `signedTorus_killed_count`. -/
theorem signedTorus_single_component {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    [DecidableEq G] [DecidableEq H] (E g : ℕ)
    (hkG : (Finset.univ.filter (fun x : G => x^E = 1)).card = g)
    (hkH : (Finset.univ.filter (fun x : H => x^E = 1)).card = g) :
    ((Finset.univ ×ˢ Finset.univ).filter (fun x : G × H => (x.1^E = 1) = (x.2^E ≠ 1))).card =
      g * (Fintype.card H - g) + (Fintype.card G - g) * g := by
  classical
  rw [Finset.filter_product_card Finset.univ Finset.univ (fun x : G => x^E = 1) (fun y : H => y^E ≠ 1)]
  simp only [not_not, hkG, hkH, nonkernel_card (fun x : G => x^E = 1) hkG, nonkernel_card (fun x : H => x^E = 1) hkH]

/-- Distinct positive local sizes leave at least half of the product group outside the
kernel. This is the deterministic arithmetic behind the conditional success probability. -/
theorem signedTorus_half_survive {P Q : ℕ} (hP : 0 < P) (hQ : 0 < Q) (hne : P ≠ Q) :
    2 * P.gcd Q ^ 2 ≤ P * Q := by
  let g := P.gcd Q
  obtain ⟨a, ha⟩ : g ∣ P := Nat.gcd_dvd_left ..
  obtain ⟨b, hb⟩ : g ∣ Q := Nat.gcd_dvd_right ..
  have a0 : 0 < a := by by_contra! h; simp [show a = 0 by omega] at ha; omega
  have b0 : 0 < b := by by_contra! h; simp [show b = 0 by omega] at hb; omega
  have ab : 2 ≤ a * b := by
    by_cases h : a = 1
    · have h' : b ≠ 1 := by rintro rfl; simp [h] at ha hb; exact hne (ha.trans hb.symm)
      simp [h]; omega
    · exact (show 2 ≤ a by omega).trans (Nat.le_mul_of_pos_right _ b0)
  change 2 * g^2 ≤ P*Q
  calc
    _ ≤ (a*b) * g^2 := Nat.mul_le_mul_right _ ab
    _ = _ := by rw [ha, hb]; ring

/-- A large shared divisor of the successors can coexist only with a bounded shared
divisor of the predecessors, since their least common multiple divides the prime gap. -/
theorem signedTorus_gcd_product_le_gap {p q : ℕ} (hp : 0 < p) (hlt : p < q) :
    (p-1).gcd (q-1) * (p+1).gcd (q+1) ≤ 2 * (q-p) := by
  let a := (p-1).gcd (q-1)
  let b := (p+1).gcd (q+1)
  have ad : a ∣ q-p := by
    rw [show q-p = (q-1)-(p-1) by omega]
    exact Nat.dvd_sub (Nat.gcd_dvd_right ..) (Nat.gcd_dvd_left ..)
  have bd : b ∣ q-p := by
    rw [show q-p = (q+1)-(p+1) by omega]
    exact Nat.dvd_sub (Nat.gcd_dvd_right ..) (Nat.gcd_dvd_left ..)
  have cd : a.gcd b ∣ 2 := by
    rw [show 2 = (p+1)-(p-1) by omega]
    exact Nat.dvd_sub ((Nat.gcd_dvd_right a b).trans (Nat.gcd_dvd_left ..))
      ((Nat.gcd_dvd_left a b).trans (Nat.gcd_dvd_left ..))
  change a*b ≤ 2*(q-p)
  rw [← Nat.gcd_mul_lcm]
  exact Nat.mul_le_mul (Nat.le_of_dvd (by decide) cd)
    (Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) (Nat.lcm_dvd ad bd))

/-- A large signed gcd also bounds the two gcds obtained by changing just one sign. -/
theorem signedTorus_adjacent_gcd_product {n r : ℕ} (hn : 0 < n) (hr : 0 < r) :
    n.gcd (r-1) * n.gcd (r+1) ≤ 2*n := by
  let a := n.gcd (r-1)
  let b := n.gcd (r+1)
  have cd : a.gcd b ∣ 2 := by
    rw [show 2 = (r+1)-(r-1) by omega]
    exact Nat.dvd_sub ((Nat.gcd_dvd_right a b).trans (Nat.gcd_dvd_right ..))
      ((Nat.gcd_dvd_left a b).trans (Nat.gcd_dvd_right ..))
  change a*b ≤ 2*n
  rw [← Nat.gcd_mul_lcm]
  exact Nat.mul_le_mul (Nat.le_of_dvd (by decide) cd)
    (Nat.le_of_dvd hn (Nat.lcm_dvd (Nat.gcd_dvd_left ..) (Nat.gcd_dvd_left ..)))

/-- In either quadratic algebra over a field of odd characteristic, the scalar norm
of the difference of two norm-one elements detects exact equality of both coordinates. -/
theorem norm_one_difference_zero_iff {K : Type*} [Field K] {D a b c d : K}
    (hD : D ≠ 0) (h₂ : (2 : K) ≠ 0) (hu : a^2 - D*b^2 = 1) (hv : c^2 - D*d^2 = 1) :
    (a-c)^2 - D*(b-d)^2 = 0 ↔ a = c ∧ b = d := by
  constructor
  · intro hz
    have hprod : 2 * (a*c - D*b*d - 1) = 0 := by linear_combination hu + hv - hz
    have hreal := (mul_eq_zero.mp hprod).resolve_left h₂
    have himag : D * (a*d-b*c)^2 = 0 := by
      linear_combination (a*c-D*b*d+1)*hreal - (c^2-D*d^2)*hu - hv
    have hcross : a*d-b*c = 0 := (pow_eq_zero_iff (by decide)).mp ((mul_eq_zero.mp himag).resolve_left hD)
    constructor
    · linear_combination c*hreal - a*hv - D*d*hcross
    · linear_combination d*hreal - b*hv - c*hcross
  · rintro ⟨rfl, rfl⟩
    simp

/-- Two-coordinate multiplication in the algebra with `w² = D`. -/
def quadraticProduct {R : Type*} [CommRing R] (D : R) (u v : R × R) : R × R :=
  (u.1 * v.1 + D * u.2 * v.2, u.1 * v.2 + u.2 * v.1)

private theorem eval_quadraticProduct {R : Type*} [CommRing R] (D w : R) (root : w^2 = D)
    (u v : R × R) :
    (quadraticProduct D u v).1 + (quadraticProduct D u v).2 * w =
      (u.1 + u.2*w) * (v.1 + v.2*w) := by
  simp only [quadraticProduct, ← root]
  ring

/-- Binary powering of quadratic coordinates, requiring only arithmetic modulo the input. -/
def quadraticPower {R : Type*} [CommRing R] (D : R) (u : R × R) (e : ℕ) : R × R :=
  if hz : e = 0 then (1, 0) else
    let half := quadraticPower D u (e / 2)
    let sq := quadraticProduct D half half
    if e % 2 = 0 then sq else quadraticProduct D sq u
termination_by e
decreasing_by omega

theorem eval_quadraticPower {R : Type*} [CommRing R] (D w : R) (root : w^2 = D)
    (u : R × R) (e : ℕ) :
    (quadraticPower D u e).1 + (quadraticPower D u e).2 * w = (u.1 + u.2*w)^e := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases hz : e = 0
    · simp [hz, quadraticPower]
    · rw [quadraticPower]
      simp only [hz, ↓reduceDIte]
      have step := ih (e / 2) (by omega)
      split_ifs with even
      · rw [eval_quadraticProduct D w root, step, ← pow_add, show e/2+e/2=e by omega]
      · rw [eval_quadraticProduct D w root, eval_quadraticProduct D w root, step, ← pow_add,
          ← pow_succ, show e/2+e/2+1=e by omega]

/-- The base `(3+4i)/5` and the exponent `N−1` give a proper divisor using only N=24257.
The ordinary predecessor gcd is 2, while the successor gcd is 64. -/
theorem signedTorus_24257 :
    let n := 24257
    let u := ((3 * 9703 : ZMod n), (4 * 9703 : ZMod n))
    let v := quadraticPower (-1 : ZMod n) u (n-1)
    5 * 9703 % n = 1 ∧ v.1.val = 23494 ∧ v.2.val = 0 ∧ (v.1 - 1).val.gcd n = 191 ∧
    127 * 191 = n ∧ (127-1).gcd (191-1) = 2 ∧ (127+1).gcd (191+1) = 64 := by
  dsimp only
  have power : quadraticPower (-1 : ZMod 24257) (3 * 9703, 4 * 9703) 24256 = (23494, 0) := by
    simp (config := { decide := true }) only [quadraticPower, Nat.reduceDiv, Nat.reduceMod,
      Nat.reduceEqDiff, ↓reduceDIte, ↓reduceIte]
  rw [show 24257 - 1 = 24256 by decide, power]
  decide +kernel

/-- The signed fixture has prime factors, norm-one input and the advertised public sign. -/
theorem signedTorus_24257_input : Nat.Prime 127 ∧ Nat.Prime 191 ∧
    (3 * 9703 : ZMod 24257)^2 + (4 * 9703 : ZMod 24257)^2 = 1 ∧
    jacobiSym (-1) 24257 = 1 := by
  refine ⟨by norm_num, by norm_num, by decide, ?_⟩
  rw [jacobiSym.at_neg_one (by decide)]
  decide

/-- The ordinary base-two predecessor projection has trivial first gcd on the same input. -/
theorem signedTorus_24257_ordinary :
    (2 : ZMod 24257)^24256 = 9146 ∧ ((9146-1 : ℕ).gcd 24257) = 1 := by
  exact ⟨by reduce_mod_char, by decide⟩

/-- A negative Jacobi symbol alone need not separate the ordinary local 2-primary orders. -/
theorem negativeJacobi_equal_orders :
    jacobiSym (-1) 39 = -1 ∧ orderOf (-1 : ZMod 3) = 2 ∧ orderOf (-1 : ZMod 13) = 2 := by
  refine ⟨?_, orderOf_eq_prime (by norm_num) (by decide), orderOf_eq_prime (by norm_num) (by decide)⟩
  rw [jacobiSym.at_neg_one (by decide)]
  decide

end PrimeFactors
