import PrimeFactors.PascalReadout
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace PrimeFactors

/-- Scaling a residue by the quotient N/M aligns its phase with the q mod M
gridpoint. The identity includes the exact public remainder correction. -/
theorem scaled_factor_grid {p q M : ℕ} (hp : 0 < p) (hM : 0 < M) :
    M * (((p*q/M)*q) % (p*q)) + (p*q % M)*q = (p*q)*(q % M) := by
  let y := p*(q%M)
  have expand : p*q = M*(p*(q/M)) + y := by
    dsimp [y]
    have h := congrArg (fun x => p*x) (Nat.mod_add_div q M)
    dsimp at h
    nlinarith only [h]
  have short : y/M < p := (Nat.div_lt_iff_lt_mul hM).mpr
    (Nat.mul_lt_mul_of_pos_left (Nat.mod_lt q hM) hp)
  have ha : p*q/M = p*(q/M) + y/M := by
    rw [expand, Nat.mul_add_div hM]
  have hr : p*q % M = y%M := by
    rw [expand, Nat.mul_add_mod]
  rw [Nat.mul_mod_mul_right, ha, Nat.mul_add_mod, Nat.mod_eq_of_lt short, hr]
  have eq := congrArg (fun x => x*q) (Nat.mod_add_div y M)
  dsimp [y] at eq ⊢
  nlinarith only [eq]

/-- The public square-root-index Pascal coefficient gives exactly the same
scaled grid identity as the hidden factor, using a single phase. -/
theorem pascal_factor_grid {p q M : ℕ} (hp : p.Prime) (hq : q.Prime) (lt : p<q)
    (po : Odd p) (qo : Odd q) (balance : q<4*p) (hM : 0<M) :
    let n := p*q
    let k := 2*((Nat.sqrt n-1)/2)+1
    let R := ((n/M)*((n-1).choose k+1)) % n
    M*R + (n%M)*q = n*(q%M) := by
  dsimp only
  have h := pascal_sqrt_readout hp hq lt po qo balance
  have c : ((p*q-1).choose (2*((Nat.sqrt (p*q)-1)/2)+1)+1) ≡ q [MOD p*q] := by
    exact ((Nat.mod_modEq _ _).symm.add_right 1).trans (congrArg (· % (p*q)) h)
  exact (c.mul_left (p*q/M)) ▸ scaled_factor_grid hp.pos hM

/-- Odd grid labels have one known bit. Truncating at half the grid resolution
recovers all other bits, including when the public correction is zero. -/
theorem factor_grid_prefix_of_identity {p q H R : ℕ} (hp : 0<p) (hq : 0<q) (qo : Odd q)
    (size : p*q%(2*H)≤p) (grid : 2*H*R+(p*q%(2*H))*q=(p*q)*(q%(2*H))) :
    2*(H*R/(p*q))+1=q%(2*H) := by
  have oddRem : Odd (q%(2*H)) := Nat.odd_iff.mpr <|
    (Nat.mod_mod_of_dvd q (dvd_mul_right 2 H)).trans (Nat.odd_iff.mp qo)
  obtain ⟨j, hj⟩ := oddRem
  rw [hj] at grid ⊢
  rw [Nat.div_eq_of_lt_le (k:=j)]
  · have small := Nat.mul_le_mul_right q size
    nlinarith only [grid, small]
  · have positive := Nat.mul_pos hp hq
    nlinarith only [grid, positive, Nat.zero_le ((p*q%(2*H))*q)]

/-- The first log₂(H) fractional bits when H is dyadic give all unknown bits
of the residue modulo 2H. Oddness supplies its final bit. -/
theorem pascal_factor_grid_prefix {p q H : ℕ} (hp : p.Prime) (hq : q.Prime) (lt : p<q)
    (po : Odd p) (qo : Odd q) (balance : q<4*p) (pos : 0<H) (size : p*q%(2*H)≤p) :
    let n := p*q
    let k := 2*((Nat.sqrt n-1)/2)+1
    let R := ((n/(2*H))*((n-1).choose k+1)) % n
    2*(H*R/n)+1 = q%(2*H) := by
  exact factor_grid_prefix_of_identity hp.pos hq.pos qo size
    (pascal_factor_grid hp hq lt po qo balance (Nat.mul_pos (by decide : 0<2) pos))

/-- An aligned cutoff in the same threshold range also decodes q mod 2H.
The valuation lemma below explains why its raw digits can simultaneously vanish. -/
theorem pascal_prefix_between {p q k H : ℕ} (hp : p.Prime) (hq : q.Prime) (lt : p<q)
    (po : Odd p) (qo : Odd q) (ko : Odd k) (pk : p≤k) (kq : k<q) (short : k<2*p)
    (pos : 0<H) (size : p*q%(2*H)≤p) :
    let n := p*q
    let R := ((n/(2*H))*((n-1).choose k+1)) % n
    2*(H*R/n)+1 = q%(2*H) := by
  have h := pascal_between hp hq lt po qo ko pk kq short
  have eq : ((p*q-1).choose k) % (p*q)+1 = q := by
    rw [h, Nat.sub_add_cancel hq.pos]
  have c := ((Nat.mod_modEq ((p*q-1).choose k) (p*q)).symm.add_right 1).trans
    (congrArg (· % (p*q)) eq)
  apply factor_grid_prefix_of_identity hp.pos hq.pos qo size
  exact (c.mul_left (p*q/(2*H))) ▸ scaled_factor_grid hp.pos (Nat.mul_pos (by decide : 0<2) pos)

/-- For odd gridpoints the spacing is two. A noisy phase within the
remaining one-unit margin stays closer to the correct odd gridpoint. -/
theorem pascal_grid_error {z phase correction index : ℝ}
    (exactGrid : phase + correction = index) (nonneg : 0≤correction)
    (accuracy : |z-phase| < 1-correction) :
    |z-index| < 1 := by
  rw [abs_lt] at accuracy ⊢
  constructor <;> linarith [accuracy.1, accuracy.2]

/-- After subtracting the old digit prefix and scaling by the new radix B,
two candidate block labels admitting circular error less than half a cell
must agree modulo B. The integer turns handle either side of the wrap. -/
theorem pascal_block_lifts_unique {B i j v w : ℤ} {z : ℝ}
    (left : |z-((i+B*v : ℤ) : ℝ)| < 1/2)
    (right : |z-((j+B*w : ℤ) : ℝ)| < 1/2) : i ≡ j [ZMOD B] := by
  rw [abs_lt] at left right
  have h₁ : ((i+B*v : ℤ) : ℝ) < ((j+B*w : ℤ) : ℝ)+1 := by linarith [left.1, right.2]
  have h₂ : ((j+B*w : ℤ) : ℝ) < ((i+B*v : ℤ) : ℝ)+1 := by linarith [right.1, left.2]
  have first : i+B*v < j+B*w+1 := by exact_mod_cast h₁
  have second : j+B*w < i+B*v+1 := by exact_mod_cast h₂
  have eq : i+B*v = j+B*w := by omega
  simpa only [Int.ModEq, Int.add_mul_emod_self_left] using congrArg (· % B) eq

private theorem valuation_choose_factorials {ell n k : ℕ} [Fact ell.Prime] (h : k≤n) :
    padicValNat ell (n.choose k) + padicValNat ell k.factorial +
        padicValNat ell (n-k).factorial = padicValNat ell n.factorial := by
  have e := congrArg (padicValNat ell) (Nat.choose_mul_factorial_mul_factorial h)
  rwa [padicValNat.mul (Nat.mul_ne_zero (Nat.choose_pos h).ne' (Nat.factorial_ne_zero _))
    (Nat.factorial_ne_zero _), padicValNat.mul (Nat.choose_pos h).ne' (Nat.factorial_ne_zero _)] at e

/-- Removing matching base-ell zero digits from a binomial index preserves
the valuation, even when the corresponding upper digit is nonzero. -/
theorem pascal_valuation_drop_digit {ell n k : ℕ} [hp : Fact ell.Prime] (h : ell*k ≤ n) :
    padicValNat ell (n.choose (ell*k)) = padicValNat ell ((n/ell).choose k) := by
  have small : k ≤ n/ell := (Nat.le_div_iff_mul_le hp.out.pos).mpr (by simpa [mul_comm] using h)
  have f (v : ℕ) : padicValNat ell v.factorial =
      padicValNat ell (v/ell).factorial + v/ell :=
    (padicValNat_mul_div_factorial _).symm.trans (padicValNat_factorial_mul _)
  have h₁ := valuation_choose_factorials (ell:=ell) h
  have h₂ := valuation_choose_factorials (ell:=ell) small
  rw [f n, f (n-ell*k), padicValNat_factorial_mul, Nat.sub_mul_div'] at h₁
  omega

/-- The valuation of the power-index entry is read from the upper digits. -/
theorem pascal_valuation_power {ell : ℕ} [hp : Fact ell.Prime] (b n : ℕ) (h : ell^b≤n) :
    padicValNat ell (n.choose (ell^b)) = padicValNat ell (n/ell^b) := by
  induction b generalizing n with
  | zero => simp
  | succ b ih =>
    rw [pow_succ'] at h ⊢
    rw [pascal_valuation_drop_digit h, ih (n/ell) (by
      apply (Nat.le_div_iff_mul_le hp.out.pos).mpr
      simpa [Nat.mul_comm] using h), Nat.div_div_eq_div_mul]

/-- Raw prime-power projection at the fixed Pascal cutoff. For a unit n
all b low base-ell digits vanish, and the exact valuation is public. -/
theorem pascal_raw_valuation {ell n : ℕ} [hp : Fact ell.Prime] (b : ℕ)
    (unit : ¬ell ∣ n) (size : ell^b ≤ n) :
    padicValNat ell ((n-1).choose (ell^b-1)) = b + padicValNat ell (n/ell^b) := by
  have pos : 0 < ell^b := pow_pos hp.out.pos _
  have npos := pos.trans_le size
  have rel := Nat.succ_mul_choose_eq (n-1) (ell^b-1)
  rw [Nat.succ_eq_add_one, Nat.sub_add_cancel npos, Nat.succ_eq_add_one, Nat.sub_add_cancel pos] at rel
  have vals := congrArg (padicValNat ell) rel
  rw [padicValNat.mul npos.ne' (Nat.choose_pos (Nat.sub_le_sub_right size 1)).ne',
    padicValNat.eq_zero_of_not_dvd unit, zero_add,
    padicValNat.mul (Nat.choose_pos size).ne' pos.ne', padicValNat.prime_pow,
    pascal_valuation_power b n size, add_comm] at vals
  exact vals

/-- Direct reduction of the fixed-width coefficient at the index radix
returns zero on every input coprime to that radix. -/
theorem pascal_raw_mod_zero {ell n : ℕ} [Fact ell.Prime] (b : ℕ)
    (unit : ¬ell ∣ n) (size : ell^b ≤ n) :
    (n-1).choose (ell^b-1) % ell^b = 0 := by
  apply Nat.mod_eq_zero_of_dvd
  apply (padicValNat_dvd_iff b _).mpr
  exact Or.inr ((pascal_raw_valuation b unit size) ▸ Nat.le_add_right _ _)

/-- Any aligned cutoff has zero raw projection, even at non-power indices. -/
theorem pascal_aligned_mod_zero {n k M : ℕ} (unit : M.Coprime n)
    (npos : 0<n) (aligned : M ∣ k+1) :
    (n-1).choose k % M = 0 := by
  have e := Nat.succ_mul_choose_eq (n-1) k
  simp only [Nat.succ_eq_add_one, Nat.sub_add_cancel npos] at e
  apply Nat.mod_eq_zero_of_dvd
  apply unit.dvd_of_dvd_mul_left
  rw [e]
  exact dvd_mul_of_dvd_right aligned _

/-- The nearest index congruent to -1 modulo 2H lies within H of every
real in [u,u+1). The integer endpoints suffice even for a nonintegral root. -/
theorem pascal_aligned_nearest {u H : ℕ} (hH : 0<H) (room : 2*H≤u+1+H) :
    let K := 2*H*((u+1+H)/(2*H))-1
    K≤u+H ∧ u+1≤K+H := by
  have h := Nat.mod_add_div (u+1+H) (2*H)
  have r := Nat.mod_lt (u+1+H) (by omega : 0<2*H)
  dsimp only
  omega

/-- If the nearest aligned cutoff misses [p,q), the first Fermat midpoint
splits the input at the quarter-width scale. -/
theorem pascal_aligned_miss_fermat {p q x K H : ℝ} (hp : 0<p) (xp : p≤x)
    (root : x^2=p*q) (balance : q≤2*p) (scale : (2*H)^2≤4*x)
    (near : |K-x|≤H) (miss : K<p ∨ q≤K) : (p+q)/2 < x+1 := by
  have bounds := abs_le.mp near
  have amgm : x-p≤q-x := by
    by_contra! high
    have wrong := mul_lt_mul_of_pos_left high hp
    nlinarith only [wrong, root, sq_nonneg (x-p)]
  have lower : x-p≤H := by rcases miss with h|h <;> linarith [bounds.1, bounds.2]
  have width := mul_self_le_mul_self (sub_nonneg.mpr xp) lower
  have bound := mul_le_mul_of_nonneg_left balance hp.le
  have ratio : x < 2*p := by
    by_contra! high
    nlinarith only [root, bound, mul_self_le_mul_self (by positivity : 0≤2*p) high,
      sq_pos_of_pos hp]
  nlinarith only [width, root, scale, ratio, hp]

example : 2 * (4*((391/8*23) % 391)/391) + 1 = 7 := by decide

example : padicValNat 2 ((143-1).choose (2^4-1)) = 7 := by
  rw [pascal_raw_valuation 4 (by decide) (by decide)]
  change 4 + padicValNat 2 (2^3) = 7
  rw [padicValNat.prime_pow]

end PrimeFactors
