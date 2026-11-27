import PrimeFactors.DeepDigitDensityExample

/-! Compare complete-period factor-sum densities when adding independent local
tests or increasing the precision of the existing tests. -/
namespace PrimeFactors.NewPrimesOrMoreDigits

open PrimePowerDensityRatio (density density_nonneg)
open PrimePowerWheelDensity (density_crt less_than_four)
open private PrimeFactors.PrimePowerDensityRatio.count_at from PrimeFactors.PrimePowerDensityRatio

/-- Every odd prime square with unit product allows strictly less than half
of its sum classes, in either quadratic-character branch. -/
theorem square_density {n p : ℕ} (prime : p.Prime) (odd : p≠2) (unit : ¬p∣n) :
    density n (p^2) < 1/2 := by
  classical
  letI : Fact p.Prime := ⟨prime⟩
  have large : 3≤p := by have := prime.two_le; omega
  have counts : 2*LocalSumMenu.count n (p^2)<p^2 := by
    rw [PrimeFactors.PrimePowerDensityRatio.count_at odd unit 1]
    have l : 2*((p-3)/2)+3 ≤ p := by omega
    have r : 2*((p-1)/2)+1 ≤ p := by omega
    cases decide (IsSquare (n:ZMod p)) <;>
      simp only [primePowerSumCount,collidingDigitCount,primePowerSquareCount,pow_one,Bool.true_eq_false,
        Bool.false_eq_true,if_false,if_true,reduceCtorEq] <;>
      nlinarith only [Nat.mul_le_mul_right p l,Nat.mul_le_mul_right p r,large]
  rw [density]
  apply (div_lt_div_iff₀ (Nat.cast_pos.mpr (pow_pos prime.pos 2)) (by decide : (0:ℚ)<2)).mpr
  rw [one_mul,mul_comm]
  exact_mod_cast counts

/-- At a fresh ordinary prime p at least a, the largest possible density
is bounded above by (a+1)/(2a). -/
theorem ordinary_density {n p a : ℕ} (prime : p.Prime) (odd : p≠2) (unit : ¬p∣n)
    (ap : 0<a) (le : a≤p) : density n p ≤ (a+1:ℚ)/(2*a) := by
  classical
  letI : Fact p.Prime := ⟨prime⟩
  have large : 3≤p := by have := prime.two_le; omega
  have counts : 2*LocalSumMenu.count n p≤p+1 := by
    have formula := PrimeFactors.PrimePowerDensityRatio.count_at odd unit 0
    rw [pow_one] at formula
    rw [formula]
    cases decide (IsSquare (n:ZMod p)) <;> simp [primePowerSumCount,collidingDigitCount] <;> omega
  have rat : 2*(LocalSumMenu.count n p:ℚ) ≤ (p:ℚ)+1 := by exact_mod_cast counts
  have ra : (0:ℚ)<a := by exact_mod_cast ap
  rw [density]
  apply (div_le_div_iff₀ (Nat.cast_pos.mpr prime.pos) (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left rat ra.le,(show (a:ℚ)≤p by exact_mod_cast le)]

private noncomputable abbrev old (S : Finset ℕ) := ∏ p∈S, p^2

private theorem fresh {S : Finset ℕ} {p : ℕ} (prime : p.Prime) (outside : p∉S)
    (all : ∀q∈S,Nat.Prime q) : p.Coprime (old S) := by
  apply Nat.Coprime.prod_right
  intro q hq
  exact ((Nat.coprime_primes prime (all q hq)).mpr (fun eq => outside (eq ▸ hq))).pow_right _

private theorem compare {n m : ℕ} (S : Finset ℕ) (depth : ℕ → ℕ)
    (eligible : ∀ p∈S, p.Prime ∧ p≠2 ∧ ¬p∣n ∧ 2≤depth p)
    (independent : (old S).Coprime m) (small : density n m≤1/4) :
    density n (old S*m) < density n (∏ p∈S,p^(depth p)) := by
  rw [density_crt independent]
  have oldBound := less_than_four n S depth eligible
  change density n (old S) < _ at oldBound
  linarith only [mul_le_mul_of_nonneg_left small (density_nonneg n (old S)),oldBound]

/-- Adding any two distinct fresh odd prime squares gives lower full-period
density than increasing every old odd prime to any precision at least two. -/
theorem two_squares {n p q : ℕ} (S : Finset ℕ) (depth : ℕ → ℕ)
    (eligible : ∀ r∈S, r.Prime ∧ r≠2 ∧ ¬r∣n ∧ 2≤depth r)
    (pp : p.Prime) (qp : q.Prime) (po : p≠2) (qo : q≠2)
    (pu : ¬p∣n) (qu : ¬q∣n) (pn : p∉S) (qn : q∉S) (ne : p≠q) :
    density n ((∏ r∈S,r^2)*(p^2*q^2)) < density n (∏ r∈S,r^(depth r)) := by
  have all := fun r (hr : r∈S) => (eligible r hr).1
  apply compare S depth eligible (((fresh pp pn all).symm.pow_right 2).mul_right ((fresh qp qn all).symm.pow_right 2))
  rw [density_crt ((((Nat.coprime_primes pp qp).mpr ne).pow_left 2).pow_right 2)]
  have h := mul_le_mul (square_density pp po pu).le (square_density qp qo qu).le
    (density_nonneg _ _) (by norm_num : (0:ℚ)≤1/2)
  exact le_trans h (by norm_num)

/-- For distinct fresh ordinary primes in increasing order, the three largest
possible local densities multiply to at most 8/35. -/
theorem three_density {n p q r : ℕ} (pp : p.Prime) (qp : q.Prime) (rp : r.Prime)
    (odd : p≠2) (pq : p<q) (qr : q<r) (pu : ¬p∣n) (qu : ¬q∣n) (ru : ¬r∣n) :
    density n (p*q*r) ≤ 8/35 := by
  have pl : 3≤p := by have := pp.two_le; omega
  have qo : q≠2 := by omega
  have ro : r≠2 := by omega
  have ql : 5≤q := by obtain ⟨k,eq⟩ := qp.odd_of_ne_two qo; omega
  have rl : 7≤r := by obtain ⟨k,eq⟩ := rp.odd_of_ne_two ro; omega
  have pc := (Nat.coprime_primes pp qp).mpr pq.ne
  have rc := (((Nat.coprime_primes rp pp).mpr (pq.trans qr).ne.symm).mul_right
    ((Nat.coprime_primes rp qp).mpr qr.ne.symm)).symm
  rw [density_crt rc,density_crt pc]
  have pair := mul_le_mul (ordinary_density pp odd pu (by decide) pl)
    (ordinary_density qp qo qu (by decide) ql) (density_nonneg _ _) (by norm_num)
  have triple := mul_le_mul pair (ordinary_density rp ro ru (by decide) rl)
    (density_nonneg _ _) (by norm_num)
  exact triple.trans (by norm_num)

/-- Three fresh ordinary prime tests also outperform every increase in the
old precisions, when measured over complete periods. -/
theorem three_ordinary {n p q r : ℕ} (S : Finset ℕ) (depth : ℕ → ℕ)
    (eligible : ∀ v∈S, v.Prime ∧ v≠2 ∧ ¬v∣n ∧ 2≤depth v)
    (pp : p.Prime) (qp : q.Prime) (rp : r.Prime) (odd : p≠2) (pq : p<q) (qr : q<r)
    (pu : ¬p∣n) (qu : ¬q∣n) (ru : ¬r∣n) (pn : p∉S) (qn : q∉S) (rn : r∉S) :
    density n ((∏ v∈S,v^2)*(p*q*r)) < density n (∏ v∈S,v^(depth v)) := by
  have all := fun v (hv : v∈S) => (eligible v hv).1
  apply compare S depth eligible (((fresh pp pn all).symm.mul_right (fresh qp qn all).symm).mul_right (fresh rp rn all).symm)
  exact (three_density pp qp rp odd pq qr pu qu ru).trans (by norm_num)

private theorem control_density {p : ℕ} (hp : p∈DeepDigitDensityExample.seeds) (k : ℕ) :
    density 94579 (p^(k+1)) = (primePowerSumCount p true (k+1):ℚ)/(p^(k+1):ℕ) := by
  rw [density,DeepDigitDensityExample.local_count hp]

private theorem control_first {p : ℕ} (hp : p∈DeepDigitDensityExample.seeds) :
    density 94579 p = (primePowerSumCount p true 1:ℚ)/p := by simpa using control_density hp 0

private theorem member (p : ℕ) (h : p∈([3,5,7,11,13]:List ℕ)) : p∈DeepDigitDensityExample.seeds := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl <;> decide +kernel

/-- The three-prime bound is attained on the same public unit product. -/
theorem three_density_sharp : density 94579 (3*5*7) = 8/35 := by
  simp (disch := decide) only [density_crt]
  rw [control_first (member 3 (by decide)),control_first (member 5 (by decide)),
      control_first (member 7 (by decide))]
  decide +kernel

/-- Two fresh ordinary primes can lose the full-period comparison. The
precisions are increased only at 3, 5 and 13 in this published toy example. -/
theorem two_ordinary_counterexample :
    let baseline := density 94579 ((3^2*5^2)*13^2)
    let deep := density 94579 ((3^8*5^8)*13^8)
    let freshTests := density 94579 (((3^2*5^2)*13^2)*(7*11))
    baseline/deep = 3683684874796875/1135347171606742 ∧
      baseline/freshTests=77/24 ∧ deep<freshTests := by
  dsimp only
  simp (disch := decide) only [density_crt]
  rw [control_density (member 3 (by decide)) 1,control_density (member 5 (by decide)) 1,
      control_density (member 13 (by decide)) 1,control_density (member 3 (by decide)) 7,
      control_density (member 5 (by decide)) 7,control_density (member 13 (by decide)) 7,
      control_first (member 7 (by decide)),control_first (member 11 (by decide))]
  decide +kernel

end PrimeFactors.NewPrimesOrMoreDigits
