import PrimeFactors.QuarticIntervalExtension

namespace PrimeFactors.QuarticLevelExclusion

open QuarticDivisorWindow QuarticFactorLane QuarticIntervalExtension

/-- A quartic and an inclusive interval for its integer quotient by a divisor squared. -/
structure Row where
  coeff : Fin 5 → ℤ
  low : ℤ
  high : ℤ

/-- Coefficients of aF(X) + b(c+sX)². -/
noncomputable def combination (v : Fin 5 → ℤ) (c s a b : ℤ) : Fin 5 → ℤ :=
  ![a*v 0+b*c^2, a*v 1+b*2*c*s, a*v 2+b*s^2, a*v 3, a*v 4]

theorem combination_value (v : Fin 5 → ℤ) (c s a b x : ℤ) :
    eval (combination v c s a b) x = a*value (weights v) 1 x + b*(c+s*x)^2 := by
  simp [eval,combination,weights,value]
  ring

/-- Strict inequalities at the levels just outside the proposed interval suffice. -/
noncomputable def bounded (r : Row) (c s l u : ℤ) : Bool :=
  decide (∀ i, 0 < bernstein (combination r.coeff c s 1 (1-r.low)) l u i) &&
  decide (∀ i, 0 < bernstein (combination r.coeff c s (-1) (r.high+1)) l u i)

theorem level_bounds {r : Row} {c s l u x k : ℤ} (cert : bounded r c s l u = true)
    (lx : l ≤ x) (xu : x ≤ u) (eqn : value (weights r.coeff) 1 x = (c+s*x)^2*k) :
    r.low ≤ k ∧ k ≤ r.high := by
  simp only [bounded,Bool.and_eq_true,decide_eq_true_eq] at cert
  have A := eval_positive cert.1 lx xu
  have B := eval_positive cert.2 lx xu
  rw [combination_value,eqn] at A B
  have sq := sq_nonneg (c+s*x)
  constructor
  · by_contra! h
    have le : k ≤ r.low-1 := by omega
    nlinarith only [A, mul_le_mul_of_nonneg_left le sq]
  · by_contra! h
    have le : r.high+1 ≤ k := by omega
    nlinarith only [B, mul_le_mul_of_nonneg_left le sq]

/-- Test all integer levels in one row against the same offset residue. -/
noncomputable def missesLevels (r : Row) (c s z m : ℤ) : Bool :=
  (List.range (r.high-r.low+1).toNat).all fun j =>
    decide (value (weights r.coeff) 1 z % m ≠ ((c+s*z)^2*(r.low+j)) % m)

/-- A different row may reject each residue. A multiple of m cannot divide
an input which is itself not divisible by m. -/
noncomputable def obstructed (rows : List Row) (c s : ℤ) (m : ℕ) : Bool :=
  (List.range m).all fun z =>
    decide ((c+s*z) % (m:ℤ) = 0) || rows.any (fun r => missesLevels r c s z m)

private theorem value_congr {m x z : ℤ} (v : Fin 5 → ℤ) (eq : x ≡ z [ZMOD m]) :
    value (weights v) 1 x ≡ value (weights v) 1 z [ZMOD m] := by
  apply Int.modEq_iff_dvd.mpr
  have h := eq.dvd.trans (Polynomial.sub_dvd_eval_sub z x (polynomial (weights v) 1))
  simpa only [eval_polynomial] using h

theorem level_obstruction {rows : List Row} {n c s t x l u d : ℤ} {m : ℕ}
    (hm : 0 < m) (live : ¬(m:ℤ) ∣ n) (unit : IsCoprime s n) (anchor : n ∣ c+s*t)
    (valid : ∀ r ∈ rows, jets r.coeff n t ∧ bounded r c s l u = true)
    (miss : obstructed rows c s m = true) (lx : l ≤ x) (xu : x ≤ u)
    (pos : d = c+s*x) : ¬d ∣ n := by
  intro hd
  have off := progression_offset unit anchor hd pos
  have mp : 0 < (m:ℤ) := by exact_mod_cast hm
  let z := x % (m:ℤ)
  have z0 : 0 ≤ z := Int.emod_nonneg x mp.ne'
  have zm : z < (m:ℤ) := Int.emod_lt_of_pos x mp
  have eq : x ≡ z [ZMOD (m:ℤ)] := (Int.mod_modEq ..).symm
  have base := (eq.mul_left s).add_left c
  have bad := List.all_eq_true.mp miss z.toNat (List.mem_range.mpr (by omega))
  simp only [Bool.or_eq_true,decide_eq_true_eq,Int.toNat_of_nonneg z0,List.any_eq_true] at bad
  rcases bad with zero | ⟨r,hr,no⟩
  · apply live
    apply Dvd.dvd.trans _ hd
    rw [pos]
    exact Int.dvd_iff_emod_eq_zero.mpr (base.eq.trans zero)
  · obtain ⟨k,hk⟩ := square_divides (valid r hr).1 hd off
    rw [pos] at hk
    obtain ⟨low,high⟩ := level_bounds (valid r hr).2 lx xu hk
    have j : (k-r.low).toNat < (r.high-r.low+1).toNat := by omega
    have badLevel := List.all_eq_true.mp no _ (List.mem_range.mpr j)
    simp only [decide_eq_true_eq] at badLevel
    apply badLevel
    have level : r.low + ((k-r.low).toNat:ℤ) = k := by omega
    rw [level]
    exact (value_congr r.coeff eq).symm.trans (hk ▸ ((base.pow 2).mul_right k))

/-- The whole integer interval is excluded when the stride is two and the center
and input are odd. The endpoints need not themselves be odd. -/
theorem odd_interval_excludes {rows : List Row} {n c L U m : ℕ} {t l u : ℤ}
    (hn : n%2=1) (hc : c%2=1) (anchor : (n:ℤ) ∣ (c:ℤ)+2*t)
    (hm : 0 < m) (live : n % m ≠ 0)
    (valid : ∀ r ∈ rows, jets r.coeff n t ∧ bounded r c 2 l u = true)
    (miss : obstructed rows c 2 m = true)
    (left : (c:ℤ)+2*l ≤ L) (right : (U:ℤ) ≤ c+2*u)
    (d : ℕ) (lo : L ≤ d) (hi : d ≤ U) : ¬d ∣ n := by
  intro hd
  have odd := Nat.odd_iff.mpr hn
  have unit : IsCoprime (2:ℤ) (n:ℤ) := by exact_mod_cast (Nat.coprime_two_left.mpr odd).isCoprime
  obtain ⟨q,hq⟩ := hd
  obtain ⟨k,hk⟩ := (Nat.odd_mul.mp (hq ▸ odd)).1
  let x := ((d:ℤ)-c)/2
  have pos : (d:ℤ) = (c:ℤ)+2*x := by dsimp [x]; omega
  have modn : ¬(m:ℤ) ∣ (n:ℤ) := by exact_mod_cast (mt Nat.mod_eq_zero_of_dvd live)
  apply level_obstruction hm modn unit anchor valid miss (x:=x) (by omega) (by omega) pos
  exact_mod_cast (show d ∣ n from ⟨q,hq⟩)

end PrimeFactors.QuarticLevelExclusion
