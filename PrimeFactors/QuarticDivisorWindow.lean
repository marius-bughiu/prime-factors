import PrimeFactors.QuarticFactorLane
import PrimeFactors.UnitQuarticBox
import Mathlib.Data.ZMod.Basic

namespace PrimeFactors.QuarticDivisorWindow

open Finset QuarticFactorLane

/-- Use the ordinary quartic with coefficients in ascending order. -/
noncomputable def weights (v : Fin 5 → ℤ) : Weights :=
  ⟨v 3, v 1, v 4, v 0, v 2⟩

noncomputable def slope (v : Fin 5 → ℤ) (t : ℤ) : ℤ :=
  v 1 + 2*v 2*t + 3*v 3*t^2 + 4*v 4*t^3

noncomputable def height (v : Fin 5 → ℤ) (W : ℕ) : ℤ := ∑ i, |v i| * (W:ℤ)^i.val

noncomputable def jets (v : Fin 5 → ℤ) (n t : ℤ) : Prop :=
  n^2 ∣ value (weights v) 1 t ∧ n ∣ slope v t

theorem eval_bound (v : Fin 5 → ℤ) {x : ℤ} {W : ℕ} (hx : |x| ≤ W) :
    |value (weights v) 1 x| ≤ height v W := by
  have ev : value (weights v) 1 x = ∑ i, v i*x^i.val := by
    rw [Fin.sum_univ_five]
    change _ = v 0*x^0 + v 1*x^1 + v 2*x^2 + v 3*x^3 + v 4*x^4
    simp [value,weights]
  rw [ev]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  apply sum_le_sum
  intro i _
  rw [abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hx _) (abs_nonneg _)

/-- All divisors in the progression impose a double zero modulo their square. -/
theorem square_divides {v : Fin 5 → ℤ} {n t d x : ℤ}
    (hj : jets v n t) (hd : d ∣ n) (offset : d ∣ x-t) :
    d^2 ∣ value (weights v) 1 x := by
  obtain ⟨k,hk⟩ := offset
  have xv : x=t+d*k := by omega
  obtain ⟨u,hu⟩ := (pow_dvd_pow_of_dvd hd 2).trans hj.1
  obtain ⟨r,hr⟩ := hd.trans hj.2
  rw [xv,expansion,hu]
  change _ ∣ d^2*u + (v 1*1 + 2*v 2*t + 3*v 3*t^2 + 4*v 4*t^3)*(d*k) +
    (v 2+3*v 3*t+6*v 4*t^2)*(d*k)^2+(v 3+4*v 4*t)*(d*k)^3+v 4*(d*k)^4
  rw [mul_one,show v 1 + 2*v 2*t + 3*v 3*t^2 + 4*v 4*t^3 = d*r from hr]
  exact ⟨u+r*k+(v 2+3*v 3*t+6*v 4*t^2)*k^2+(v 3+4*v 4*t)*d*k^3+v 4*d^2*k^4,by ring⟩

/-- A checked coefficient vector restricts all sufficiently large divisors in the window. -/
theorem root_of_divisor {v : Fin 5 → ℤ} {n t d x : ℤ} {W : ℕ}
    (hj : jets v n t) (hd : d ∣ n) (offset : d ∣ x-t)
    (nearby : |x|≤W) (small : height v W < d^2) :
    value (weights v) 1 x = 0 :=
  Int.eq_zero_of_abs_lt_dvd (square_divides hj hd offset) ((eval_bound v nearby).trans_lt small)

/-- The two public residues have at most n³ possible values, independently of t. -/
theorem relation_exists {n W D : ℕ} (hn : 0<n) (hW : 0<W) (hD : 0<D)
    (room : n^3 * (5^5 * W^10) < (D^2)^5) (t : ℤ) :
    ∃ v : Fin 5 → ℤ, v≠0 ∧ jets v n t ∧ height v W < (D:ℤ)^2 := by
  letI : NeZero n := ⟨hn.ne'⟩
  let label (p : Fin 5 → ℤ) : ZMod (n^2) × ZMod n :=
    ((value (weights p) 1 t : ℤ), (slope p t : ℤ))
  have prodW : (∏ i : Fin 5, W^i.val) = W^10 := by
    rw [Fin.prod_univ_five]
    change W^0 * W^1 * W^2 * W^3 * W^4 = _
    ring
  have size : Fintype.card (ZMod (n^2) × ZMod n) * (5^5 * ∏ i : Fin 5, W^i.val) < (D^2)^5 := by
    rw [Fintype.card_prod,ZMod.card,ZMod.card,prodW,show n^2*n=n^3 by ring]
    exact room
  obtain ⟨p,q,neq,same,short⟩ := UnitQuarticBox.collision (fun i : Fin 5 => W^i.val)
    (by positivity) (fun i => pow_pos hW _) size label
  let v := p-q
  have e0 := congrArg Prod.fst same
  have e1 := congrArg Prod.snd same
  have ev : value (weights v) 1 t = value (weights p) 1 t - value (weights q) 1 t := by
    simp [v,weights,value]; ring
  have es : slope v t = slope p t - slope q t := by simp [v,slope]; ring
  refine ⟨v,sub_ne_zero.mpr neq,⟨?_,?_⟩,?_⟩
  · rw [ev,←Nat.cast_pow,←ZMod.intCast_zmod_eq_zero_iff_dvd,Int.cast_sub,sub_eq_zero]
    exact e0
  · rw [es,←ZMod.intCast_zmod_eq_zero_iff_dvd,Int.cast_sub,sub_eq_zero]
    exact e1
  · simpa only [v,height,Pi.sub_apply,Nat.cast_pow] using short

/-- For stride s coprime to n compute the anchor t by solving st ≡ -c modulo n.
The same quartic works for every possible divisor d=c+sx in the prescribed block. -/
theorem progression_offset {n c s t x d : ℤ} (unit : IsCoprime s n)
    (anchor : n ∣ c+s*t) (hd : d ∣ n) (position : d = c+s*x) : d ∣ x-t := by
  obtain ⟨q,hq⟩ := hd
  have u : IsCoprime s d := (hq ▸ unit : IsCoprime s (d*q)).of_mul_right_left
  have hd : d ∣ n := ⟨q,hq⟩
  have z : d ∣ s*(x-t) := by
    have sub := dvd_sub (dvd_refl d) (hd.trans anchor)
    rwa [show d-(c+s*t)=s*(x-t) by rw [position]; ring] at sub
  exact u.symm.dvd_of_dvd_mul_left z

/-- A finite certificate that the quartic has no integer root modulo m. -/
noncomputable def misses (v : Fin 5 → ℤ) (m : ℕ) : Bool :=
  (List.range m).all fun r => decide (value (weights v) 1 r % (m:ℤ) ≠ 0)

theorem no_root {v : Fin 5 → ℤ} {m : ℕ} (hm : 0<m) (miss : misses v m=true) (x : ℤ) :
    value (weights v) 1 x ≠ 0 := by
  intro zero
  have mp : 0<(m:ℤ) := by exact_mod_cast hm
  let r := x % (m:ℤ)
  have r0 : 0≤r := Int.emod_nonneg x mp.ne'
  have rlt : r<(m:ℤ) := Int.emod_lt_of_pos x mp
  have bad := List.all_eq_true.mp miss r.toNat (List.mem_range.mpr (by omega))
  rw [decide_eq_true_eq,Int.toNat_of_nonneg r0] at bad
  apply bad
  have eq : x ≡ r [ZMOD (m:ℤ)] := (Int.mod_modEq x (m:ℤ)).symm
  have h := (Int.modEq_iff_dvd.mp eq).trans
    (Polynomial.sub_dvd_eval_sub r x (polynomial (weights v) 1))
  rw [eval_polynomial,eval_polynomial,zero,sub_zero] at h
  exact Int.emod_eq_zero_of_dvd h

/-- For an odd product and odd center, checking just the odd progression
rules out every natural divisor between the reported endpoints. -/
theorem odd_interval_excludes {v : Fin 5 → ℤ} {n c W L U m : ℕ} {t : ℤ}
    (hn : n%2=1) (hc : c%2=1) (anchor : (n:ℤ) ∣ (c:ℤ)+2*t)
    (hj : jets v n t) (small : height v W < (L:ℤ)^2)
    (left : c≤L+2*W) (right : U≤c+2*W) (hm : 0<m) (miss : misses v m=true)
    (d : ℕ) (lo : L≤d) (hi : d≤U) : ¬ d ∣ n := by
  intro hd
  have odd := Nat.odd_iff.mpr hn
  have unit : IsCoprime (2:ℤ) (n:ℤ) := by exact_mod_cast (Nat.coprime_two_left.mpr odd).isCoprime
  obtain ⟨q,hq⟩ := hd
  obtain ⟨k,hk⟩ := (Nat.odd_mul.mp (hq ▸ odd)).1
  have dz : (d:ℤ) ∣ (n:ℤ) := by exact_mod_cast (show d ∣ n from ⟨q,hq⟩)
  let x := ((d:ℤ)-c)/2
  have pos : (d:ℤ)=(c:ℤ)+2*x := by dsimp [x]; omega
  have near : |x|≤(W:ℤ) := abs_le.mpr (by omega)
  have bound := pow_le_pow_left₀ (Int.natCast_nonneg L) (show (L:ℤ)≤d by exact_mod_cast lo) 2
  exact no_root hm miss x (root_of_divisor hj dz (progression_offset unit anchor dz pos)
    near (small.trans_le bound))

set_option maxRecDepth 8192 in
set_option exponentiation.threshold 16384 in
/-- A public nonzero quartic for each block of indices, with at most four possible offsets.
The hypotheses use only the product, progression, radius and lower bound on divisors. -/
theorem every_2048_progression {n : ℕ} (hn : 0<n) (size : n<2^2048)
    (c s t : ℤ) (unit : IsCoprime s (n:ℤ)) (anchor : (n:ℤ) ∣ c+s*t) :
    ∃ v : Fin 5 → ℤ, v≠0 ∧ jets v n t ∧ height v (2^407) < (2:ℤ)^2046 ∧
      (candidates (weights v) 1).card ≤ 4 ∧
      ∀ x d : ℤ, d ∣ (n:ℤ) → d=c+s*x → (2:ℤ)^1023 ≤ d → |x| ≤ (2:ℕ)^407 →
        x ∈ candidates (weights v) 1 := by
  have room : n^3*(5^5*(2^407)^10) < (((2:ℕ)^1023)^2)^5 :=
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left size.le 3)).trans_lt (by decide +kernel)
  obtain ⟨v,nz,hj,small⟩ := relation_exists hn (by decide) (by decide) room t
  have nonzero : (weights v).a≠0 ∨ (weights v).b≠0 ∨ (weights v).c≠0 ∨
      (weights v).d≠0 ∨ (weights v).e≠0 := by
    by_contra! h
    apply nz
    funext i
    fin_cases i <;> simp_all [weights]
  have small' : height v (2^407) < (2:ℤ)^2046 := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat,←pow_mul] using small
  refine ⟨v,nz,hj,small',candidates_card ..,?_⟩
  intro x d hd pos big nearby
  have bound := pow_le_pow_left₀ (show (0:ℤ)≤2^1023 by positivity) big 2
  apply Multiset.mem_toFinset.mpr
  apply (Polynomial.mem_roots (polynomial_nonzero one_ne_zero nonzero)).mpr
  rw [Polynomial.IsRoot,eval_polynomial]
  exact root_of_divisor hj hd (progression_offset unit anchor hd pos) nearby
    (small'.trans_le (by simpa only [←pow_mul] using bound))

/-- An odd center for each block of 2^408 successive odd-divisor indices. -/
def oddCenter (i : Fin (2^614)) : ℕ := 2^1023 + 1 + 2*(i.val*2^408 + 2^407)

set_option maxRecDepth 8192 in
set_option exponentiation.threshold 16384 in
/-- All 1024-bit odd divisors fit in the 2^614 public windows, with signed offsets
in the radius used by every_2048_progression. -/
theorem odd_address {d : ℕ} (parity : Odd d) (lower : 2^1023≤d) (upper : d<2^1024) :
    ∃ i : Fin (2^614), ∃ x : ℤ, (d:ℤ) = oddCenter i+2*x ∧ |x| ≤ (2:ℤ)^407 := by
  obtain ⟨k,hk⟩ := parity
  let j := k-2^1022
  have cap : j < 2^1022 := by
    have a : 2*(2^1022:ℕ)=2^1023 := by decide
    have b : 2*(2^1023:ℕ)=2^1024 := by decide
    dsimp [j]; omega
  have ib : j/2^408 < 2^614 := by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0<2^408)).mpr
    simpa only [show (2:ℕ)^614*2^408=2^1022 by decide] using cap
  let i : Fin (2^614) := ⟨j/2^408,ib⟩
  let r := j%2^408
  have hr : r<2^408 := Nat.mod_lt _ (by decide)
  have step : (2:ℕ)^408=2*2^407 := by decide
  have decomp : r + i.val*2^408=j := by
    simpa only [r,i,Nat.mul_comm] using Nat.mod_add_div j (2^408)
  refine ⟨i,(r:ℤ)-2^407,?_,abs_le.mpr (by omega)⟩
  have split : k=2^1022+j := by
    have a : 2*(2^1022:ℕ)=2^1023 := by decide
    dsimp [j]; omega
  change (d:ℤ)=((2^1023+1+2*(i.val*2^408+2^407):ℕ):ℤ)+2*((r:ℤ)-2^407)
  omega

/-- The signed anchor is public even when the center is larger than the input. -/
def oddAnchor (n c : ℕ) : ℤ := ((n:ℤ)-c)/2

theorem odd_anchor {n : ℕ} (hn : Odd n) (i : Fin (2^614)) :
    (n:ℤ) ∣ (oddCenter i:ℤ)+2*oddAnchor n (oddCenter i) := by
  obtain ⟨k,hk⟩ := hn
  refine ⟨1,?_⟩
  simp only [oddAnchor,oddCenter,Nat.cast_add,Nat.cast_one,Nat.cast_mul,
    Nat.cast_pow,Nat.cast_ofNat,mul_one]
  have ev : (2:ℤ)^1023 = 2*2^1022 := by rw [pow_succ]; ring
  omega

/-- Existence and coverage together for each public center, independent of the factor. -/
theorem odd_schedule {n : ℕ} (hn : 0<n) (size : n<2^2048) (parity : Odd n) :
    ∀ i : Fin (2^614), ∃ v : Fin 5 → ℤ, v≠0 ∧
      (candidates (weights v) 1).card≤4 ∧ ∀ x d : ℤ, d ∣ (n:ℤ) →
        d=oddCenter i+2*x → (2:ℤ)^1023≤d → |x|≤(2:ℕ)^407 →
        x ∈ candidates (weights v) 1 := by
  intro i
  have unit : IsCoprime (2:ℤ) (n:ℤ) := by exact_mod_cast (Nat.coprime_two_left.mpr parity).isCoprime
  obtain ⟨v,nz,_,_,count,all⟩ := every_2048_progression hn size (oddCenter i) 2
    (oddAnchor n (oddCenter i)) unit (odd_anchor parity i)
  exact ⟨v,nz,count,all⟩

end PrimeFactors.QuarticDivisorWindow
