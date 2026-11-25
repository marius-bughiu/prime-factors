import PrimeFactors.BinomialDivisorWindow
import PrimeFactors.BinomialDivisorScale

/-! Signed integer-valued binomial polynomials at a prescribed public center. -/

namespace PrimeFactors.CenteredBinomialDivisorWindow

open Polynomial Finset BinomialDivisorWindow HigherDivisorWindow

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

/-- Binomial coefficient for the two signs of the integral upper argument. -/
def signedChoose (x : ℤ) (i : ℕ) : ℤ :=
  if x < 0 then (-1)^i * ((x.natAbs+i-1).choose i : ℕ) else (x.natAbs.choose i : ℕ)

theorem eval_pochhammer (x : ℤ) (i : ℕ) :
    (descPochhammer ℤ i).eval x=(i.factorial:ℤ)*signedChoose x i := by
  by_cases neg : x<0
  · have eq : -x=(x.natAbs:ℤ) := by rw [Int.natCast_natAbs,abs_of_neg neg]
    have h := ascPochhammer_eval_neg_eq_descPochhammer ℤ x i
    rw [eq,ascPochhammer_nat_eq_natCast_ascFactorial,Nat.ascFactorial_eq_factorial_mul_choose',
      Nat.cast_mul] at h
    have sign : (-1:ℤ)^i * (-1)^i=1 := by rw [←mul_pow]; norm_num
    simp only [signedChoose,if_pos neg]
    calc
      _ = ((-1:ℤ)^i*(-1)^i)*(descPochhammer ℤ i).eval x := by rw [sign,one_mul]
      _ = (-1:ℤ)^i*((i.factorial:ℤ)*((x.natAbs+i-1).choose i:ℤ)) := by rw [mul_assoc,←h]
      _ = _ := by ring
  · have eq : x=(x.natAbs:ℤ) := ((Int.natCast_natAbs x).trans (abs_of_nonneg (by omega))).symm
    simp only [signedChoose,if_neg neg]
    conv_lhs => rw [eq,descPochhammer_eval_eq_descFactorial,Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]

theorem abs_signedChoose {x : ℤ} {R H k i : ℕ} (near : |x|≤(R:ℤ))
    (degree : i≤k) (room : R+k≤H) : |signedChoose x i|≤(H.choose i:ℤ) := by
  have h : x.natAbs≤R := by exact_mod_cast ((Int.natCast_natAbs x).trans_le near)
  unfold signedChoose
  split_ifs
  · rw [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,abs_of_nonneg (Int.natCast_nonneg _)]
    exact_mod_cast Nat.choose_le_choose i (show x.natAbs+i-1≤H by omega)
  · rw [abs_of_nonneg (Int.natCast_nonneg _)]
    exact_mod_cast Nat.choose_le_choose i (show x.natAbs≤H by omega)

noncomputable def value {k : ℕ} (v : Fin (k+1) → ℤ) (x : ℤ) := ∑ i, v i*signedChoose x i.val

theorem eval_cleared (k : ℕ) (v : Fin (k+1) → ℤ) (x : ℤ) :
    (cleared k v).eval x = (k.factorial:ℤ)*value v x := by
  simp only [cleared,value,eval_finset_sum,eval_mul,eval_C,eval_pochhammer,mul_sum]
  apply sum_congr rfl
  intro i _
  have scale : (multiplier k i:ℤ)*(i.val.factorial:ℤ)=k.factorial := by
    exact_mod_cast multiplier_exact (by omega : i.val≤k)
  linear_combination v i*signedChoose x i.val*scale

theorem value_bound {k R H : ℕ} {x : ℤ} (v : Fin (k+1) → ℤ) (near : |x|≤(R:ℤ))
    (room : R+k≤H) : |value v x|≤∑ i, |v i| *(H.choose i.val:ℤ) := by
  apply (abs_sum_le_sum_abs ..).trans
  apply sum_le_sum
  intro i _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_signedChoose near (by omega) room) (abs_nonneg _)

theorem vanishes {k m n H D R : ℕ} {v : Fin (k+1) → ℤ} {d t x : ℤ}
    (jets : Jets m n t (cleared k v)) (short : (∑ i, |v i| *(H.choose i.val:ℤ))<(D:ℤ)^m)
    (divides : d∣(n:ℤ)) (offset : d∣x-t) (floor : (D:ℤ)≤d)
    (coprime : IsCoprime d (k.factorial:ℤ)) (near : |x|≤(R:ℤ)) (room : R+k≤H) :
    (cleared k v).eval x=0 := by
  have dvd := HigherDivisorWindow.dvd_eval_of_jets jets divides offset
  rw [eval_cleared] at dvd ⊢
  have hit : d^m∣value v x := coprime.pow_left.dvd_of_dvd_mul_left dvd
  have bound := (value_bound v near room).trans_lt (short.trans_le (pow_le_pow_left₀ (Int.natCast_nonneg _) floor _))
  rw [Int.eq_zero_of_abs_lt_dvd hit bound,mul_zero]

/-- A fixed nonzero polynomial covers both signs at the same public anchor. -/
theorem relation_exists {k m n R H D : ℕ} (hn : 0<n) (span : R+k≤H) (hd : 0<D)
    (room : n^(m+m.choose 2)*((k+1)^(k+1)*∏ i : Fin (k+1), H.choose i.val) < (D^m)^(k+1))
    (t : ℤ) :
    ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤k ∧ ∀ x d : ℤ, d∣(n:ℤ) → d∣x-t →
      (D:ℤ)≤d → IsCoprime d (k.factorial:ℤ) → |x|≤(R:ℤ) → F.eval x=0 := by
  obtain ⟨v,nz,jets,short⟩ := short_row hn (by omega : k≤H) hd room t
  refine ⟨cleared k v,cleared_nonzero nz,
    (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (degree_bound _ _)),?_⟩
  intro x d divides offset floor coprime near
  exact vanishes jets short divides offset floor coprime near span

private theorem at_rank {r m n H R D : ℕ} (hr : 0<r) (hn : 0<n) (span : R+(r-1)≤H) (hd : 0<D)
    (room : n^(m+m.choose 2)*(r^r*BinomialDivisorScale.weights r H)<(D^m)^r) (t : ℤ) :
    ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤r-1 ∧ ∀ x d : ℤ, d∣(n:ℤ) → d∣x-t →
      (D:ℤ)≤d → IsCoprime d ((r-1).factorial:ℤ) → |x|≤(R:ℤ) → F.eval x=0 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  refine relation_exists (k:=k) (m:=m) (R:=R) (H:=H) hn span hd ?_ t
  simpa only [Fin.prod_univ_eq_prod_range,BinomialDivisorScale.weights] using room

open FeasibleDivisorCover

/-- Centered finite and LLL determinant budgets use weights at R+k. -/
theorem centered_rooms {n : ℕ} (big : 2^2047≤n) (b : Bool) :
    let m := multiplicity
    let r := dimension
    let D := divisorFloor n b
    let W := BinomialDivisorScale.weights r (5359*radius b+(r-1))
    n^(m+m.choose 2)*(r^r*W) < (D^m)^r ∧
    r^(2*r)*2^((r-1)*r)*(n^(m+m.choose 2)*W)^4 < (D^m)^(4*r) := by
  apply BinomialDivisorScale.rooms big b
  have hk : dimension-1≤radius b := by cases b <;> decide +kernel
  omega

/-- The radius is 5359 times the old radius, on both sides of any public odd center. -/
theorem at_center {n : ℕ} (big : 2^2047≤n) (parity : Odd n) (b : Bool) (c : ℕ) (odd : Odd c) :
    ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card≤dimension-1 ∧ ∀ (x : ℤ) (d : ℕ),
      d.Prime → dimension-1<d → d∣n → (d:ℤ)=(c:ℤ)+2*x → divisorFloor n b≤d →
      |x|≤((5359*radius b:ℕ):ℤ) → F.eval x=0 := by
  let t := ((n:ℤ)-c)/2
  have anchor : (n:ℤ) ∣ (c:ℤ)+2*t := by
    obtain ⟨a,ha⟩ := odd
    obtain ⟨z,hz⟩ := parity
    refine ⟨1,?_⟩
    dsimp only [t]
    omega
  have fd : 0<lower n := Nat.succ_pos _
  have dp : 0<divisorFloor n b := by cases b; exact fd; exact fd.trans_le (le_max_left ..)
  have target := (centered_rooms big b).1
  have hn : 0<n := (show 0<2^2047 by decide +kernel).trans_le big
  obtain ⟨F,nz,rank,hit⟩ := at_rank (r:=dimension) (m:=multiplicity)
    (R:=5359*radius b) (by decide) hn (le_refl _) dp target t
  refine ⟨F,nz,rank,?_⟩
  intro x d prime high div position floor near
  have unit : IsCoprime (2:ℤ) (n:ℤ) := by exact_mod_cast (Nat.coprime_two_left.mpr parity).isCoprime
  have dv : (d:ℤ)∣(n:ℤ) := by exact_mod_cast div
  exact hit x d dv (QuarticDivisorWindow.progression_offset unit anchor dv position)
    (by exact_mod_cast floor) (prime_denominator prime high) near

end PrimeFactors.CenteredBinomialDivisorWindow
