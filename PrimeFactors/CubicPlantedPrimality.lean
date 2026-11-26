import PrimeFactors.PartialOrder
import Mathlib.Tactic

/-! A cube-root-size partial order certificate, specialized to the explicit
cubic family with predecessors 2(s−1)(2s²+1) and 2s(2s²+2s+1).
For the classical N−1 approach using a cube-root-size factored portion, see
Brillhart, Lehmer and Selfridge (1975), Theorem 5, DOI 10.1090/S0025-5718-1975-0384673-1. -/
namespace PrimeFactors.CubicPlantedPrimality

/-- If all prime divisors are 1 modulo F, a proper split must produce a pair
of positive integers with the prescribed sum and product. The height ensures
that no carry can occur in the sum. -/
theorem of_sum_product {n F low high : ℕ} (size : 1<n) (fpos : 0<F)
    (shape : n=1+F*(low+F*high)) (small : low<F) (height : high+1<F)
    (order : ∀ r : ℕ, r.Prime → r∣n → F∣r-1)
    (reject : ∀ a b : ℕ, 0<a → 0<b → a+b=low → a*b=high → False) : n.Prime := by
  apply Nat.prime_def_lt'.mpr
  refine ⟨size,?_⟩
  intro d dlow dlt dn
  obtain ⟨r,prime,rd⟩ := Nat.exists_prime_and_dvd (by omega : d≠1)
  have rn := rd.trans dn
  obtain ⟨a,ha⟩ := order r prime rn
  have rpos := prime.one_lt
  have hR : r=1+F*a := by omega
  have apos : 0<a := by
    cases a <;> simp_all only [mul_zero,add_zero] <;> omega
  obtain ⟨c,hc⟩ := rn
  have rlt : r<n := (Nat.le_of_dvd (by omega) rd).trans_lt dlt
  have cpos : 1<c := by
    cases c with
    | zero => simp only [mul_zero] at hc; omega
    | succ c =>
      cases c with
      | zero => simp only [Nat.succ_eq_add_one,zero_add,mul_one] at hc; omega
      | succ c => omega
  have nmod : 1≡n [MOD F] := (Nat.modEq_iff_dvd' (by omega)).mpr ⟨low+F*high,by omega⟩
  have rmod : 1≡r [MOD F] := (Nat.modEq_iff_dvd' (by omega)).mpr ⟨a,ha⟩
  have cmod := (rmod.mul_right c).symm
  rw [one_mul,←hc] at cmod
  obtain ⟨b,hb⟩ := (Nat.modEq_iff_dvd' (by omega : 1≤c)).mp (nmod.trans cmod)
  have hC : c=1+F*b := by omega
  have bpos : 0<b := by
    cases b <;> simp_all only [mul_zero,add_zero] <;> omega
  have roll : 1+F*(a+b+F*(a*b))=1+F*(low+F*high) := by
    calc
      _ = (1+F*a)*(1+F*b) := by ring
      _ = n := by rw [←hR,←hC,←hc]
      _ = _ := shape
  have eq := Nat.eq_of_mul_eq_mul_left fpos (Nat.add_left_cancel roll)
  have prod : a*b≤high := by
    by_cases good : a*b≤high
    · exact good
    have gap := Nat.mul_le_mul_left F (Nat.lt_of_not_ge good)
    rw [Nat.mul_succ] at gap
    omega
  have sl : a+b≤a*b+1 := by
    obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt apos)
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt bpos)
    nlinarith [Nat.zero_le (i*j)]
  have sums := congrArg (fun v : ℕ => v%F) eq
  simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (by omega : a+b<F),
    Nat.mod_eq_of_lt small] at sums
  have products := Nat.eq_of_mul_eq_mul_left fpos (show F*(a*b)=F*high by omega)
  exact reject a b apos bpos sums products

/-- A single modular order witness supplies the prime-divisor condition. -/
theorem prime_of_order {n F low high : ℕ} (z : ZMod n)
    (size : 1<n) (fpos : 0<F) (shape : n=1+F*(low+F*high)) (small : low<F)
    (height : high+1<F) (reject : ∀ a b : ℕ, 0<a → 0<b → a+b=low → a*b=high → False)
    {ps : List ℕ} (cover : Covers F ps) (full : z^F=1)
    (proper : ∀ l∈ps, Nat.Coprime ((z^(F/l)-1).val) n) : n.Prime := by
  letI : NeZero n := ⟨by omega⟩
  apply of_sum_product size fpos shape small height _ reject
  exact fun _ prime divides => partial_order_dvd_predecessor z fpos cover full proper prime divides

theorem reject_one {a b j : ℕ} (ap : 0<a) (bp : 0<b) (sum : a+b=1) (_ : a*b=j) : False := by
  omega

theorem reject_three {a b j : ℕ} (jbig : 2<j) (ap : 0<a) (bp : 0<b)
    (sum : a+b=3) (prod : a*b=j) : False := by
  have ac : a≤2 := by omega
  have bc : b≤2 := by omega
  interval_cases a <;> interval_cases b <;> omega

end PrimeFactors.CubicPlantedPrimality
