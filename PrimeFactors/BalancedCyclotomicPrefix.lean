import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Tactic

/-! The coefficients of a binary cyclotomic polynomial through degree 2p−1,
where p is the smaller of the two primes. -/

namespace PrimeFactors.BalancedCyclotomicPrefix

open Polynomial
open scoped Polynomial

/-- Clearing the two geometric-series denominators gives an identity in ℤ[X]. -/
theorem product_identity {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q) :
    cyclotomic (p*q) ℤ*(1-X^p)*(1-X^q)=(1-X)*(1-X^(p*q)) := by
  letI : Fact p.Prime := ⟨hp⟩
  have nd : ¬q∣p := fun dvd => (not_le.mpr ord) (Nat.le_of_dvd hp.pos dvd)
  have geo : cyclotomic p ℤ*(X-1)=X^p-1 := by rw [cyclotomic_prime,geom_sum_mul]
  have ex := congrArg (expand ℤ q) geo
  simp only [map_mul,map_sub,map_one,map_pow,expand_X,cyclotomic_expand_eq_cyclotomic_mul hq nd,
    ←pow_mul,Nat.mul_comm q p] at ex
  calc
    _ = cyclotomic (p*q) ℤ*(X^p-1)*(X^q-1) := by ring
    _ = (cyclotomic (p*q) ℤ*cyclotomic p ℤ*(X^q-1))*(X-1) := by rw [←geo]; ring
    _ = _ := by rw [ex]; ring

private theorem remainder {R : Type*} [CommRing R] {f a b c h : R}
    (eq : f*(1-a)*(1-b)=h*(1-c)) :
    f-h*(1+a+b)=f*(a^2*(1-b)+a*b+b^2*(1-a))-h*(1+a+b)*c := by
  linear_combination (1+a+b)*eq

/-- Every term left over after the constant and two single-factor shifts
starts at degree 2p or higher. -/
theorem truncation {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q) :
    (X : ℤ[X])^(2*p) ∣ cyclotomic (p*q) ℤ-(1-X)*(1+X^p+X^q) := by
  have ap : (X : ℤ[X])^(2*p) ∣ (X^p)^2 := by rw [←pow_mul,Nat.mul_comm p 2]
  have ab : (X : ℤ[X])^(2*p) ∣ X^p*X^q := by
    rw [←pow_add]
    exact pow_dvd_pow _ (by omega)
  have bq : (X : ℤ[X])^(2*p) ∣ (X^q)^2 := by
    rw [←pow_mul]
    exact pow_dvd_pow _ (by omega)
  have pq : (X : ℤ[X])^(2*p) ∣ X^(p*q) := pow_dvd_pow _ (by
    rw [Nat.mul_comm 2 p]
    exact Nat.mul_le_mul_left _ hq.two_le)
  rw [remainder (product_identity hp hq ord)]
  exact dvd_sub
    (dvd_mul_of_dvd_right
      (dvd_add (dvd_add (dvd_mul_of_dvd_left ap _) ab) (dvd_mul_of_dvd_left bq _)) _)
    (dvd_mul_of_dvd_right pq _)

/-- If B≤p<q, the same prefix works for every k<2B. When q<2B
the two prime positions themselves both lie inside the prefix. -/
theorem low_block {p q B k : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q)
    (lower : B≤p) (hk : k<2*B) :
    (cyclotomic (p*q) ℤ).coeff k=((1-X)*(1+X^p+X^q) : ℤ[X]).coeff k := by
  have zero := X_pow_dvd_iff.mp (truncation hp hq ord) k (by omega)
  exact sub_eq_zero.mp (by simpa only [coeff_sub] using zero)

/-- A coefficient can be read as six signed indicator terms, including any
endpoint overlap. -/
theorem coefficient {p q B k : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q)
    (lower : B≤p) (hk : k<2*B) :
    (cyclotomic (p*q) ℤ).coeff k =
      (if k=0 then 1 else 0) - (if k=1 then 1 else 0) +
      (if k=p then 1 else 0) - (if k=p+1 then 1 else 0) +
      (if k=q then 1 else 0) - (if k=q+1 then 1 else 0) := by
  rw [low_block hp hq ord lower hk]
  have expand : ((1-X)*(1+X^p+X^q) : ℤ[X]) =
      X^0-X^1+X^p-X^(p+1)+X^q-X^(q+1) := by rw [pow_succ X p,pow_succ X q]; ring
  rw [expand]
  simp only [coeff_add,coeff_sub,coeff_X_pow]

/-- Beyond the constant and linear terms, a nonzero coefficient in the
prefix must occur at a prime or immediately after one. -/
theorem support {p q B k : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q)
    (lower : B≤p) (start : 2≤k) (hk : k<2*B)
    (nonzero : (cyclotomic (p*q) ℤ).coeff k≠0) : k=p ∨ k=p+1 ∨ k=q ∨ k=q+1 := by
  by_contra! miss
  obtain ⟨np,ns,nq,nt⟩ := miss
  apply nonzero
  simp only [coefficient hp hq ord lower hk,if_neg (show k≠0 by omega),
    if_neg (show k≠1 by omega),if_neg np,if_neg ns,if_neg nq,if_neg nt,sub_zero,add_zero]

private theorem telescopes (g : ℤ[X]) (k : ℕ) :
    ∑ j∈Finset.range (k+1),((1-X)*g).coeff j=g.coeff k := by
  induction k with
  | zero => simp [sub_mul]
  | succ k ih =>
    rw [Finset.sum_range_succ,ih,sub_mul,one_mul,coeff_sub,coeff_X_mul]
    ring

/-- Summing the coefficients through k cancels each neighboring negative term. -/
theorem prefix_sum {p q B k : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q)
    (lower : B≤p) (hk : k<2*B) :
    ∑ j∈Finset.range (k+1),(cyclotomic (p*q) ℤ).coeff j =
      (if k=0 then 1 else 0)+(if k=p then 1 else 0)+(if k=q then 1 else 0) := by
  calc
    _ = ∑ j∈Finset.range (k+1),((1-X)*(1+X^p+X^q) : ℤ[X]).coeff j :=
      Finset.sum_congr rfl fun j hj => low_block hp hq ord lower
        (by have := Finset.mem_range.mp hj; omega)
    _ = _ := by rw [telescopes,coeff_add,coeff_add,coeff_X_pow,coeff_X_pow,coeff_one]

/-- At degree 2p the geometric series contributes its first repeated factor.
The correction is exactly one, including when q is larger than 2p. -/
theorem boundary {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p<q) :
    (cyclotomic (p*q) ℤ).coeff (2*p) =
      ((1-X)*(1+X^p+X^q) : ℤ[X]).coeff (2*p)+1 := by
  let f := cyclotomic (p*q) ℤ
  let low : ℤ[X] := (1-X)*(1+X^p+X^q)
  have correction : f-low-f*X^(2*p) =
      f*(1-X^p)*(X^p*X^q+(X^q)^2)-low*X^(p*q) := by
    have eq := remainder (product_identity hp hq ord)
    dsimp only [f,low]
    rw [show 2*p=p*2 by omega,pow_mul,eq]
    ring
  have mixed : (X : ℤ[X])^(2*p+1)∣X^p*X^q := by
    rw [←pow_add]
    exact pow_dvd_pow _ (by omega)
  have double : (X : ℤ[X])^(2*p+1)∣(X^q)^2 := by
    rw [←pow_mul]
    exact pow_dvd_pow _ (by omega)
  have total : (X : ℤ[X])^(2*p+1)∣X^(p*q) := by
    apply pow_dvd_pow
    have h := Nat.mul_le_mul_left p (show 3≤q by have := hp.two_le; omega)
    have := hp.pos
    omega
  have high : (X : ℤ[X])^(2*p+1) ∣ f-low-f*X^(2*p) := by
    rw [correction]
    exact dvd_sub (dvd_mul_of_dvd_right (dvd_add mixed double) _) (dvd_mul_of_dvd_right total _)
  have zero := X_pow_dvd_iff.mp high (2*p) (Nat.lt_succ_self _)
  have initial : f.coeff 0=1 :=
    cyclotomic_coeff_zero ℤ (by nlinarith only [Nat.mul_le_mul hp.two_le hq.two_le])
  simp only [coeff_sub,coeff_mul_X_pow',le_refl,if_true,Nat.sub_self,initial] at zero
  change f.coeff (2*p)=low.coeff (2*p)+1
  linarith

end PrimeFactors.BalancedCyclotomicPrefix
