import PrimeFactors.PrimitiveCharacterParityMoment

/-! Exact normalized even and odd averages of short Dirichlet polynomials. -/
namespace PrimeFactors.PrimitiveParityAverages

open Finset PrimitiveCharacterParityMoment
open scoped ComplexConjugate

/-- Number of pairs of nonprincipal characters at two primes. -/
def T (p q : ℕ) := (p-2)*(q-2)

/-- The indicator (1±parity)/2 projects onto the chosen character family. -/
noncomputable def indicator {p q : ℕ} (even : Bool)
    (χ : DirichletCharacter ℂ p) (ψ : DirichletCharacter ℂ q) : ℂ :=
  (if even then 1+parity χ ψ else 1-parity χ ψ)/2

theorem indicator_eq {p q : ℕ} (even : Bool) (χ : DirichletCharacter ℂ p) (ψ : DirichletCharacter ℂ q) :
    indicator even χ ψ = if parity χ ψ=(if even then 1 else -1) then 1 else 0 := by
  rcases parity_cases χ ψ with h | h <;> cases even <;> norm_num [indicator,h]

noncomputable def total (p q : ℕ) (even : Bool) (F : DirichletCharacter ℂ p → DirichletCharacter ℂ q → ℂ) :=
  family p q fun χ ψ => indicator even χ ψ * F χ ψ

noncomputable def average (p q : ℕ) (even : Bool) (F : DirichletCharacter ℂ p → DirichletCharacter ℂ q → ℂ) :=
  total p q even F / total p q even (fun _ _ => 1)

private theorem total_eq (p q : ℕ) (even : Bool) (F : DirichletCharacter ℂ p → DirichletCharacter ℂ q → ℂ) :
    total p q even F = if even then
      (family p q F + family p q (fun χ ψ => parity χ ψ*F χ ψ))/2 else
      (family p q F - family p q (fun χ ψ => parity χ ψ*F χ ψ))/2 := by
  cases even <;>
    simp only [total,family,indicator,Bool.false_eq_true,if_false,if_true,div_mul_eq_mul_div,add_mul,
      sub_mul,one_mul, sum_add_distrib,sum_sub_distrib,←sum_div]

noncomputable def energy {ι : Type*} [Fintype ι] (a : ι → ℂ) := ∑ i, a i * conj (a i)
noncomputable def coherent {ι : Type*} [Fintype ι] (a : ι → ℂ) := (∑ i, a i) * conj (∑ i, a i)

noncomputable def squareValue {ι : Type*} [Fintype ι] (n : ι → ℕ) (a : ι → ℂ)
    {p q : ℕ} (χ : DirichletCharacter ℂ p) (ψ : DirichletCharacter ℂ q) :=
  polynomial n a χ ψ * conj (polynomial n a χ ψ)

private theorem totals {ι : Type*} [Fintype ι] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (n : ι → ℕ) (a : ι → ℂ) (distinct : Function.Injective n) (pos : ∀ i, 0<n i)
    (pbound : ∀ i j, n i+n j<p) (qbound : ∀ i j, n i+n j<q) :
    family p q (squareValue n a) = ((T p q:ℂ)-1)*energy a+coherent a ∧
    (family p q fun χ ψ => parity χ ψ * squareValue n a χ ψ) = coherent a := by
  classical
  have base (i j : ι) : kernel p q false (n i) (n j) = (if i=j then (T p q:ℂ)-1 else 0)+1 := by
    have hp := pbound i j
    have hq := qbound i j
    rw [unsigned_short (pos i) (pos j) (by omega) (by omega) (by omega) (by omega)]
    by_cases same : i=j <;> simp [same,distinct.eq_iff,T]
  have simple (i j : ι) : kernel p q true (n i) (n j)=1 :=
    signed_short (pos i) (pos j) (pbound i j) (qbound i j)
  constructor
  · have h := quadratic p q false n a
    simp only [Bool.false_eq_true,if_false,one_mul,base,mul_add,mul_ite,mul_zero,mul_one,
      sum_add_distrib,sum_ite_eq,mem_univ,if_true,←sum_mul,←mul_sum,←map_sum] at h
    simpa only [squareValue,energy,coherent,mul_comm ((T p q:ℂ)-1)] using h
  · have h := quadratic p q true n a
    simp only [if_true,simple,mul_one,←mul_sum,←sum_mul,←map_sum] at h
    simpa only [squareValue,coherent,mul_assoc] using h

/-- The even and odd family sizes are (T+1)/2 and (T−1)/2 respectively. -/
theorem sizes {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp : 2<p) (hq : 2<q) :
    total p q true (fun _ _ => 1)=((T p q:ℂ)+1)/2 ∧
    total p q false (fun _ _ => 1)=((T p q:ℂ)-1)/2 := by
  have all := unsigned_short (p:=p) (q:=q) (m:=1) (n:=1) (by decide) (by decide)
    (by omega) (by omega) (by omega) (by omega)
  have diff := signed_short (p:=p) (q:=q) (m:=1) (n:=1) (by decide) (by decide) hp hq
  simp only [kernel,PrimitiveCharacterParityMoment.read,Nat.cast_one,map_one,mul_one,Bool.false_eq_true,if_false,if_true] at all diff
  simp only [total_eq,Bool.false_eq_true,if_false,if_true,mul_one,all,diff,T,and_self]

/-- The normalized odd mean is the sum of the squared coefficient magnitudes.
The normalized even mean includes one correction depending on the local family size. -/
theorem polynomial_means {ι : Type*} [Fintype ι] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : 2<p) (hq : 2<q) (nonemptyOdd : 1<T p q) (n : ι → ℕ) (a : ι → ℂ)
    (distinct : Function.Injective n) (pos : ∀ i, 0<n i)
    (pbound : ∀ i j, n i+n j<p) (qbound : ∀ i j, n i+n j<q) :
    average p q true (squareValue n a) = energy a + 2*(coherent a-energy a)/((T p q:ℂ)+1) ∧
    average p q false (squareValue n a) = energy a := by
  obtain ⟨all,diff⟩ := totals n a distinct pos pbound qbound
  obtain ⟨ev,od⟩ := sizes hp hq
  have plus : (T p q:ℂ)+1≠0 := by exact_mod_cast (show T p q+1≠0 by omega)
  have minus : (T p q:ℂ)-1≠0 := sub_ne_zero.mpr (by exact_mod_cast nonemptyOdd.ne')
  constructor
  · rw [average,ev,total_eq,if_pos rfl,all,diff]
    field_simp
    ring
  · rw [average,od,total_eq,if_neg (by decide),all,diff]
    field_simp

/-- Squared magnitude of 1+χ(2), where χ is represented by its two local characters. -/
noncomputable def twoPower {p q : ℕ} (χ : DirichletCharacter ℂ p) (ψ : DirichletCharacter ℂ q) :=
  (1+read χ ψ 2)*conj (1+read χ ψ 2)

private theorem two_nonempty {p q : ℕ} (hp : 8<p) (hq : 8<q) : 1<T p q :=
  (show 1 < 2*2 by decide).trans_le (Nat.mul_le_mul (show 2≤p-2 by omega) (show 2≤q-2 by omega))

private theorem first_moments {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp : 8<p) (hq : 8<q) :
    average p q true twoPower = 2+4/((T p q:ℂ)+1) ∧
    average p q false twoPower = 2 := by
  let n : Fin 2 → ℕ := ![1,2]
  let a : Fin 2 → ℂ := fun _ => 1
  have cap : ∀ i j, n i+n j≤4 := by decide
  have inj : Function.Injective n := by unfold Function.Injective; decide
  have h := polynomial_means (by omega : 2<p) (by omega : 2<q) (two_nonempty hp hq)
    n a inj (by decide) (fun i j => (cap i j).trans_lt (by omega)) (fun i j => (cap i j).trans_lt (by omega))
  have one (χ : DirichletCharacter ℂ p) (ψ : DirichletCharacter ℂ q) : read χ ψ 1=1 := by simp [PrimitiveCharacterParityMoment.read]
  have value : @squareValue _ _ n a p q=twoPower := by
    funext χ ψ
    simp [squareValue,polynomial,Fin.sum_univ_two,n,a,twoPower,one]
  rw [value] at h
  have d : energy a=2 := by norm_num [energy,a,Fin.sum_univ_two]
  have c : coherent a=4 := by norm_num [coherent,a,Fin.sum_univ_two,map_ofNat]
  rw [d,c] at h
  norm_num at h
  exact h

theorem twoPower_even {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp : 8<p) (hq : 8<q) :
    average p q true twoPower=2+4/((T p q:ℂ)+1) := (first_moments hp hq).1

theorem twoPower_odd {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp : 8<p) (hq : 8<q) :
    average p q false twoPower=2 := (first_moments hp hq).2

private theorem second_moments {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp : 8<p) (hq : 8<q) :
    (average p q true (fun χ ψ => (twoPower χ ψ)^2)) = 6+20/((T p q:ℂ)+1) ∧
    (average p q false (fun χ ψ => (twoPower χ ψ)^2)) = 6 := by
  let n : Fin 3 → ℕ := ![1,2,4]
  let a : Fin 3 → ℂ := ![1,2,1]
  have cap : ∀ i j, n i+n j≤8 := by decide
  have inj : Function.Injective n := by unfold Function.Injective; decide
  have h := polynomial_means (by omega : 2<p) (by omega : 2<q) (two_nonempty hp hq)
    n a inj (by decide) (fun i j => (cap i j).trans_lt hp) (fun i j => (cap i j).trans_lt hq)
  have one (χ : DirichletCharacter ℂ p) (ψ : DirichletCharacter ℂ q) : read χ ψ 1=1 := by simp [PrimitiveCharacterParityMoment.read]
  have four (χ : DirichletCharacter ℂ p) (ψ : DirichletCharacter ℂ q) : read χ ψ 4=(read χ ψ 2)^2 := by
    simp only [PrimitiveCharacterParityMoment.read,show (4:ℕ)=2^2 by decide,Nat.cast_pow,map_pow,mul_pow]
  have value : @squareValue _ _ n a p q=(fun χ ψ => (twoPower χ ψ)^2) := by
    funext χ ψ
    have poly : polynomial n a χ ψ = (1+read χ ψ 2)^2 := by
      simp [polynomial,Fin.sum_univ_three,n,a,one,four]
      ring
    simp only [squareValue,poly,twoPower,mul_pow,map_pow]
  rw [value] at h
  have d : energy a=6 := by
    rw [energy,Fin.sum_univ_three]
    change (1:ℂ)*conj 1+2*conj 2+1*conj 1=6
    norm_num [map_ofNat]
  have c : coherent a=16 := by
    rw [coherent,Fin.sum_univ_three]
    change (1+2+1:ℂ)*conj (1+2+1)=16
    norm_num [map_ofNat,map_add]
  rw [d,c] at h
  norm_num at h
  exact h

theorem twoPower_even_sq {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp : 8<p) (hq : 8<q) :
    (average p q true (fun χ ψ => (twoPower χ ψ)^2)) = 6+20/((T p q:ℂ)+1) := (second_moments hp hq).1

theorem twoPower_odd_sq {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp : 8<p) (hq : 8<q) :
    (average p q false (fun χ ψ => (twoPower χ ψ)^2)) = 6 := (second_moments hp hq).2

end PrimeFactors.PrimitiveParityAverages
