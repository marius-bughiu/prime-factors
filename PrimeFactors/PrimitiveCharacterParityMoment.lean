import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! Even-minus-odd moments in the family of pairs of nonprincipal characters at
two primes. For distinct primes these are the local components of primitive
characters of the product. The finite identities work directly with the pairs.
For the classical orthogonality formula with parity, see Conrey, Iwaniec and
Soundararajan, *The mean square of the product of a Dirichlet L-function and
a Dirichlet polynomial*, Lemma 2. -/

namespace PrimeFactors.PrimitiveCharacterParityMoment

open Finset
open scoped ComplexConjugate

noncomputable def nonprincipal (p : ℕ) : Finset (DirichletCharacter ℂ p) := by
  classical exact univ.erase 1

/-- Sum once over every pair of nonprincipal local characters. -/
noncomputable def family (p q : ℕ) (F : DirichletCharacter ℂ p → DirichletCharacter ℂ q → ℂ) :=
  ∑ χ ∈ nonprincipal p, ∑ ψ ∈ nonprincipal q, F χ ψ

noncomputable def read {p q : ℕ} (χ : DirichletCharacter ℂ p) (ψ : DirichletCharacter ℂ q)
    (n : ℕ) := χ (n : ZMod p)*ψ (n : ZMod q)

noncomputable def parity {p q : ℕ} (χ : DirichletCharacter ℂ p) (ψ : DirichletCharacter ℂ q) :=
  χ (-1 : ZMod p)*ψ (-1 : ZMod q)

theorem parity_cases {p q : ℕ} (χ : DirichletCharacter ℂ p) (ψ : DirichletCharacter ℂ q) :
    parity χ ψ=1 ∨ parity χ ψ= -1 := by
  apply sq_eq_one_iff.mp
  simp only [parity,mul_pow,← map_pow,neg_one_sq,map_one,mul_one]

/-- A signed reading subtracts odd characters from even characters. -/
noncomputable def kernel (p q : ℕ) (signed : Bool) (m n : ℕ) :=
  family p q fun χ ψ => (if signed then parity χ ψ else 1)*read χ ψ m*conj (read χ ψ n)

private noncomputable def localKernel (p : ℕ) (a b : ZMod p) :=
  ∑ χ ∈ nonprincipal p, χ a * conj (χ b)

/-- Ordinary character orthogonality, with the one principal term removed. -/
private theorem local_orthogonality {p : ℕ} [Fact p.Prime] {a b : ZMod p}
    (ha : a≠0) (hb : b≠0) :
    localKernel p a b = (if a=b then ((p-1 : ℕ):ℂ) else 0)-1 := by
  classical
  have conjugate (χ : DirichletCharacter ℂ p) : conj (χ b) = χ b⁻¹ :=
    (MulChar.star_apply' χ b).trans (MulChar.inv_apply' χ b)
  have total := DirichletCharacter.sum_char_inv_mul_char_eq ℂ (isUnit_iff_ne_zero.mpr hb) a
  have removed := sum_erase_add (univ : Finset (DirichletCharacter ℂ p))
    (fun χ => χ a * conj (χ b)) (mem_univ 1)
  simp only [MulChar.one_apply (isUnit_iff_ne_zero.mpr ha),MulChar.one_apply (isUnit_iff_ne_zero.mpr hb),
    map_one,mul_one] at removed
  change localKernel p a b + 1 = _ at removed
  have total' : (∑ χ : DirichletCharacter ℂ p, χ a * conj (χ b)) =
      (if a=b then ((p-1 : ℕ):ℂ) else 0) := calc
    _ = ∑ χ : DirichletCharacter ℂ p, χ b⁻¹ * χ a :=
      sum_congr rfl (fun χ _ => by rw [conjugate,mul_comm])
    _ = _ := by simpa only [Nat.totient_prime (Fact.out : p.Prime),eq_comm (a:=b) (b:=a)] using total
  rw [total'] at removed
  linear_combination removed

private def input (p : ℕ) (signed : Bool) (m : ℕ) : ZMod p := if signed then -(m:ZMod p) else m

private theorem kernel_product (p q : ℕ) (signed : Bool) (m n : ℕ) :
    kernel p q signed m n =
      localKernel p (input p signed m) n * localKernel q (input q signed m) n := by
  unfold kernel family localKernel
  rw [sum_mul]
  apply sum_congr rfl
  intro χ _
  rw [mul_sum]
  apply sum_congr rfl
  intro ψ _
  cases signed <;> simp only [input,Bool.false_eq_true,if_false,if_true,read,parity,map_mul,
    show -(m:ZMod p)=(-1)*(m:ZMod p) by ring,
    show -(m:ZMod q)=(-1)*(m:ZMod q) by ring] <;> ring

private theorem nz {p n : ℕ} (pos : 0<n) (lt : n<p) : (n : ZMod p)≠0 := by
  rw [ne_eq,ZMod.natCast_zmod_eq_zero_iff_dvd]
  exact Nat.not_dvd_of_pos_of_lt pos lt

private theorem add_match {p m n : ℕ} :
    -(m : ZMod p)=(n : ZMod p) ↔ p∣m+n := by
  rw [←ZMod.natCast_zmod_eq_zero_iff_dvd,Nat.cast_add]
  constructor <;> intro h <;> linear_combination -h

/-- The signed kernel at unit inputs. Each prime contributes its nonprincipal
character sum at the modular condition m+n=0. -/
theorem signed_kernel {p q m n : ℕ} [Fact p.Prime] [Fact q.Prime]
    (mp : ¬p∣m) (np : ¬p∣n) (mq : ¬q∣m) (nq : ¬q∣n) :
    kernel p q true m n =
      ((if p∣m+n then ((p-1 : ℕ):ℂ) else 0)-1) *
      ((if q∣m+n then ((q-1 : ℕ):ℂ) else 0)-1) := by
  have nn {r a : ℕ} (h : ¬r∣a) : (a:ZMod r)≠0 := fun e => h ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp e)
  rw [kernel_product]
  simp only [input,if_true,local_orthogonality (neg_ne_zero.mpr (nn mp)) (nn np),
    local_orthogonality (neg_ne_zero.mpr (nn mq)) (nn nq), add_match]

theorem signed_short {p q m n : ℕ} [Fact p.Prime] [Fact q.Prime]
    (mp : 0<m) (np : 0<n) (sp : m+n<p) (sq : m+n<q) :
    kernel p q true m n=1 := by
  have notdvd {r a : ℕ} (h : 0<a) (l : a<r) := Nat.not_dvd_of_pos_of_lt h l
  rw [signed_kernel (notdvd mp (by omega)) (notdvd np (by omega))
    (notdvd mp (by omega)) (notdvd np (by omega)),if_neg (notdvd (by omega) sp),
    if_neg (notdvd (by omega) sq)]
  norm_num

/-- Unsigned short readings retain the number of character pairs on the diagonal. -/
theorem unsigned_short {p q m n : ℕ} [Fact p.Prime] [Fact q.Prime] (mp : 0<m) (np : 0<n)
    (mP : m<p) (nP : n<p) (mQ : m<q) (nQ : n<q) :
    kernel p q false m n = if m=n then (((p-2)*(q-2) : ℕ):ℂ) else 1 := by
  have inj {r : ℕ} (a : m<r) (b : n<r) : (m:ZMod r)=(n:ZMod r) ↔ m=n := by
    rw [ZMod.natCast_eq_natCast_iff',Nat.mod_eq_of_lt a,Nat.mod_eq_of_lt b]
  rw [kernel_product]
  simp only [input,Bool.false_eq_true,if_false,local_orthogonality (nz mp mP) (nz np nP),
    local_orthogonality (nz mp mQ) (nz np nQ),inj mP nP,inj mQ nQ]
  split_ifs with h
  · have pp := (Fact.out : p.Prime).two_le
    have qp := (Fact.out : q.Prime).two_le
    rw [Nat.cast_mul,show p-1=p-2+1 by omega,show q-1=q-2+1 by omega]
    push_cast
    ring
  · norm_num

private theorem family_sum {ι : Type*} [Fintype ι] (p q : ℕ)
    (F : ι → DirichletCharacter ℂ p → DirichletCharacter ℂ q → ℂ) :
    (family p q fun χ ψ => ∑ i, F i χ ψ) = ∑ i, family p q (F i) := by
  unfold family
  simp_rw [sum_comm (s:=nonprincipal q) (t:=univ)]
  rw [sum_comm]

private theorem family_mul (p q : ℕ) (c : ℂ)
    (F : DirichletCharacter ℂ p → DirichletCharacter ℂ q → ℂ) :
    (family p q fun χ ψ => c*F χ ψ) = c*family p q F := by
  simp only [family,mul_sum]

/-- A finite Dirichlet polynomial, allowing repeated positive indices. -/
noncomputable def polynomial {ι : Type*} [Fintype ι] (n : ι → ℕ) (a : ι → ℂ)
    {p q : ℕ} (χ : DirichletCharacter ℂ p) (ψ : DirichletCharacter ℂ q) :=
  ∑ i, a i * read χ ψ (n i)

/-- Expand the quadratic reading from its signed or unsigned kernel entries. -/
theorem quadratic {ι : Type*} [Fintype ι] (p q : ℕ) (signed : Bool) (n : ι → ℕ) (a : ι → ℂ) :
    (family p q fun χ ψ => (if signed then parity χ ψ else 1) * polynomial n a χ ψ *
      conj (polynomial n a χ ψ)) = ∑ i, ∑ j, (a i * conj (a j)) * kernel p q signed (n i) (n j) := by
  have expand (χ : DirichletCharacter ℂ p) (ψ : DirichletCharacter ℂ q) :
      (if signed then parity χ ψ else 1)*polynomial n a χ ψ*conj (polynomial n a χ ψ) =
        ∑ i, ∑ j, (a i*conj (a j))*((if signed then parity χ ψ else 1)*read χ ψ (n i)*conj (read χ ψ (n j))) := by
    simp only [polynomial,map_sum,map_mul,mul_sum,sum_mul]
    conv_lhs => rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  simp_rw [expand,family_sum,family_mul]
  rfl

private theorem read_prod {ι : Type*} [Fintype ι] {p q : ℕ} (χ : DirichletCharacter ℂ p)
    (ψ : DirichletCharacter ℂ q) (n : ι → ℕ) :
    read χ ψ (∏ i, n i) = ∏ i, read χ ψ (n i) := by
  simp only [read,Nat.cast_prod,map_prod,prod_mul_distrib]

private theorem polynomial_power {ι : Type*} [Fintype ι] {p q : ℕ} (χ : DirichletCharacter ℂ p)
    (ψ : DirichletCharacter ℂ q) (n : ι → ℕ) (a : ι → ℂ) (k : ℕ) :
    (polynomial n a χ ψ)^k =
      polynomial (fun f : Fin k → ι => ∏ i, n (f i)) (fun f => ∏ i, a (f i)) χ ψ := by
  simp only [polynomial,Fintype.sum_pow,prod_mul_distrib,read_prod]

/-- For support in [1,B] and 2 B^k below both primes, the signed 2k-th
absolute moment depends only on the sum of the public coefficients. -/
theorem moment_short {ι : Type*} [Fintype ι] {p q B : ℕ} [Fact p.Prime] [Fact q.Prime]
    (n : ι → ℕ) (a : ι → ℂ) (k : ℕ) (pos : ∀ i, 0<n i) (small : ∀ i, n i≤B)
    (pbound : 2*B^k < p) (qbound : 2*B^k < q) :
    (family p q fun χ ψ => parity χ ψ * (polynomial n a χ ψ)^k * conj ((polynomial n a χ ψ)^k)) =
      (∑ i, a i)^k * conj ((∑ i, a i)^k) := by
  classical
  let idx (f : Fin k → ι) := ∏ i, n (f i)
  let coef (f : Fin k → ι) := ∏ i, a (f i)
  have ip (f : Fin k → ι) : 0 < idx f := Finset.prod_pos fun i _ => pos (f i)
  have cap (f : Fin k → ι) : idx f ≤ B^k := calc
    _ ≤ ∏ _i : Fin k, B := prod_le_prod' fun i _ => small (f i)
    _ = _ := by simp
  have entry (f g : Fin k → ι) : kernel p q true (idx f) (idx g)=1 :=
    signed_short (ip f) (ip g) (by have := cap f; have := cap g; omega)
      (by have := cap f; have := cap g; omega)
  have expanded := quadratic p q true idx coef
  simp only [if_true,entry,mul_one,←mul_sum,←sum_mul,←map_sum] at expanded
  have mass : (∑ f, coef f) = (∑ i, a i)^k := (Fintype.sum_pow a k).symm
  rw [mass] at expanded
  simp only [polynomial_power]
  exact expanded

set_option exponentiation.threshold 4096 in
/-- At the 1024-bit lower factor height, even the 96th signed moment is
universal for support through 2^21. -/
theorem full_size {ι : Type*} [Fintype ι] {p q k : ℕ} [Fact p.Prime] [Fact q.Prime]
    (n : ι → ℕ) (a : ι → ℂ) (pos : ∀ i, 0<n i) (small : ∀ i, n i≤2^21)
    (hp : 2^1023 ≤ p) (hq : 2^1023 ≤ q) (order : k≤48) :
    (family p q fun χ ψ => parity χ ψ * (polynomial n a χ ψ)^k * conj ((polynomial n a χ ψ)^k)) =
      (∑ i, a i)^k * conj ((∑ i, a i)^k) := by
  have margin : 2*(2^21 : ℕ)^48 < 2^1023 := by decide +kernel
  have power := Nat.pow_le_pow_right (show 0<(2^21 : ℕ) by decide) order
  have smallPower := (Nat.mul_le_mul_left 2 power).trans_lt margin
  exact moment_short n a k pos small (smallPower.trans_le hp) (smallPower.trans_le hq)

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- At modulus 77, 3+4 reaches the first prime and changes the signed
second moment from the short-range value 4 to −8. -/
theorem sharp77 :
    (family 7 11 fun χ ψ => parity χ ψ*(read χ ψ 3+read χ ψ 4)*conj (read χ ψ 3+read χ ψ 4)) = -8 := by
  have h := quadratic 7 11 true (fun b : Bool => if b then 3 else 4) (fun _ => 1)
  have v34 : kernel 7 11 true 3 4 = -5 := by
    rw [signed_kernel (by decide) (by decide) (by decide) (by decide)]
    norm_num
  have v43 : kernel 7 11 true 4 3 = -5 := by
    rw [signed_kernel (by decide) (by decide) (by decide) (by decide)]
    norm_num
  have v44 : kernel 7 11 true 4 4 = 1 := by
    rw [signed_kernel (by decide) (by decide) (by decide) (by decide)]
    norm_num
  have v33 := signed_short (by decide : 0<3) (by decide : 0<3) (by decide : 3+3<7) (by decide : 3+3<11)
  simp [polynomial,Fintype.sum_bool,v34,v43,v44,v33] at h
  norm_num at h
  simpa only [map_add] using h

end PrimeFactors.PrimitiveCharacterParityMoment
