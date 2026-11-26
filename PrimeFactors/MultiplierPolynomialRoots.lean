import PrimeFactors.PrimitiveNorm
import PrimeFactors.PolynomialRelations
import PrimeFactors.GeometricMatchRank

/-! Local prime-power roots and exact finite sieve work for the reduced MPQS polynomial
with integer coefficients satisfying `A*C = B^2 - k*N`. -/
namespace PrimeFactors.MultiplierPolynomialRoots
open Finset

/-- The polynomial whose signed integer values are tested for smoothness. -/
def value {R : Type*} [CommRing R] (A B C x : R) := A*x^2+2*B*x+C

/-- A unit leading coefficient transports reduced zeros bijectively to ordinary square roots. -/
theorem unit_card {R : Type*} [CommRing R] {A B C D : R}
    (unit : IsUnit A) (coeff : A*C=B^2-D) :
    Nat.card {x : R // value A B C x=0} = Nat.card {y : R // y^2=D} := by
  obtain ⟨u,rfl⟩ := unit
  let e := (Units.mulLeft u).trans (Equiv.addRight B)
  apply Nat.card_congr (e.subtypeEquiv ?_)
  intro x
  change value (u:R) B C x=0 ↔ ((u:R)*x+B)^2=D
  have row := PolynomialRelations.full_row coeff x
  change (u:R)*value (u:R) B C x = _ at row
  conv_rhs => rw [←sub_eq_zero,←row,u.isUnit.mul_right_eq_zero]

private theorem coeff_at {m : ℕ} {A B C D : ℤ} (h : A*C=B^2-D) :
    (A:ZMod m)*C=(B:ZMod m)^2-D := by exact_mod_cast congrArg (fun z : ℤ => (z:ZMod m)) h

/-- For every positive exponent the ordinary sieve prime contributes either two
progressions or none. The multiplier affects only the public square test on `k*N`. -/
theorem ordinary {p : ℕ} [Fact p.Prime] (odd : p≠2) {A : ℕ} {B C k N : ℤ}
    (coeff : (A:ℤ)*C=B^2-k*N) (cop : A.Coprime p) (unit : (k*N : ZMod p)≠0) (e : ℕ) :
    Nat.card {x : ZMod (p^(e+1)) // value (A:ZMod (p^(e+1))) B C x=0} =
      if IsSquare (k*N : ZMod p) then 2 else 0 := by
  classical
  have u := (ZMod.isUnit_iff_coprime A (p^(e+1))).mpr (cop.pow_right _)
  have h := unit_card u (by simpa only [Int.cast_natCast] using coeff_at (m:=p^(e+1)) coeff)
  simpa only [Int.cast_mul] using h.trans (primitiveNorm_odd_root_count odd (k*N) (by simpa using unit) e)

/-- If the prime occurs exactly once in `k*N`, the single initial root has no
lift to the second level. This accounts for ordinary squarefree multiplier primes. -/
theorem ramified {p : ℕ} [Fact p.Prime] {A : ℕ} {B C k N : ℤ}
    (coeff : (A:ℤ)*C=B^2-k*N) (cop : A.Coprime p) (one : (p:ℤ)∣k*N)
    (once : ¬(p:ℤ)^2∣k*N) (e : ℕ) :
    Nat.card {x : ZMod p // value (A:ZMod p) B C x=0} = 1 ∧
      Nat.card {x : ZMod (p^(e+2)) // value (A:ZMod (p^(e+2))) B C x=0} = 0 := by
  have h := primitiveNorm_ramified_roots (k*N) one once e
  exact ⟨(unit_card ((ZMod.isUnit_iff_coprime A p).mpr cop) (by simpa only [Int.cast_natCast] using coeff_at (m:=p) coeff)).trans h.1,
    (unit_card ((ZMod.isUnit_iff_coprime A _).mpr (cop.pow_right (e+2))) (by simpa only [Int.cast_natCast] using coeff_at (m:=p^(e+2)) coeff)).trans h.2⟩

private theorem unit_of_first {p e : ℕ} [Fact p.Prime] {z : ZMod (p^(e+1))}
    (h : firstPrimeDigit p e z≠0) : IsUnit z := by
  obtain ⟨a,rfl⟩ := ZMod.natCast_zmod_surjective z
  rw [map_natCast] at h
  apply (ZMod.isUnit_iff_coprime ..).mpr
  apply Nat.Coprime.pow_right
  exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr fun d => h ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mpr d)).symm

/-- At a coefficient prime with nonzero linear term, the reduced quadratic is a
permutation at every depth. In particular there is one progression for every target. -/
theorem coefficient_prime {p e : ℕ} [Fact p.Prime] {A B C : ℤ}
    (zero : (A:ZMod p)=0) (linear : (2:ZMod p)*B≠0) (target : ZMod (p^(e+1))) :
    Nat.card {x : ZMod (p^(e+1)) // value (A:ZMod (p^(e+1))) B C x=target} = 1 := by
  let Q := value (A:ZMod (p^(e+1))) B C
  have inj : Function.Injective Q := by
    intro x y same
    have u : IsUnit ((A:ZMod (p^(e+1)))*(x+y)+2*B) := by
      apply unit_of_first
      simpa [map_add,map_mul,map_ofNat,map_intCast,zero] using linear
    apply sub_eq_zero.mp
    apply u.mul_left_eq_zero.mp
    change value (A:ZMod (p^(e+1))) B C x=value (A:ZMod (p^(e+1))) B C y at same
    unfold value at same
    linear_combination same
  obtain ⟨x,hx⟩ := Finite.surjective_of_injective inj target
  haveI : Nonempty {a // Q a=target} := ⟨⟨x,hx⟩⟩
  haveI : Subsingleton {a // Q a=target} := ⟨fun a b => Subtype.ext (inj (a.2.trans b.2.symm))⟩
  exact @Nat.card_unique {a // Q a=target} _ _

/-- Cancelling the square part of a square leading coefficient yields a congruence
of squares modulo the input `N`, for arbitrary multipliers, including mixed rows. -/
theorem normalized {N A c : ℕ} {B C k : ℤ} (coeff : (A:ℤ)*C=B^2-k*N)
    (square : A=c^2) (inv : ZMod N) (inverse : inv*c=1) (x : ZMod N) :
    (inv*((A:ZMod N)*x+B))^2 = value (A:ZMod N) B C x := by
  have row := PolynomialRelations.full_row (coeff_at (m:=N) coeff) x
  simp only [Int.cast_natCast,Int.cast_mul,ZMod.natCast_self,mul_zero,sub_zero] at row
  change (A:ZMod N)*value (A:ZMod N) B C x = _ at row
  rw [mul_pow,←row,←mul_assoc,show (inv^2*(A:ZMod N))=1 by rw [square,Nat.cast_pow,←mul_pow,inverse,one_pow],one_mul]

/-- Relations can be pooled across polynomials with independent multipliers
and square leading coefficients. No parity coordinate for `k` is needed. -/
theorem pooled {ι : Type*} (rows : Finset ι) (N : ℕ) (A c : ι → ℕ) (B C k : ι → ℤ)
    (inv x : ι → ZMod N) (z : ℤ)
    (coeff : ∀ i∈rows, (A i:ℤ)*C i=(B i)^2-k i*N)
    (square : ∀ i∈rows, A i=(c i)^2) (unit : ∀ i∈rows, inv i*c i=1)
    (dependency : ∏ i∈rows, value (A i:ZMod N) (B i) (C i) (x i)=(z:ZMod N)^2) :
    (∏ i∈rows, inv i*((A i:ZMod N)*x i+B i))^2=(z:ZMod N)^2 := by
  rw [←Finset.prod_pow]
  exact (Finset.prod_congr rfl fun i hi => normalized (coeff i hi) (square i hi) (inv i) (unit i hi) (x i)).trans dependency

/-- Exact number of marks from a single residue in offsets `0,...,W`. -/
def visits (m W a : ℕ) := if a≤W then 1+(W-a)/m else 0

private theorem visits_one {m : ℕ} [NeZero m] (W : ℕ) (a : ZMod m) :
    ((range (W+1)).filter (fun j : ℕ => (j:ZMod m)=a)).card = visits m W a.val := by
  have pos : 0<m := Nat.pos_of_ne_zero (NeZero.ne m)
  have conv (j : ℕ) : (j:ZMod m)=a ↔ j≡a.val [MOD m] := by
    rw [←ZMod.natCast_eq_natCast_iff,ZMod.natCast_zmod_val]
  simp_rw [conv]
  by_cases inside : a.val≤W
  · rw [GeometricMatchRank.residue_count inside pos, Nat.div_eq_of_lt (ZMod.val_lt a),zero_add,visits,if_pos inside,Nat.add_comm 1]
  · rw [visits,if_neg inside,card_eq_zero,filter_eq_empty_iff]
    intro j hj h
    change j%m=a.val%m at h
    have eq : j%m=a.val := h.trans (Nat.mod_eq_of_lt a.val_lt)
    have := Nat.mod_le j m
    have := mem_range.mp hj
    omega

/-- Sum the lengths of the actual arithmetic progressions. The offset `start`
can be negative. An empty final period or a root outside the finite interval
is accounted for exactly. The modulus can also be a prime power. -/
theorem window_marks {m : ℕ} [NeZero m] (start : ℤ) (W : ℕ) (A B C : ZMod m) :
    ((range (W+1)).filter (fun j : ℕ => value A B C ((start:ZMod m)+j)=0)).card =
      ∑ a∈univ.filter (fun a : ZMod m => value A B C ((start:ZMod m)+a)=0), visits m W a.val := by
  let T := univ.filter (fun a : ZMod m => value A B C ((start:ZMod m)+a)=0)
  have count := sum_card_fiberwise_eq_card_filter (range (W+1)) T (fun j : ℕ => (j:ZMod m))
  simp only [T,mem_filter,mem_univ,true_and] at count
  exact count.symm.trans (sum_congr rfl fun a _ => visits_one W a)

/-- Prescribing `k ≡ N mod m` forces all ordinary odd primes dividing `m` to
split at every depth. One public choice is `k=N%m`; this does not guarantee a
small multiplier independent of the chosen modulus. -/
theorem forced_split {m k N p A : ℕ} [Fact p.Prime] (odd : p≠2)
    (prime_modulus : p∣m) (matchResidue : k ≡ N [MOD m]) (Nunit : (N:ZMod p)≠0)
    (cop : A.Coprime p) {B C : ℤ} (coeff : (A:ℤ)*C=B^2-k*N) (e : ℕ) :
    Nat.card {x : ZMod (p^(e+1)) // value (A:ZMod (p^(e+1))) B C x=0} = 2 := by
  have eq : (k:ZMod p)=N := (ZMod.natCast_eq_natCast_iff ..).mpr (matchResidue.of_dvd prime_modulus)
  have nz : ((k:ℤ)*(N:ℤ):ZMod p)≠0 := by simpa [eq] using mul_ne_zero Nunit Nunit
  rw [ordinary odd coeff cop nz]
  apply if_pos
  simp only [Int.cast_natCast,eq]
  exact ⟨_,rfl⟩

private theorem level_sum (p R : ℚ) (prime : 1<p) (depth : ℕ) :
    (∑ e∈range depth, R/p^(e+1))=R/(p-1)*(1-(1/p)^depth) := by
  have h0 : p≠0 := by linarith
  have h1 : p-1≠0 := by linarith
  induction depth with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ,ih,pow_succ (1/p),pow_succ p,one_div_pow]
    field_simp
    ring

/-- Exact mean truncated valuation on full periods: level `e+1` means one
additional prime division for each root at that depth (polynomial zeros require
separate handling when asking for an untruncated valuation). -/
theorem truncated_mean {p : ℕ} [Fact p.Prime] (odd : p≠2) {A : ℕ} {B C k N : ℤ}
    (coeff : (A:ℤ)*C=B^2-k*N) (cop : A.Coprime p) (unit : (k*N : ZMod p)≠0) (depth : ℕ) :
    (∑ e∈range depth, (Nat.card {x : ZMod (p^(e+1)) // value (A:ZMod (p^(e+1))) B C x=0} : ℚ)/(p:ℚ)^(e+1)) =
      (if IsSquare (k*N:ZMod p) then 2 else 0 : ℚ)/((p:ℚ)-1)*(1-(1/(p:ℚ))^depth) := by
  simp_rw [ordinary odd coeff cop unit]
  rw [Nat.cast_ite]
  simp only [Nat.cast_ofNat,Nat.cast_zero]
  apply level_sum
  exact_mod_cast (Fact.out : p.Prime).one_lt

/-- A prime dividing one of the reduced values in a full nonzero sample can be
tested again at higher powers. This example records the visits at the first three
3-adic levels for both choices of multiplier on the same thirteen sites. -/
noncomputable def smallMarks (m : ℕ) (C : ℤ) : ℕ :=
  ((List.range 13).filter fun j => (value 4 1 C ((j:ℤ)-6))%m=0).length

theorem example_77 : (4:ℤ)*(-19)=1^2-77 ∧ (4:ℤ)*(-96)=1^2-5*77 ∧
    ([3,9,27].map fun m => smallMarks m (-19))=[0,0,0] ∧
    ([3,9,27].map fun m => smallMarks m (-96))=[9,3,1] := by decide +kernel

/-- Two nonsquare negative values at different multipliers split the original
input. The inverse of the common coefficient square root is 39 modulo 77. -/
theorem pooled_77 : value 4 1 (-19 : ℤ) 0 = -19 ∧ value 4 1 (-96 : ℤ) 2 = -76 ∧
    (-19 : ℤ)*(-76)=38^2 ∧ (39:ZMod 77)*2=1 ∧
    (39*(4*0+1)*(39*(4*2+1)) : ZMod 77) = 60 ∧
    (60-38:ℕ).gcd 77 = 11 ∧ 7*11=77 ∧ Nat.Prime 7 ∧ Nat.Prime 11 := by decide +kernel

end PrimeFactors.MultiplierPolynomialRoots
