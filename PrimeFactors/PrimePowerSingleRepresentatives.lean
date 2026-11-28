import PrimeFactors.AdmissibleSumRealization
import PrimeFactors.PrimitiveNorm

/-! Over an odd prime power of exponent at least two, a repeated local root
can be replaced by two different local roots with the same sum and product.
A single prime representative per unit class is necessary and sufficient
for every admissible unit-product sum to be realizable by distinct primes. -/

open private PrimeFactors.primitiveNorm_unit_of_digit from PrimeFactors.PrimitiveNorm
open private PrimeFactors.AdmissibleSumRealization.sort_pair from PrimeFactors.AdmissibleSumRealization

namespace PrimeFactors.PrimePowerSingleRepresentatives

open AdmissibleSumRealization

def OneRepresentative (m L H : ℕ) : Prop :=
  ∀ a < m, a.Coprime m → ∃ p : ℕ, L ≤ p ∧ p < H ∧ p.Prime ∧ p%m=a

private theorem lift {m L H : ℕ} [NeZero m] (supply : OneRepresentative m L H)
    {x : ZMod m} (unit : IsUnit x) :
    ∃ p : ℕ, L ≤ p ∧ p < H ∧ p.Prime ∧ (p : ZMod m) = x := by
  have cu := (ZMod.isUnit_iff_coprime x.val m).mp (by simpa only [ZMod.natCast_zmod_val] using unit)
  obtain ⟨p,lo,hi,P,h⟩ := supply x.val x.val_lt cu
  exact ⟨p,lo,hi,P,ZMod.val_injective m (by simpa only [ZMod.val_natCast] using h)⟩

variable {p : ℕ} [Fact p.Prime]

/-- A repeated-root factorization has an alternative with distinct roots
because p^(k+1) is nonzero and its square vanishes modulo p^(k+2). -/
theorem distinct_roots (odd : p ≠ 2) (k : ℕ) (r s : ZMod (p^(k+2)))
    (h : AdmissibleSum r s) :
    ∃ x y : ZMod (p^(k+2)), x≠y ∧ x*y=r ∧ x+y=s := by
  obtain ⟨x,y,rfl,rfl⟩ := h
  by_cases eq : x=y
  · subst y
    let d : ZMod (p^(k+2)) := (p^(k+1) : ℕ)
    have prime := (Fact.out : p.Prime)
    have nz : d≠0 := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp.mt
      (Nat.not_dvd_of_pos_of_lt (pow_pos prime.pos _)
        (Nat.pow_lt_pow_right prime.one_lt (by omega : k+1<k+2)))
    have vanish : d^2=0 := by
      dsimp only [d]
      rw [←Nat.cast_pow,←pow_mul]
      exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr (pow_dvd_pow p (by omega))
    have two : IsUnit (2 : ZMod (p^(k+2))) := (ZMod.isUnit_iff_coprime 2 _).mpr
      ((Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two prime).mpr odd.symm)))
    refine ⟨x+d,x-d,?_,?_,by ring⟩
    · intro equal
      apply nz
      exact two.mul_right_eq_zero.mp (by linear_combination equal)
    · linear_combination -vanish
  · exact ⟨x,y,eq,rfl,rfl⟩

/-- A unit square modulo an odd prime power has only the two signed roots. -/
theorem signed_roots (odd : p ≠ 2) (k : ℕ) {x a : ZMod (p^(k+1))} (unit : IsUnit a)
    (same : x^2=a^2) : x=a ∨ x= -a := by
  have product : (x-a)*(x+a)=0 := by linear_combination same
  by_cases equal : firstPrimeDigit p k (x-a)=0
  · have nz := (unit.map (firstPrimeDigit p k)).ne_zero
    have two : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
    have plus : firstPrimeDigit p k (x+a) ≠ 0 := by
      rw [map_sub,sub_eq_zero] at equal
      rw [map_add,equal,←two_mul]
      exact mul_ne_zero two nz
    exact Or.inl (sub_eq_zero.mp ((PrimeFactors.primitiveNorm_unit_of_digit plus).mul_left_eq_zero.mp product))
  · exact Or.inr (eq_neg_of_add_eq_zero_left
      ((PrimeFactors.primitiveNorm_unit_of_digit equal).mul_right_eq_zero.mp product))

/-- One representative per unit class is necessary and sufficient at every
odd prime-power exponent at least two. -/
theorem single_iff (odd : p ≠ 2) (k L H : ℕ) :
    OneRepresentative (p^(k+2)) L H ↔
      ∀ r s : ZMod (p^(k+2)), IsUnit r → (AdmissibleSum r s ↔ Realized L H r s) := by
  constructor
  · intro supply r s unit
    constructor
    · intro pass
      obtain ⟨x,y,ne,rfl,rfl⟩ := distinct_roots odd k r s pass
      obtain ⟨ux,uy⟩ := (Commute.all x y).isUnit_mul_iff.mp unit
      obtain ⟨v,vl,vh,V,vx⟩ := lift supply ux
      obtain ⟨w,wl,wh,W,wy⟩ := lift supply uy
      exact PrimeFactors.AdmissibleSumRealization.sort_pair vl vh wl wh V W vx wy
        (fun eq => ne (vx.symm.trans ((congrArg (fun z : ℕ => (z : ZMod (p^(k+2)))) eq).trans wy)))
    · rintro ⟨v,w,_,_,_,_,_,rfl,rfl⟩
      exact admissibleSum_of_factor_pair _ rfl
  · intro all a small cop
    let x : ZMod (p^(k+2)) := a
    have u : IsUnit x := (ZMod.isUnit_iff_coprime _ _).mpr cop
    have rep := (all (x*(-x)) 0 (u.mul u.neg)).mp ⟨x,-x,rfl,add_neg_cancel _⟩
    obtain ⟨v,w,lo,lt,hi,V,W,prod,sum⟩ := rep
    push_cast at prod sum
    have square : (v : ZMod (p^(k+2)))^2=x^2 := by
      linear_combination (v : ZMod (p^(k+2)))*sum-prod
    rcases signed_roots odd (k+1) u square with same|neg
    · exact ⟨v,lo,lt.trans hi,V,by
        simpa only [x,ZMod.val_natCast,Nat.mod_eq_of_lt small] using congrArg ZMod.val same⟩
    · have same : (w : ZMod (p^(k+2)))=x := by linear_combination sum-neg
      exact ⟨w,lo.trans lt.le,hi,W,by
        simpa only [x,ZMod.val_natCast,Nat.mod_eq_of_lt small] using congrArg ZMod.val same⟩

/-- In the seven-bit interval class 5 modulo 9 contains only 113. All six
unit classes have a representative, which is enough to realize all sums. -/
theorem classroom : OneRepresentative 9 64 128 ∧ ¬TwoRepresentatives 9 64 128 := by
  have one : ∀ a : Fin 9, a.val.Coprime 9 →
      ∃ v : Fin 128, 64 ≤ v.val ∧ v.val.Prime ∧ v.val%9=a.val := by decide +kernel
  have unique : ∀ v : Fin 128, 64 ≤ v.val → v.val.Prime → v.val%9=5 → v.val=113 := by decide +kernel
  constructor
  · intro a small unit
    obtain ⟨v,lo,V,eq⟩ := one ⟨a,small⟩ unit
    exact ⟨v.val,lo,v.isLt,V,eq⟩
  · intro two
    obtain ⟨v,w,lo,lt,hi,V,W,hv,hw⟩ := two 5 (by decide) (by decide)
    have eq := unique ⟨v,lt.trans hi⟩ lo V hv
    have eq' := unique ⟨w,hi⟩ (lo.trans lt.le) W hw
    exact lt.ne (eq.trans eq'.symm)

theorem classroom_realized (r s : ZMod 9) (u : IsUnit r) :
    AdmissibleSum r s ↔ Realized 64 128 r s := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact (single_iff (p:=3) (by decide) 0 64 128).mp classroom.1 r s u

end PrimeFactors.PrimePowerSingleRepresentatives
