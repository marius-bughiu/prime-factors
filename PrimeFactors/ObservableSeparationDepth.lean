import PrimeFactors.FactorPairSeparationDepth

/-! A product and a supplied low sum remainder suffice to decide whether
the two factor endings are already determined, without knowing their gap. -/

namespace PrimeFactors.ObservableSeparationDepth

open FactorPairSeparationDepth (depth Determines)
open private PrimeFactors.FactorPairSeparationDepth.nondiv from PrimeFactors.FactorPairSeparationDepth

/-- The extra two bits come from squaring an even sum known modulo 2^e. -/
theorem discriminant {p q s : ℤ} {e : ℕ} (he : 2≤e) (op : Odd p) (oq : Odd q)
    (h : s ≡ p+q [ZMOD (2:ℤ)^e]) : s^2-4*(p*q) ≡ (q-p)^2 [ZMOD (2:ℤ)^(e+2)] := by
  obtain ⟨a,ha⟩ := op
  obtain ⟨b,hb⟩ := oq
  have div := Int.modEq_iff_dvd.mp h
  obtain ⟨z,hz⟩ := (pow_dvd_pow (2:ℤ) he).trans div
  have evenSum : (2:ℤ)^2 ∣ (p+q)+s := by
    refine ⟨a+b+1-z,?_⟩
    linear_combination -hz + 2*ha + 2*hb
  apply Int.modEq_iff_dvd.mpr
  rw [pow_add,show (q-p)^2-(s^2-4*(p*q)) = (p+q-s)*(p+q+s) by ring]
  exact mul_dvd_mul div evenSum

/-- Canonical observable residue, including zero when the available bits
cannot yet resolve a nonzero discriminant. -/
def reading (N s : ℤ) (e : ℕ) : ℤ := (s^2-4*N) % (2:ℤ)^(e+2)

/-- Number of low zero bits in a reading, capped at the available width. -/
def zeroBits (r : ℤ) (j : ℕ) : ℕ := (r.natAbs.gcd (2^j)).log2

/-- One reduced discriminant and its trailing-zero count. Half the count
is used only for a nonzero residue. -/
def ready (N s : ℤ) (k e : ℕ) : Bool := decide (2*k-1≤e ∨
  (reading N s e≠0 ∧ depth k (zeroBits (reading N s e) (e+2)/2) ≤ e))

private theorem powers {t i : ℕ} {g : ℤ} (o : Odd g) : (2:ℤ)^i ∣ 2^t*g ↔ i≤t := by
  constructor
  · intro h
    by_contra! lt
    exact PrimeFactors.FactorPairSeparationDepth.nondiv o lt h
  · intro le
    exact (pow_dvd_pow (2:ℤ) le).trans (dvd_mul_right _ _)

private theorem remainder_dvd (d : ℤ) {i j : ℕ} (le : i≤j) :
    (2:ℤ)^i ∣ d%2^j ↔ (2:ℤ)^i ∣ d := by
  have same := (Int.mod_modEq d ((2:ℤ)^j)).of_dvd (pow_dvd_pow (2:ℤ) le)
  rw [←Int.modEq_zero_iff_dvd,←Int.modEq_zero_iff_dvd]
  exact ⟨fun h => same.symm.trans h,fun h => same.trans h⟩

private theorem residue_order (d : ℤ) {v j : ℕ} (divs : ∀ i, (2:ℤ)^i ∣ d ↔ i≤v)
    (visible : v<j) : d%2^j≠0 ∧ zeroBits (d%2^j) j=v := by
  have nz : d%2^j ≠ 0 := fun zero => (not_le_of_gt visible) ((divs j).mp (Int.dvd_iff_emod_eq_zero.mpr zero))
  have known (i : ℕ) (le : i≤j) : (2:ℕ)^i ∣ (d%2^j).natAbs ↔ i≤v := by
    rw [←Int.natCast_dvd]
    push_cast
    exact (remainder_dvd d le).trans (divs i)
  obtain ⟨i,le,shape⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Nat.gcd_dvd_right (d%2^j).natAbs (2^j))
  have lower : (2:ℕ)^v ∣ (d%2^j).natAbs.gcd (2^j) :=
    Nat.dvd_gcd ((known v visible.le).mpr le_rfl) (pow_dvd_pow 2 visible.le)
  have upper : i≤v := (known i le).mp (shape ▸ Nat.gcd_dvd_left (d%2^j).natAbs (2^j))
  rw [shape,Nat.pow_dvd_pow_iff_le_right (by decide : 1<(2:ℕ))] at lower
  simp only [zeroBits,shape,Nat.log2_eq_log_two,Nat.log_pow (by decide : 1<(2:ℕ))]
  exact ⟨nz,upper.antisymm lower⟩

private theorem visibility {k e t : ℕ} (before : e<2*k-1) (accepts : depth k t≤e) :
    2*t<e+2 := by
  unfold depth at accepts
  split_ifs at accepts <;> omega

/-- For analysis, a nonzero visible discriminant gives the true gap order.
The test itself uses only N, the supplied residue s and their bit widths. -/
theorem ready_iff_depth {p q s g : ℤ} {k e t : ℕ} (he : 2≤e)
    (op : Odd p) (oq : Odd q) (sum : s ≡ p+q [ZMOD (2:ℤ)^e])
    (gap : q-p=(2:ℤ)^t*g) (odd : Odd g) :
    ready (p*q) s k e = true ↔ depth k t≤e := by
  have normal : (q-p)^2 = (2:ℤ)^(2*t)*g^2 := by rw [gap,mul_pow,←pow_mul,Nat.mul_comm t 2]
  let d := (q-p)^2
  have divs (i : ℕ) : (2:ℤ)^i ∣ d ↔ i≤2*t := by
    dsimp only [d]; rw [normal]; exact powers odd.pow
  have obs : reading (p*q) s e=d%2^(e+2) := discriminant he op oq sum
  simp only [ready,decide_eq_true_eq,obs]
  by_cases full : 2*k-1≤e
  · simp only [full,true_or,true_iff]
    unfold depth
    split_ifs <;> omega
  · by_cases visible : 2*t<e+2
    · obtain ⟨nz,val⟩ := residue_order d divs visible
      simp [full,nz,val]
    · have zero : d%2^(e+2)=0 := Int.dvd_iff_emod_eq_zero.mp ((divs _).mpr (by omega))
      simp only [full,zero,ne_eq,not_true_eq_false,false_and,or_self,false_iff]
      exact fun enough => visible (visibility (by omega) enough)

private theorem gap_form {z : ℤ} (nz : z≠0) :
    ∃ t : ℕ, ∃ g : ℤ, z=(2:ℤ)^t*g ∧ Odd g := by
  obtain ⟨t,u,odd,shape⟩ := Nat.exists_eq_two_pow_mul_odd (fun h => nz (Int.natAbs_eq_zero.mp h))
  have exactAbs : (z.natAbs:ℤ)=(2:ℤ)^t*u := by exact_mod_cast shape
  rw [Int.natCast_natAbs] at exactAbs
  by_cases pos : 0≤z
  · exact ⟨t,u,by simpa only [abs_of_nonneg pos] using exactAbs,by exact_mod_cast odd⟩
  · refine ⟨t,-(u:ℤ),?_,(show Odd (u:ℤ) by exact_mod_cast odd).neg⟩
    rw [abs_of_neg (lt_of_not_ge pos)] at exactAbs
    linear_combination -exactAbs

/-- Whether the supplied precision determines the true pair of endings is
decidable from its public product and supplied sum residue alone. -/
theorem ready_iff {p q s : ℤ} {k e : ℕ} (hk : 3≤k) (he : 2≤e)
    (op : Odd p) (oq : Odd q) (distinct : p≠q) (sum : s ≡ p+q [ZMOD (2:ℤ)^e]) :
    ready (p*q) s k e = true ↔ Determines p q k e := by
  obtain ⟨t,g,gap,odd⟩ := gap_form (sub_ne_zero.mpr distinct.symm)
  exact (ready_iff_depth he op oq sum gap odd).trans (FactorPairSeparationDepth.determines_iff hk gap odd).symm

/-- The gap of 71 and 79 realizes the exceptional k−1 branch. For k=4,
one extra supplied sum bit changes the answer. Each input uses its
canonical four- or five-bit residue in place of the full sum 150. -/
theorem control : ready 5609 6 4 4=false ∧ ready 5609 22 4 5=true := by
  norm_num [ready,reading,zeroBits,depth,Nat.log2_eq_log_two]

end PrimeFactors.ObservableSeparationDepth
