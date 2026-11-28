import PrimeFactors.ThreeSquarePointDensity

/-! The sum of three square residues modulo four can be zero only when
all three are zero. Doubling the radius therefore preserves the total
count of signed points and annihilates the primitive count. -/
namespace PrimeFactors.EvenThreeSquareRadius

open Finset ThreeSquareRadiusCounts
open private PrimeFactors.ThreeSquareRadiusCounts.signs PrimeFactors.ThreeSquareRadiusCounts.slice
  from PrimeFactors.ThreeSquareRadiusCounts
open private PrimeFactors.ThreeSquarePointDensity.magnitudes from PrimeFactors.ThreeSquarePointDensity

theorem even_coordinates {r x y z : ℕ} (eq : x^2+y^2+z^2=(2*r)^2) :
    2∣x ∧ 2∣y ∧ 2∣z := by
  have tab : ∀ x y z : ZMod 4, x^2+y^2+z^2=0 → x.val%2=0 ∧ y.val%2=0 ∧ z.val%2=0 := by
    decide +kernel
  have eq' := congrArg (fun k : ℕ => (k:ZMod 4)) eq
  push_cast at eq'
  rw [mul_pow,show (2:ZMod 4)^2=0 by decide,zero_mul] at eq'
  simpa only [ZMod.val_natCast,Nat.mod_mod_of_dvd _ (by decide : 2∣4),Nat.dvd_iff_mod_eq_zero]
    using tab _ _ _ eq'

/-- The actual signed, ordered triples, with every zero coordinate allowed. -/
abbrev Points (r : ℕ) :=
  {v : ℤ×ℤ×ℤ // v.1^2+v.2.1^2+v.2.2^2=(r:ℤ)^2}

private theorem signed_even {r : ℕ} (x : Points (2*r)) :
    (2:ℤ)∣x.val.1 ∧ (2:ℤ)∣x.val.2.1 ∧ (2:ℤ)∣x.val.2.2 := by
  obtain ⟨h1,h2,h3⟩ := even_coordinates (PrimeFactors.ThreeSquarePointDensity.magnitudes x.property)
  exact ⟨Int.natAbs_dvd_natAbs.mp h1,Int.natAbs_dvd_natAbs.mp h2,Int.natAbs_dvd_natAbs.mp h3⟩

/-- The forward bijection doubles coordinates and the inverse halves them. -/
noncomputable def doubleEquiv (r : ℕ) : Points r ≃ Points (2*r) where
  toFun v := ⟨(2*v.val.1,2*v.val.2.1,2*v.val.2.2),by
    change (2*v.val.1)^2+(2*v.val.2.1)^2+(2*v.val.2.2)^2=((2*r:ℕ):ℤ)^2
    push_cast
    linear_combination 4*v.property⟩
  invFun v := ⟨(v.val.1/2,v.val.2.1/2,v.val.2.2/2),by
    obtain ⟨⟨x,hx⟩,⟨y,hy⟩,⟨z,hz⟩⟩ := signed_even v
    have eq := v.property
    rw [hx,hy,hz] at eq
    change (v.val.1/2)^2+(v.val.2.1/2)^2+(v.val.2.2/2)^2=(r:ℤ)^2
    rw [hx,hy,hz]
    simp only [Int.mul_ediv_cancel_left _ (by decide : (2:ℤ)≠0)]
    push_cast at eq
    linarith only [eq]⟩
  left_inv v := by apply Subtype.ext; simp [Int.mul_ediv_cancel_left]
  right_inv v := by
    obtain ⟨hx,hy,hz⟩ := signed_even v
    apply Subtype.ext
    simp [Int.mul_ediv_cancel' hx,Int.mul_ediv_cancel' hy,Int.mul_ediv_cancel' hz]

private noncomputable abbrev rawRow (r : ℕ) (u : ℕ×ℕ) :=
  PrimeFactors.ThreeSquareRadiusCounts.slice r u.1 u.2 false

private theorem row_of {r x y z : ℕ} (eq : x^2+y^2+z^2=r^2) :
    rawRow r (x,y) = PrimeFactors.ThreeSquareRadiusCounts.signs x *
      PrimeFactors.ThreeSquareRadiusCounts.signs y * PrimeFactors.ThreeSquareRadiusCounts.signs z := by
  have hz : (r^2-x^2-y^2).sqrt=z := by rw [show r^2-x^2-y^2=z^2 by omega,pow_two,Nat.sqrt_eq]
  simp [rawRow,PrimeFactors.ThreeSquareRadiusCounts.slice,hz,eq]

private theorem row_nonzero {r x y : ℕ} (nz : rawRow r (x,y)≠0) :
    ∃ z, x^2+y^2+z^2=r^2 := by
  unfold rawRow PrimeFactors.ThreeSquareRadiusCounts.slice at nz
  dsimp only at nz
  split at nz
  · rename_i yes; exact ⟨_,yes.1⟩
  · exact False.elim (nz rfl)

private theorem row_double {r x y z : ℕ} (eq : x^2+y^2+z^2=r^2) :
    rawRow r (x,y)=rawRow (2*r) (2*x,2*y) := by
  have eq' : (2*x)^2+(2*y)^2+(2*z)^2=(2*r)^2 := by
    simpa only [mul_pow,←mul_add] using congrArg (2^2*·) eq
  rw [row_of eq,row_of eq']
  simp [PrimeFactors.ThreeSquareRadiusCounts.signs]

/-- The equality holds for the finite counts used by the representation formula. -/
theorem double_total (r : ℕ) : count (2*r) false=count r false := by
  symm
  simp only [count,←sum_product']
  apply sum_bij_ne_zero (fun u _ _ => (2*u.1,2*u.2))
  · rintro ⟨x,y⟩ mem _
    simp only [mem_product,mem_range] at mem ⊢
    omega
  · rintro ⟨x,y⟩ _ _ ⟨x',y'⟩ _ _ eq
    exact Prod.ext (Nat.mul_left_cancel (by decide : 0<2) (congrArg Prod.fst eq))
      (Nat.mul_left_cancel (by decide : 0<2) (congrArg Prod.snd eq))
  · rintro ⟨x,y⟩ mem nz
    obtain ⟨z,eq⟩ := row_nonzero nz
    obtain ⟨⟨x',rfl⟩,⟨y',rfl⟩,⟨z',rfl⟩⟩ := even_coordinates eq
    have low : x'^2+y'^2+z'^2=r^2 := by nlinarith only [eq]
    have same := row_double low
    simp only [mem_product,mem_range] at mem
    refine ⟨(x',y'),?_,fun h => nz (same.symm.trans h),rfl⟩
    simp only [mem_product,mem_range]
    omega
  · rintro ⟨x,y⟩ _ nz
    obtain ⟨z,eq⟩ := row_nonzero nz
    exact row_double eq

theorem double_primitive (r : ℕ) : count (2*r) true=0 := by
  unfold count
  refine sum_eq_zero fun x _ => sum_eq_zero fun y _ => ?_
  unfold PrimeFactors.ThreeSquareRadiusCounts.slice
  dsimp only
  split
  · rename_i yes
    obtain ⟨hx,hy,hz⟩ := even_coordinates yes.1
    have d := Nat.dvd_gcd (Nat.dvd_gcd hx hy) hz
    rw [yes.2 rfl] at d
    omega
  · rfl

theorem pow_two_total (k r : ℕ) : count (2^k*r) false=count r false := by
  induction k with
  | zero => simp
  | succ k ih => rwa [pow_succ',Nat.mul_assoc,double_total]

/-- The odd-radius classical formula suffices for every positive multiplier,
including all powers of two and all shared odd factors. -/
theorem all_multipliers {m p q : ℕ} (formula : HurwitzFormula)
    (pp : p.Prime) (qp : q.Prime) (sp : p%4=1) (sq : q%4=1) (positive : 0<m) :
    count (m*(p*q)) false=(p*q)*count m false := by
  obtain ⟨k,b,bo,rfl⟩ := Nat.exists_eq_two_pow_mul_odd positive.ne'
  rw [Nat.mul_assoc,pow_two_total,pow_two_total,blind formula pp qp sp sq bo]

/-- The more general coprime scaling identity likewise handles even multipliers
without placing an extra premise on counts at the even radii. -/
theorem coprime_dilation {m N : ℕ} (formula : HurwitzFormula) (positive : 0<m)
    (odd : Odd N) (cop : m.Coprime N) :
    (6:ℤ)*count (m*N) false=(count m false : ℤ)*count N false := by
  obtain ⟨k,b,bo,rfl⟩ := Nat.exists_eq_two_pow_mul_odd positive.ne'
  rw [Nat.mul_assoc,pow_two_total,pow_two_total]
  exact dilation formula bo odd (cop.of_dvd_left (dvd_mul_left ..))

/-- Radius zero has one signed point. This accounts for the positive multiplier
condition in the whole-product scaling statements. -/
theorem at_zero : count 0 false=1 := by decide +kernel

theorem at_thirty : count 30 false=150 ∧ count 30 true=0 := by
  exact ⟨(double_total 15).trans toy_fifteen.1,double_primitive 15⟩

end PrimeFactors.EvenThreeSquareRadius
