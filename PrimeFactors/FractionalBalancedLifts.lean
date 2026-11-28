import PrimeFactors.FractionalCorrectionBudget

/-! Least representatives in the ordinary-correction menu can be filtered
using both their ratio and the public factor-sum interval. These statements
count the surviving pairs and give no search-time bound. -/

namespace PrimeFactors.FractionalBalancedLifts

open Finset FractionalCorrectionBudget

/-- Public balanced-sum interval, with the strict upper endpoint from y<2x. -/
def InWindow (n s : ℕ) : Prop := 4*n ≤ s^2 ∧ 2*s^2 < 9*n

noncomputable instance (n s : ℕ) : Decidable (InWindow n s) :=
  inferInstanceAs (Decidable (4*n ≤ s^2 ∧ 2*s^2 < 9*n))

theorem true_window {x y : ℕ} (order : x≤y) (bal : y<2*x) : InWindow (x*y) (x+y) := by
  have O : (x:ℤ)≤y := by exact_mod_cast order
  have B : (y:ℤ)<2*x := by exact_mod_cast bal
  have P := mul_pos (sub_pos.mpr B) (by omega : 0<2*(y:ℤ)-x)
  constructor
  · exact_mod_cast (by nlinarith only [sq_nonneg ((x:ℤ)-y)] : 4*((x:ℤ)*y)≤((x:ℤ)+y)^2)
  · exact_mod_cast (by nlinarith only [P] : 2*((x:ℤ)+y)^2<9*((x:ℤ)*y))

/-- The simultaneous pair and sum windows bound both ratios of the two
products, even for candidate integers with no primality information. -/
theorem product_bounds {n x y : ℕ} (order : x≤y) (bal : y<2*x) (window : InWindow n (x+y)) :
    8*n<9*(x*y) ∧ 8*(x*y)<9*n := by
  obtain ⟨lo,hi⟩ := true_window order bal
  obtain ⟨nl,nh⟩ := window
  omega

/-- Once the congruence modulus reaches one eighth of N, the two products
are closer than one period in either direction, so they coincide. -/
theorem exact_lift {n m x y : ℕ} (order : x≤y) (bal : y<2*x) (window : InWindow n (x+y))
    (large : n≤8*m) (same : x*y ≡ n [MOD m]) : x*y=n := by
  obtain ⟨lo,hi⟩ := product_bounds order bal window
  exact le_antisymm (same.le_of_lt_add (by omega)) (same.symm.le_of_lt_add (by omega))

/-- Ordered, nontrivial least residue pairs passing both balanced windows. -/
noncomputable def pairs (n m : ℕ) : Finset (ℕ×ℕ) :=
  (range m ×ˢ range m).filter fun z =>
    1<z.1 ∧ z.1≤z.2 ∧ z.2<2*z.1 ∧ InWindow n (z.1+z.2) ∧ z.1*z.2 ≡ n [MOD m]

/-- If both primes are below m, their least residues survive, and the
filtered pairs consist of the original factor pair alone. -/
theorem matched_pairs {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (order : p≤q) (bal : q<2*p)
    (wide : q<m) (large : p*q≤8*m) : pairs (p*q) m = {(p,q)} := by
  ext ⟨x,y⟩
  rw [pairs,mem_filter,mem_singleton]
  constructor
  · rintro ⟨_,nontrivial,xy,bound,window,congruent⟩
    obtain ⟨rfl,rfl⟩ := ordered_semiprime_pair_unique hp hq order xy nontrivial
      (exact_lift xy bound window large congruent)
    rfl
  · rintro eqn
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eqn
    exact ⟨mem_product.mpr ⟨mem_range.mpr (order.trans_lt wide),mem_range.mpr wide⟩,
      hp.one_lt,order,bal,true_window order bal,Nat.ModEq.refl _⟩

/-- For m above both primes the nonunit prefix reading is already zero. -/
theorem count_zero {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (order : p<q)
    (wide : q<m) : FractionalNonunitPrefix.prefixCount (p*q) m = 0 := by
  rw [FractionalNonunitPrefix.quotient_sum hp hq order.ne (hq.one_lt.trans wide),
    Nat.div_eq_of_lt wide, Nat.div_eq_of_lt (order.trans wide),zero_add]

/-- A compatible pair of unit representatives contributes its sum to the
entire ordinary correction menu, even if the pair fails the balance test. -/
theorem in_full_menu {x y m n : ℕ} [NeZero m] (xm : x<m) (ym : y<m)
    (xc : x.Coprime m) (yc : y.Coprime m) (nc : n.Coprime m) (congruent : x*y ≡ n [MOD m]) :
    x+y ∈ menu (ZMod.unitOfCoprime n nc) := by
  have product : ZMod.unitOfCoprime x xc * ZMod.unitOfCoprime y yc = ZMod.unitOfCoprime n nc := by
    apply Units.ext
    simp only [Units.val_mul,ZMod.coe_unitOfCoprime,←Nat.cast_mul]
    exact (ZMod.natCast_eq_natCast_iff ..).mpr congruent
  rw [←product]
  simpa only [Nat.mod_eq_of_lt xm,Nat.mod_eq_of_lt ym] using actual xc yc

/-- The integer rounding of the 1/8 threshold is sharp under the two
window tests: at 8m=N−1, a false least residue pair can attain product N+m.
This growing family makes no claim that N or the lifted entries are prime. -/
theorem one_below (k : ℕ) (pos : 1≤k) :
    let m := 9*k^2+2*k
    let n := 8*m+1
    let x := 9*k+1
    1<x ∧ x<m ∧ x<2*x ∧ InWindow n (x+x) ∧ x*x ≡ n [MOD m] ∧ x*x=n+m ∧ x*x≠n := by
  let m := 9*k^2+2*k
  let n := 8*m+1
  let x := 9*k+1
  have bound := Nat.mul_le_mul_right k pos
  have xm : x<m := by dsimp only [x,m]; nlinarith only [bound,pos]
  have product : x*x=n+m := by dsimp [n,m,x]; ring
  have lower : 4*n≤(x+x)^2 := by dsimp [n,m,x]; nlinarith only [Nat.zero_le (k^2),Nat.zero_le k]
  have upper : 2*(x+x)^2+1=9*n := by dsimp [n,m,x]; ring
  have xx : 1<x := by dsimp [x]; omega
  have strict : 2*(x+x)^2<9*n := Nat.lt_of_succ_le upper.le
  have mp : 0<m := (Nat.zero_lt_one.trans xx).trans xm
  have different : x*x≠n := by rw [product]; exact (Nat.lt_add_of_pos_right mp).ne'
  exact ⟨xx,xm,by omega,⟨lower,strict⟩,product ▸ Nat.add_modEq_right,product,different⟩

/-- An ordinary correction together with least unit representatives witnessing it. -/
def HasRepresentatives (n m s : ℕ) : Prop :=
  ∃ x<m, ∃ y<m, x.Coprime m ∧ y.Coprime m ∧ x*y ≡ n [MOD m] ∧ x+y=s

theorem representatives_mem {n m s : ℕ} [NeZero m] (nc : n.Coprime m)
    (w : HasRepresentatives n m s) : s ∈ menu (ZMod.unitOfCoprime n nc) := by
  obtain ⟨x,xm,y,ym,xc,yc,prod,rfl⟩ := w
  exact in_full_menu xm ym xc yc nc prod

/-- For 12827, the two distinct ordinary corrections 228 and 232 both
satisfy the public sum bound. The second has a representative pair (23,209)
whose product is five whole moduli below N and whose ratio exceeds two. -/
theorem example_12827 :
    Nat.Coprime 12827 1604 ∧ HasRepresentatives 12827 1604 228 ∧
    HasRepresentatives 12827 1604 232 ∧ InWindow 12827 228 ∧ InWindow 12827 232 ∧
    (23*209 : ℕ)+5*1604=12827 ∧ 2*23≤209 ∧ pairs 12827 1604={(101,127)} := by
  refine ⟨by decide,?_,?_,by decide,by decide,by decide,by decide,?_⟩
  · exact ⟨101,by decide,127,by decide,by decide,by decide,by decide,by decide⟩
  · exact ⟨23,by decide,209,by decide,by decide,by decide,by decide,by decide⟩
  · rw [show 12827 = 101*127 by decide]
    apply matched_pairs <;> decide +kernel

/-- Just seventeen below the scaled cutoff, even distinct odd prime
representatives of the same ten-bit width can give a false lift. Both pairs
pass the actual two windows. -/
theorem ten_bit_prime_control :
    Nat.Prime 643 ∧ Nat.Prime 907 ∧ Nat.Prime 809 ∧ Nat.Prime 811 ∧
    512≤643 ∧ 643<809 ∧ 809<811 ∧ 811<907 ∧ 907<1024 ∧
    Nat.Coprime 583201 72898 ∧ 643*907=583201 ∧ 8*72898+17=583201 ∧
    809*811=583201+72898 ∧ 2*1620^2+9=9*583201 ∧
    (643,907)∈pairs 583201 72898 ∧ (809,811)∈pairs 583201 72898 := by
  simp only [pairs,mem_filter,mem_product,mem_range, InWindow]
  decide +kernel

end PrimeFactors.FractionalBalancedLifts
