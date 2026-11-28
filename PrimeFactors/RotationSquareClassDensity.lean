import PrimeFactors.RotationSquareRootCount
import PrimeFactors.BinaryRotationModulus

/-! Fractions of all unit residues occupied by the square and doubled-square
conditions. The sample in these identities runs over one entire period. -/

namespace PrimeFactors.RotationSquareClassDensity

open Finset RotationSquareRootCount
open scoped Classical

noncomputable def units (m : ℕ) : Finset ℕ :=
  (range m).filter fun n => n.Coprime m

/-- Unit product residues n for which c*n is a square modulo m. -/
noncomputable def accepted (m c : ℕ) : Finset ℕ :=
  (units m).filter fun n => (residues m (c*n)).Nonempty

theorem mem_units {m n : ℕ} : n∈units m ↔ n<m ∧ n.Coprime m := by
  simp [units]

theorem card_units (m : ℕ) : (units m).card=m.totient := by
  rw [Nat.totient_eq_card_coprime]
  apply congrArg Finset.card
  ext n
  simp [units, Nat.coprime_comm]

theorem mem_square {m n : ℕ} : n∈accepted m 1 ↔ n∈units m ∧ (residues m n).Nonempty := by
  simp [accepted]

private theorem cop_congr {a b m : ℕ} (same : a ≡ b [MOD m]) :
    a.Coprime m ↔ b.Coprime m := by unfold Nat.Coprime; rw [same.gcd_eq]

private theorem congr_residues {m a b : ℕ} (same : a ≡ b [MOD m]) :
    residues m a=residues m b := by
  ext x
  simp only [mem_residues]
  exact and_congr_right fun _ => ⟨fun h => h.trans same,fun h => h.trans same.symm⟩

/-- Counting squaring as a map from the units to its image: each target in
the image has exactly k inputs. -/
theorem square_count {m k : ℕ} (pos : 0<m)
    (fiber : ∀ a∈accepted m 1, (residues m a).card=k) :
    k*(accepted m 1).card=m.totient := by
  let f (x : ℕ) := x^2%m
  have covered (x : ℕ) (hx : x∈units m) : f x∈accepted m 1 := by
    have cu := ((cop_congr (Nat.mod_modEq (x^2) m)).mpr ((mem_units.mp hx).2.pow_left 2))
    exact mem_square.mpr ⟨mem_units.mpr ⟨Nat.mod_lt _ pos,cu⟩,
      x,mem_residues.mpr ⟨(mem_units.mp hx).1,(Nat.mod_modEq ..).symm⟩⟩
  have each (a : ℕ) (ha : a∈accepted m 1) :
      ((units m).filter (fun x => f x=a))=residues m a := by
    obtain ⟨below,unit⟩ := mem_units.mp (mem_square.mp ha).1
    ext x
    rw [mem_filter,mem_units,mem_residues]
    have eqv : f x=a ↔ x^2 ≡ a [MOD m] := by simp only [f,Nat.ModEq,Nat.mod_eq_of_lt below]
    constructor
    · rintro ⟨⟨low,_⟩,val⟩
      exact ⟨low,eqv.mp val⟩
    · rintro ⟨low,root⟩
      have xs := (cop_congr root).mpr unit
      rw [pow_two,Nat.coprime_mul_iff_left] at xs
      exact ⟨⟨low,xs.1⟩,eqv.mpr root⟩
  have count := card_eq_sum_card_fiberwise (s:=units m) (t:=accepted m 1) (f:=f) covered
  rw [←card_units m,count]
  calc k*(accepted m 1).card = ∑ _a∈accepted m 1,k := by simp [Nat.mul_comm]
       _ = _ := sum_congr rfl (fun a ha => by rw [each a ha,fiber a ha])

/-- Over an odd squarefree modulus, exactly one unit in 2^ω(m) is a square. -/
theorem squarefree_count {m : ℕ} (odd : Odd m) (sf : Squarefree m) :
    2^m.primeFactors.card*(accepted m 1).card=m.totient := by
  have mp : 0<m := Nat.pos_of_ne_zero sf.ne_zero
  have prod := Nat.prod_primeFactorsList mp.ne'
  have nodup := (Nat.squarefree_iff_nodup_primeFactorsList mp.ne').mp sf
  have prime (p : ℕ) (hp : p∈m.primeFactorsList) : p.Prime ∧ p≠2 := by
    refine ⟨Nat.prime_of_mem_primeFactorsList hp,?_⟩
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr odd) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactorsList hp))
  have co := nodup.pairwise_of_forall_ne fun p hp q hq ne =>
    (Nat.coprime_primes (prime p hp).1 (prime q hq).1).mpr ne
  apply square_count mp
  intro a ha
  obtain ⟨unit,y,hy⟩ := mem_square.mp ha
  have r := (mem_residues.mp hy).2
  have cu := (mem_units.mp unit).2
  have size : m.primeFactors.card=m.primeFactorsList.length :=
    List.toFinset_card_of_nodup nodup
  rw [size]
  have counts := list_count prime co (prod.symm ▸ cu) (prod.symm ▸ r)
  simpa only [prod] using counts

/-- Multiplying the tested product by any fixed unit preserves the number of
accepted residue classes. -/
theorem scaled_count {m c : ℕ} (pos : 0<m) (cu : c.Coprime m) :
    (accepted m c).card=(accepted m 1).card := by
  let d (x : ℕ) := c*x%m
  have inside (x : ℕ) (hx : x∈units m) : d x∈units m := by
    exact mem_units.mpr ⟨Nat.mod_lt _ pos,
      (cop_congr (Nat.mod_modEq ..)).mpr (Nat.coprime_mul_iff_left.mpr ⟨cu,(mem_units.mp hx).2⟩)⟩
  have inj : Set.InjOn d (units m : Set ℕ) := by
    intro x hx y hy h
    have eq : x ≡ y [MOD m] := Nat.ModEq.cancel_left_of_coprime cu.symm h
    simpa only [Nat.ModEq,Nat.mod_eq_of_lt (mem_units.mp hx).1,
      Nat.mod_eq_of_lt (mem_units.mp hy).1] using eq
  have entire : (units m).image d=units m := by
    apply eq_of_subset_of_card_le
    · exact image_subset_iff.mpr inside
    · exact (card_image_of_injOn inj).symm.le
  have iff' (x : ℕ) (hx : x∈units m) : x∈accepted m c ↔ d x∈accepted m 1 := by
    simp only [accepted,mem_filter,one_mul,hx,inside x hx,true_and]
    rw [congr_residues (Nat.mod_modEq (c*x) m)]
  have onto : (accepted m c).image d=accepted m 1 := by
    ext y
    constructor
    · intro ys
      obtain ⟨x,hx,rfl⟩ := mem_image.mp ys
      exact (iff' x (mem_filter.mp hx).1).mp hx
    · intro ys
      have ym := (mem_square.mp ys).1
      rw [←entire] at ym
      obtain ⟨x,hx,rfl⟩ := mem_image.mp ym
      exact mem_image.mpr ⟨x,(iff' x hx).mpr ys,rfl⟩
  rw [←onto,card_image_of_injOn (inj.mono (show accepted m c ⊆ units m from filter_subset ..))]

private theorem mod_three {m n : ℕ} (three : 3∣m) (unit : n.Coprime m)
    (occupied : (residues m n).Nonempty) : n%3=1 := by
  obtain ⟨x,hx⟩ := occupied
  have eq := (mem_residues.mp hx).2.of_dvd three
  change x^2%3=n%3 at eq
  rw [Nat.pow_mod] at eq
  have nz : n%3≠0 := by
    intro h
    have dvd := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h) three
    rw [unit] at dvd
    norm_num at dvd
  rcases (show x%3=0 ∨ x%3=1 ∨ x%3=2 by omega) with h|h|h <;> norm_num [h] at eq <;> omega

/-- When three divides the odd modulus the two equally populated classes
are disjoint, by their opposite required unit residues modulo three. -/
theorem union_count {m : ℕ} (odd : Odd m) (sf : Squarefree m) (three : 3∣m) :
    2^m.primeFactors.card*((accepted m 1) ∪ (accepted m 2)).card=2*m.totient := by
  have two := odd.coprime_two_right.symm
  have dis : Disjoint (accepted m 1) (accepted m 2) := by
    apply disjoint_left.mpr
    intro n h₁ h₂
    obtain ⟨unit,first⟩ := mem_square.mp h₁
    have cu := (mem_units.mp unit).2
    have l := mod_three three cu first
    have r := mod_three three (Nat.coprime_mul_iff_left.mpr ⟨two,cu⟩) (mem_filter.mp h₂).2
    rw [Nat.mul_mod, l] at r
    norm_num at r
  rw [card_union_of_disjoint dis, scaled_count (Nat.pos_of_ne_zero sf.ne_zero) two,
    Nat.mul_add, squarefree_count odd sf]
  omega

/-- The square or twice-square condition accepts precisely one in 32,768
uniform unit residues for the certified public rotation modulus. -/
theorem full_width : 32768*((accepted BinaryRotationModulus.M 1) ∪
    (accepted BinaryRotationModulus.M 2)).card=BinaryRotationModulus.M.totient := by
  have odd : Odd BinaryRotationModulus.M := Nat.odd_iff.mpr (by decide +kernel)
  have three : 3∣BinaryRotationModulus.M := by decide +kernel
  have count := union_count odd BinaryRotationModulus.squarefree three
  rw [BinaryRotationModulus.card] at count
  omega

end PrimeFactors.RotationSquareClassDensity
