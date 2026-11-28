import PrimeFactors.PrimeSquareSumWeights

/-! Multiplicities of factor sums modulo an odd prime cube. The fixed product
is public and the ordered local factor pairs are sampled uniformly. -/

open private PrimeFactors.digit_card PrimeFactors.count_digits PrimeFactors.count_if
  PrimeFactors.two_unit
  from PrimeFactors.PrimePowerCount

namespace PrimeFactors.PrimeCubeSumWeights

open PrimeSquareSumWeights
open scoped Classical

variable {p : ℕ} [Fact p.Prime]

private def raise (p : ℕ) (x : ZMod (p^2)) : ZMod (p^3) :=
  ((p*x.val : ℕ) : ZMod (p^3))

omit [Fact p.Prime] in
private theorem raise_cast (a : ℕ) : raise p (a : ZMod (p^2))=((p*a : ℕ) : ZMod (p^3)) := by
  unfold raise
  rw [ZMod.val_natCast,ZMod.natCast_eq_natCast_iff,show p^3=p*p^2 by ring]
  exact (Nat.mod_modEq a (p^2)).mul_left' p

private theorem cancel_square (v u : ℕ) :
    ((p*v : ℕ) : ZMod (p^3))^2=((p^2*u : ℕ) : ZMod (p^3)) ↔ (v : ZMod p)^2=u := by
  rw [←Nat.cast_pow,←Nat.cast_pow,mul_pow,ZMod.natCast_eq_natCast_iff,
    ZMod.natCast_eq_natCast_iff,show p^3=p^2*p by ring]
  exact ⟨Nat.ModEq.mul_left_cancel' (pow_ne_zero 2 (Fact.out : p.Prime).ne_zero),
    fun h => h.mul_left' _⟩

/-- Removing a factor of p from a root of p²u leaves a root of u modulo p
and one free base-p digit. -/
theorem roots_scaled (u : ℕ) :
    Nat.card {d : ZMod (p^3) // d^2=((p^2*u : ℕ) : ZMod (p^3))} =
      Nat.card {x : ZMod p // x^2=u}*p := by
  classical
  let lift (x : {y : ZMod (p^2) // (firstPrimeDigit p 1 y)^2=u}) :
      {d : ZMod (p^3) // d^2=((p^2*u : ℕ) : ZMod (p^3))} :=
    ⟨raise p x.val,by
      obtain ⟨v,hv⟩ := ZMod.natCast_zmod_surjective x.val
      rw [←hv,raise_cast,cancel_square]
      simpa only [←hv,map_natCast] using x.property⟩
  have inject : Function.Injective lift := by
    rintro ⟨x,hx⟩ ⟨y,hy⟩ eq
    have h : raise p x=raise p y := congrArg Subtype.val eq
    obtain ⟨v,rfl⟩ := ZMod.natCast_zmod_surjective x
    obtain ⟨w,rfl⟩ := ZMod.natCast_zmod_surjective y
    rw [raise_cast,raise_cast,ZMod.natCast_eq_natCast_iff,show p^3=p*p^2 by ring] at h
    exact Subtype.ext ((ZMod.natCast_eq_natCast_iff ..).mpr
      (Nat.ModEq.mul_left_cancel' (Fact.out : p.Prime).ne_zero h))
  have onto : Function.Surjective lift := by
    rintro ⟨d,hd⟩
    obtain ⟨v,rfl⟩ := ZMod.natCast_zmod_surjective d
    have digit : (v : ZMod p)^2=0 := by
      simpa using congrArg (firstPrimeDigit p 2) hd
    obtain ⟨w,rfl⟩ := (ZMod.natCast_zmod_eq_zero_iff_dvd v p).mp (pow_eq_zero digit)
    exact ⟨⟨(w : ZMod (p^2)),by rw [map_natCast]; exact (cancel_square w u).mp hd⟩,
      Subtype.ext (raise_cast w)⟩
  rw [←Nat.card_congr (Equiv.ofBijective lift ⟨inject,onto⟩),PrimeFactors.count_digits 1]
  calc
    _ = ∑ r : ZMod p, if r^2=(u : ZMod p) then p else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      split_ifs with h
      · have agree (s : ZMod (p^2)) : (firstPrimeDigit p 1 s=r ∧ (firstPrimeDigit p 1 s)^2=u) ↔
            firstPrimeDigit p 1 s=r := and_iff_left_of_imp (fun eq => eq ▸ h)
        rw [Nat.card_congr (Equiv.subtypeEquivRight agree)]
        simpa only [pow_one] using PrimeFactors.digit_card 1 r
      · exact Nat.card_eq_zero.mpr (Or.inl ⟨fun x => h (x.property.1 ▸ x.property.2)⟩)
    _ = _ := PrimeFactors.count_if _ _

private theorem zero_roots :
    Nat.card {d : ZMod (p^3) // d^2=0}=p := by
  have one : Nat.card {x : ZMod p // x^2=(0 : ZMod p)}=1 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
    simp [Finset.filter_eq']
  simpa only [mul_zero,Nat.cast_zero,one,one_mul] using roots_scaled (p:=p) 0

private theorem regular_roots (odd : p≠2) (D : ZMod (p^3))
    (nz : firstPrimeDigit p 2 D ≠ 0) (sq : IsSquare D) :
    Nat.card {x : ZMod (p^3) // x^2=D}=2 := by
  obtain ⟨d,rfl⟩ := ZMod.intCast_surjective D
  rw [map_intCast] at nz
  have fieldSq := (isSquare_primePow_iff_of_unit odd d nz 2).mp sq
  exact (primitiveNorm_odd_root_count odd d nz 2).trans (if_pos fieldSq)

private theorem field_roots (odd : p≠2) (u : ZMod p) (unit : u≠0) (sq : IsSquare u) :
    Nat.card {x : ZMod p // x^2=u}=2 := by
  obtain ⟨d,rfl⟩ := ZMod.intCast_surjective u
  have h := (primitiveNorm_odd_root_count odd d unit 0).trans (if_pos sq)
  exact (congrArg (fun m => Nat.card {x : ZMod m // x^2=(d : ZMod m)}) (pow_one p)).symm.trans h

private theorem repeated_roots (odd : p≠2) (D : ZMod (p^3)) (nz : D≠0)
    (digit : firstPrimeDigit p 2 D=0) (sq : IsSquare D) :
    Nat.card {x : ZMod (p^3) // x^2=D}=2*p := by
  obtain ⟨d,hd⟩ := (isSquare_iff_exists_sq _).mp sq
  obtain ⟨v,rfl⟩ := ZMod.natCast_zmod_surjective d
  have zero : (v : ZMod p)=0 := pow_eq_zero (n:=2) (by
    simpa only [hd,map_pow,map_natCast] using digit)
  obtain ⟨w,rfl⟩ := (ZMod.natCast_zmod_eq_zero_iff_dvd v p).mp zero
  have shape : D=((p^2*w^2 : ℕ) : ZMod (p^3)) := by rw [hd,←Nat.cast_pow,mul_pow]
  have notdiv : ¬p∣w := by
    rintro ⟨t,rfl⟩
    apply nz
    rw [shape,ZMod.natCast_zmod_eq_zero_iff_dvd]
    exact ⟨p*t^2,by ring⟩
  have unit : (w : ZMod p)≠0 := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp.mt notdiv
  rw [shape,roots_scaled,Nat.cast_pow,field_roots odd _ (pow_ne_zero _ unit) ⟨_,pow_two _⟩]

/-- The third digit separates three possible positive weights. A nonzero
admissible discriminant divisible by p receives twice the weight of zero. -/
theorem weight_formula (odd : p≠2) (n : ℕ) (s : ZMod (p^3)) :
    let D := s^2-4*(n : ZMod (p^3))
    weight n s = if D=0 then p else if AdmissibleSum (n : ZMod (p^3)) s then
      (if firstPrimeDigit p 2 D=0 then 2*p else 2) else 0 := by
  classical
  dsimp only
  let D := s^2-4*(n : ZMod (p^3))
  rw [weight_roots (PrimeFactors.two_unit odd 3)]
  change Nat.card {x : ZMod (p^3) // x^2=D}=_
  split_ifs with z a first
  · change D=0 at z
    rw [z]; exact zero_roots
  · exact repeated_roots odd D z first ((admissibleSum_iff_isSquare_of_two_unit
      (PrimeFactors.two_unit odd 3) _ _).mp a)
  · exact regular_roots odd D first ((admissibleSum_iff_isSquare_of_two_unit
      (PrimeFactors.two_unit odd 3) _ _).mp a)
  · apply Nat.card_eq_zero.mpr
    exact Or.inl ⟨fun x => a ((admissibleSum_iff_isSquare_of_two_unit
      (PrimeFactors.two_unit odd 3) _ _).mpr ⟨x.val,by rw [←pow_two]; exact x.property.symm⟩)⟩

/-- Highest-weight classes are precisely the admissible nonzero discriminants
whose first digit vanishes. Every other class has strictly smaller weight. -/
theorem maximal_iff (odd : p≠2) (n : ℕ) (s : ZMod (p^3)) :
    weight n s ≤ 2*p ∧ (weight n s=2*p ↔ AdmissibleSum (n : ZMod (p^3)) s ∧
      firstPrimeDigit p 2 (s^2-4*(n : ZMod (p^3)))=0 ∧ s^2-4*(n : ZMod (p^3))≠0) := by
  rw [weight_formula odd n s]
  have h := (Fact.out : p.Prime).two_le
  split_ifs <;> simp_all <;> omega

private theorem collision_count (odd : p≠2) {n : ℕ} (unit : ¬p∣n) (sq : IsSquare (n : ZMod p)) :
    Nat.card {s : ZMod (p^3) // AdmissibleSum (n : ZMod (p^3)) s ∧
      firstPrimeDigit p 2 (s^2-4*(n : ZMod (p^3)))=0} = 2*((p-1)/2+1) := by
  classical
  have nz : firstPrimeDigit p 2 (n : ZMod (p^3))≠0 := by
    rw [map_natCast]; exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp.mt unit
  rw [PrimeFactors.count_digits 2]
  calc
    _ = ∑ r : ZMod p, if r^2-4*(n : ZMod p)=0 then (p-1)/2+1 else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      have same (s : ZMod (p^3)) (eq : firstPrimeDigit p 2 s=r) :
          firstPrimeDigit p 2 (s^2-4*(n : ZMod (p^3)))=r^2-4*(n : ZMod p) := by
        simp [eq,map_ofNat]
      split_ifs with zero
      · have iffAt (s : ZMod (p^3)) : (firstPrimeDigit p 2 s=r ∧
            AdmissibleSum (n : ZMod (p^3)) s ∧ firstPrimeDigit p 2 (s^2-4*n)=0) ↔
            firstPrimeDigit p 2 s=r ∧ AdmissibleSum (n : ZMod (p^3)) s :=
          ⟨fun h => ⟨h.1,h.2.1⟩,fun h => ⟨h.1,h.2,(same s h.1).trans zero⟩⟩
        rw [Nat.card_congr (Equiv.subtypeEquivRight iffAt),
          card_admissible_singular_digit odd 2 _ nz (by simpa only [map_natCast] using zero),
          card_squares_zero_digit 1,card_primePower_squares odd 1,primePowerSquareCount]
      · exact Nat.card_eq_zero.mpr (Or.inl ⟨fun x => zero ((same x.val x.property.1).symm.trans
          x.property.2.2)⟩)
    _ = _ := by
      rw [PrimeFactors.count_if]
      have h := StableDiscriminantClasses.zero_count odd unit 0
      have eq := congrArg (fun m => Nat.card {s : ZMod m // s^2-4*(n : ZMod m)=0}) (pow_one p)
      exact congrArg (fun k => k*((p-1)/2+1)) (eq.symm.trans (h.trans (if_pos sq)))

/-- There are p−1 best first guesses for every square unit product modulo p³. -/
theorem maximal_count (odd : p≠2) {n : ℕ} (unit : ¬p∣n) (sq : IsSquare (n : ZMod p)) :
    Nat.card {s : ZMod (p^3) // weight n s=2*p} = p-1 := by
  classical
  let D (s : ZMod (p^3)) := s^2-4*(n : ZMod (p^3))
  let collisions := Finset.univ.filter (fun s : ZMod (p^3) =>
    AdmissibleSum (n : ZMod (p^3)) s ∧ firstPrimeDigit p 2 (D s)=0)
  have size : collisions.card=2*((p-1)/2+1) := by
    simpa only [collisions,D,Nat.card_eq_fintype_card,Fintype.card_subtype] using
      collision_count odd unit sq
  have zeros : (collisions.filter (fun s => D s=0)).card=2 := by
    have eq : collisions.filter (fun s => D s=0)=Finset.univ.filter (fun s => D s=0) := by
      ext s
      simp only [collisions,Finset.mem_filter,Finset.mem_univ,true_and]
      refine and_iff_right_of_imp (fun z => ⟨?_,by rw [z,map_zero]⟩)
      apply (admissibleSum_iff_isSquare_of_two_unit (PrimeFactors.two_unit odd 3) _ _).mpr
      change IsSquare (D s)
      rw [z]; exact ⟨0,by simp⟩
    rw [eq]
    simpa only [D,Nat.card_eq_fintype_card,Fintype.card_subtype,sq,if_true] using
      StableDiscriminantClasses.zero_count odd unit 2
  have winners : collisions.filter (fun s => D s≠0) =
      Finset.univ.filter (fun s : ZMod (p^3) => weight n s=2*p) := by
    ext s
    simp only [collisions,Finset.mem_filter,Finset.mem_univ,true_and,D,and_assoc,
      (maximal_iff odd n s).2]
  have h := Finset.filter_card_add_filter_neg_card_eq_card (s:=collisions) (fun s => D s=0)
  rw [zeros,winners,size] at h
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  obtain ⟨k,hk⟩ := (Fact.out : p.Prime).odd_of_ne_two odd
  omega

/-- Under the uniform distribution of ordered pairs of given square unit
product, the highest-weight classes together have probability 2/p. -/
theorem maximal_probability (odd : p≠2) {n : ℕ} (unit : ¬p∣n) (sq : IsSquare (n : ZMod p)) :
    (∑ s : {s : ZMod (p^3) // weight n s=2*p}, (weight n s.val : ℚ)) /
      Nat.card (Pairs n (p^3))=2/p := by
  classical
  have prime := (Fact.out : p.Prime)
  have cop := (prime.coprime_iff_not_dvd.mpr unit).symm
  have up := (ZMod.isUnit_iff_coprime n (p^3)).mpr (cop.pow_right 3)
  simp only [fun s : {s : ZMod (p^3) // weight n s=2*p} => s.property,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,←Nat.card_eq_fintype_card,maximal_count odd unit sq,
    total up,Nat.totient_prime_pow_succ prime 2,Nat.cast_sub prime.one_le,Nat.cast_pow,
    Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  have lo : (1 : ℚ)<p := by exact_mod_cast prime.one_lt
  field_simp [(show (0:ℚ)<p by linarith).ne',(sub_pos.mpr lo).ne']
  ring

/-- For product one, shifting the sum 2 by p² doubles its weight when the
third digit is observed. -/
theorem reversal_one (odd : p≠2) :
    weight 1 (2 : ZMod (p^3))=p ∧ weight 1 (2+(p : ZMod (p^3))^2)=2*p := by
  have cube : (p : ZMod (p^3))^3=0 := by rw [←Nat.cast_pow,ZMod.natCast_self]
  have four : (4 : ZMod p)≠0 := by
    have two : (2 : ZMod p)≠0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
    convert mul_ne_zero two two using 1
    norm_num
  constructor
  · rw [weight_formula odd]; norm_num
  · have shape : (2+(p : ZMod (p^3))^2)^2-4*(1 : ZMod (p^3))=
        ((p^2*4 : ℕ) : ZMod (p^3)) := by push_cast; linear_combination (p : ZMod (p^3))*cube
    rw [weight_roots (PrimeFactors.two_unit odd 3)]
    rw [Nat.cast_one]
    rw [shape,roots_scaled]
    change Nat.card {x : ZMod p // x^2=4}*p=2*p
    rw [field_roots odd 4 four ⟨2,by norm_num⟩]

/-- Complete positive support for product 1 modulo 27. -/
theorem control27 (s : ZMod 27) :
    weight 1 s = if s=11 ∨ s=16 then 6 else if s=2 ∨ s=25 then 3 else 0 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [weight_roots (PrimeFactors.two_unit (p:=3) (by decide) 3)]
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  revert s
  decide +kernel

end PrimeFactors.PrimeCubeSumWeights
