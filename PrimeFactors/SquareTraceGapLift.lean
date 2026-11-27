import PrimeFactors.ResidueCount
import PrimeFactors.PrimePower

/-! In a prime field of characteristic at least seven, each prescribed difference between
two traces of a nonzero square product has a witness with at least one regular trace.
The exceptional difference between the two singular traces has a rational witness with
denominators dividing six. A unit factor anchors the other trace at any prime power. -/
namespace PrimeFactors.SquareTraceGapLift
open Finset

/-- A set occupying strictly more than half the residues realizes every difference. -/
private theorem overlap {ℓ : ℕ} [Fact ℓ.Prime] (A : Finset (ZMod ℓ)) (t : ZMod ℓ)
    (size : ℓ<2*A.card) : ∃ s∈A, s+t∈A := by
  classical
  by_contra! sep
  let B := A.image (fun x => x+t)
  have disjoint : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro z az bz
    obtain ⟨s,hs,rfl⟩ := mem_image.mp bz
    exact sep s hs az
  have cap := card_le_univ (A∪B)
  rw [ZMod.card,card_union_of_disjoint disjoint,
      show B.card=A.card from card_image_of_injective A (fun _ _ h => add_right_cancel h)] at cap
  omega

private theorem small_nz {ℓ a : ℕ} [Fact ℓ.Prime] (pos : 0<a) (lt : a<ℓ) :
    (a : ZMod ℓ)≠0 := fun eq => (not_le_of_gt lt) (Nat.le_of_dvd pos ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp eq))

/-- At gap 4u, (3u/2,2u/3) and (6u,u/6) give sums 13u/6 and 37u/6.
The first discriminant is (5u/6)² and remains regular in characteristic seven. -/
private theorem explicit {ℓ : ℕ} [Fact ℓ.Prime] (large : 7≤ℓ) {u : ZMod ℓ} (hu : u≠0) :
    ∃ s : ZMod ℓ, AdmissibleSum (u*u) s ∧ AdmissibleSum (u*u) (s+4*u) ∧ s^2-4*(u*u)≠0 := by
  have h2 : (2:ZMod ℓ)≠0 := small_nz (a:=2) (by decide) (by omega)
  have h3 : (3:ZMod ℓ)≠0 := small_nz (a:=3) (by decide) (by omega)
  have h5 : (5:ZMod ℓ)≠0 := small_nz (a:=5) (by decide) (by omega)
  have h6 : (6:ZMod ℓ)≠0 := small_nz (a:=6) (by decide) (by omega)
  refine ⟨13*u/6,⟨3*u/2,2*u/3,?_,?_⟩,⟨6*u,u/6,?_,?_⟩,?_⟩
  · field_simp; ring
  · field_simp; ring
  · field_simp; ring
  · field_simp; ring
  · rw [show (13*u/6)^2-4*(u*u)=(5*u/6)^2 by field_simp; ring]
    exact pow_ne_zero _ (div_ne_zero (mul_ne_zero h5 hu) h6)

/-- Every field gap has a witness with at least one nonzero discriminant. -/
theorem regular_gap {ℓ : ℕ} [Fact ℓ.Prime] (large : 7≤ℓ) (n t : ZMod ℓ)
    (hn : n≠0) (sq : IsSquare n) :
    ∃ s : ZMod ℓ, AdmissibleSum n s ∧ AdmissibleSum n (s+t) ∧
      (s^2-4*n≠0 ∨ (s+t)^2-4*n≠0) := by
  obtain ⟨u,rfl⟩ := sq
  have hu : u≠0 := fun h => hn (by rw [h,zero_mul])
  obtain ⟨w,wa,wb,wr⟩ := explicit large hu
  by_cases t0 : t=0
  · simpa only [t0,add_zero] using ⟨w,wa,wa,Or.inl wr⟩
  by_cases pos : t=4*u
  · exact ⟨w,wa,pos ▸ wb,Or.inl wr⟩
  by_cases neg : t=-(4*u)
  · refine ⟨w+4*u,wb,?_,Or.inr ?_⟩ <;> simpa only [neg,add_neg_cancel_right] using (by assumption)
  have card := card_factorSumResidues_of_square ℓ (by omega) (u*u) hn ⟨u,rfl⟩
  obtain ⟨k,hk⟩ := (Fact.out : ℓ.Prime).odd_of_ne_two (by omega)
  obtain ⟨s,a,b⟩ := overlap (factorSumResidues ℓ (u*u)) t (by omega)
  refine ⟨s,(mem_factorSumResidues_iff ℓ hn).mp a,(mem_factorSumResidues_iff ℓ hn).mp b,?_⟩
  by_contra! bad
  have roots {x : ZMod ℓ} (h : x^2-4*(u*u)=0) : x=2*u ∨ x=-(2*u) :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by linear_combination h : x^2=(2*u)^2)
  rcases roots bad.1 with h|h <;> rcases roots bad.2 with j|j
  · exact t0 (by linear_combination j-h)
  · exact neg (by linear_combination j-h)
  · exact pos (by linear_combination j-h)
  · exact t0 (by linear_combination j-h)

/-- Any compatible trace has some compatible prime-power lift, even when it is singular.
Lift a unit factor and form its complementary factor using the product at the new modulus. -/
theorem anchor {ℓ : ℕ} [Fact ℓ.Prime] (n : ℤ) (hn : (n : ZMod ℓ)≠0) {s : ZMod ℓ}
    (a : AdmissibleSum (n : ZMod ℓ) s) (k : ℕ) :
    ∃ S : ℤ, (S : ZMod ℓ)=s ∧ AdmissibleSum (n : ZMod (ℓ^(k+1))) S := by
  obtain ⟨x,y,xy,xs⟩ := a
  have hx : x≠0 := fun h => hn (by rw [←xy,h,zero_mul])
  have cop : x.val.Coprime ℓ := (ZMod.isUnit_iff_coprime ..).mp (by
    rw [ZMod.natCast_zmod_val]; exact hx.isUnit)
  let m := ℓ^(k+1)
  let U : (ZMod m)ˣ := ZMod.unitOfCoprime x.val (cop.pow_right _)
  let Y := (n : ZMod m)*(↑(U⁻¹) : ZMod m)
  let red : ZMod m →+* ZMod ℓ := ZMod.castHom (dvd_pow_self ℓ (Nat.succ_ne_zero k)) _
  have ux : red (U : ZMod m)=x := by simp [U,ZMod.coe_unitOfCoprime]
  have prod : (U : ZMod m)*Y=n := by
    calc _ = ((U : ZMod m)*↑(U⁻¹))*(n : ZMod m) := by unfold Y; ring
         _ = _ := by simp
  have uy : red Y=y := by
    apply mul_left_cancel₀ hx
    rw [xy,←ux,←map_mul,prod,map_intCast]
  obtain ⟨S,hS⟩ := ZMod.intCast_surjective ((U : ZMod m)+Y)
  refine ⟨S,?_,⟨U,Y,prod,hS.symm⟩⟩
  have sr := congrArg red hS
  simpa only [map_intCast,map_add,ux,uy,xs] using sr

private theorem lift_right {ℓ : ℕ} [Fact ℓ.Prime] (odd : ℓ≠2) (n t : ℤ)
    (hn : (n : ZMod ℓ)≠0) (k : ℕ) {s : ZMod ℓ} (a : AdmissibleSum (n : ZMod ℓ) s)
    (b : AdmissibleSum (n : ZMod ℓ) (s+(t : ZMod ℓ))) (reg : (s+(t : ZMod ℓ))^2-4*(n:ZMod ℓ)≠0) :
    ∃ S : ZMod (ℓ^(k+1)), AdmissibleSum (n : ZMod (ℓ^(k+1))) S ∧
      AdmissibleSum (n : ZMod (ℓ^(k+1))) (S+(t : ZMod (ℓ^(k+1)))) := by
  obtain ⟨S,hs,ha⟩ := anchor n hn a k
  have h : ((S+t : ℤ) : ZMod ℓ)=s+(t : ZMod ℓ) := by rw [Int.cast_add,hs]
  have regular : (((S+t)^2-4*n : ℤ) : ZMod ℓ)≠0 := by
    simpa only [Int.cast_sub,Int.cast_pow,Int.cast_mul,Int.cast_ofNat,h] using reg
  have lifted := (admissibleSum_primePow_iff_of_regular odd n (S+t) regular k).mpr (h ▸ b)
  exact ⟨S,ha,by simpa only [Int.cast_add] using lifted⟩

/-- Every prescribed gap lifts through all positive prime powers for a product whose
nonzero base residue is square. Only one of the two traces needs a nonzero discriminant. -/
theorem power {ℓ : ℕ} [Fact ℓ.Prime] (large : 7≤ℓ) (n t : ℤ)
    (hn : (n : ZMod ℓ)≠0) (sq : IsSquare (n : ZMod ℓ)) (k : ℕ) :
    ∃ s : ZMod (ℓ^(k+1)), AdmissibleSum (n : ZMod (ℓ^(k+1))) s ∧
      AdmissibleSum (n : ZMod (ℓ^(k+1))) (s+(t : ZMod (ℓ^(k+1)))) := by
  obtain ⟨s,a,b,left|right⟩ := regular_gap large (n : ZMod ℓ) (t : ZMod ℓ) hn sq
  · have shift : s+(t : ZMod ℓ)+((-t : ℤ) : ZMod ℓ)=s := by simp
    obtain ⟨w,wa,wb⟩ := lift_right (by omega : ℓ≠2) n (-t) hn k b (by rw [shift]; exact a) (by rw [shift]; exact left)
    exact ⟨w+((-t : ℤ) : ZMod (ℓ^(k+1))),wb,by simpa using wa⟩
  · exact lift_right (by omega) n t hn k a b right

end PrimeFactors.SquareTraceGapLift
