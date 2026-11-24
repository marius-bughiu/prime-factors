import PrimeFactors.MaskedRelations
import PrimeFactors.RationalSquare

namespace PrimeFactors.SameSourcePair

/-- Dividing the two cross products by their gcd leaves two individual
squares whenever their product is a square. -/
theorem reduced_squares {U V z : ℕ} (pos : 0 < U) (square : U*V = z^2) :
    ∃ u v, U = U.gcd V*u^2 ∧ V = U.gcd V*v^2 ∧ u.Coprime v := by
  let g := U.gcd V
  let A := U/g
  let B := V/g
  have gp : 0 < g := Nat.gcd_pos_of_pos_left _ pos
  have hu : g*A = U := Nat.mul_div_cancel' (Nat.gcd_dvd_left U V)
  have hv : g*B = V := Nat.mul_div_cancel' (Nat.gcd_dvd_right U V)
  have cop : A.Coprime B := Nat.coprime_div_gcd_div_gcd gp
  have prod : g^2*(A*B) = z^2 := by
    calc
      _ = (g*A)*(g*B) := by ring
      _ = _ := by rw [hu,hv,square]
  obtain ⟨t,ht⟩ := (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp
    (show g^2 ∣ z^2 from ⟨A*B,prod.symm⟩)
  have ab : A*B = t^2 := Nat.eq_of_mul_eq_mul_left (pow_pos gp 2)
    (by rw [prod, ht, mul_pow])
  obtain ⟨u,ua⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr cop : IsUnit (gcd A B)) ab
  obtain ⟨v,vb⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr cop.symm : IsUnit (gcd B A))
    ((Nat.mul_comm B A).trans ab)
  rw [ua,vb] at cop
  exact ⟨u,v,hu.symm.trans (congrArg (g*·) ua),hv.symm.trans (congrArg (g*·) vb),
    cop.of_dvd (dvd_pow_self _ two_ne_zero) (dvd_pow_self _ two_ne_zero)⟩

private theorem short_data {N U V z : ℕ} (upos : 0 < U) (vpos : 0 < V)
    (distinct : U ≠ V) (square : U*V = z^2) (short : 2*z < N) :
    let g := U.gcd V
    ∃ u v, U = g*u^2 ∧ V = g*v^2 ∧ g*u*v = z ∧ u ≠ v ∧ u+v<N := by
  let g := U.gcd V
  have gp : 0 < g := Nat.gcd_pos_of_pos_left _ upos
  obtain ⟨u,v,hu,hv,_⟩ := reduced_squares upos square
  change U = g*u^2 at hu
  change V = g*v^2 at hv
  have up : 0 < u := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hu; omega
  have vp : 0 < v := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hv; omega
  have root : g*u*v = z := by
    apply Nat.pow_left_injective two_ne_zero
    change (g*u*v)^2 = z^2
    calc
      _ = (g*u^2)*(g*v^2) := by ring
      _ = _ := by rw [← hu,← hv,square]
  have different : u ≠ v := fun h => distinct (hu.trans ((h ▸ hv).symm))
  have size : u+v < N := by
    have h₁ := (Nat.le_mul_of_pos_left u gp).trans (Nat.le_mul_of_pos_right (g*u) vp)
    have h₂ := Nat.le_mul_of_pos_left v (Nat.mul_pos gp up)
    rw [root] at h₁ h₂
    omega
  exact ⟨u,v,hu,hv,root,different,size⟩

/-- The computable gcd uses only the two cross products and the modulus.
The normalized roots have sum strictly below the modulus. -/
theorem split_cross_products {N U V z : ℕ} [NeZero N] (upos : 0 < U) (vpos : 0 < V)
    (distinct : U ≠ V) (same : U ≡ V [MOD N]) (unit : U.Coprime N)
    (square : U*V = z^2) (short : 2*z < N) :
    let g := U.gcd V
    let factor := (Nat.sqrt (U/g) + Nat.sqrt (V/g)).gcd N
    1 < factor ∧ factor < N ∧ factor ∣ N := by
  let g := U.gcd V
  have gp : 0 < g := Nat.gcd_pos_of_pos_left _ upos
  obtain ⟨u,v,hu,hv,_,different,size⟩ := short_data upos vpos distinct square short
  change U = g*u^2 at hu
  change V = g*v^2 at hv
  have gc : N.Coprime g := (unit.of_dvd_left (Nat.gcd_dvd_left U V)).symm
  have scaled : g*u^2 ≡ g*v^2 [MOD N] := hu ▸ hv ▸ same
  have eqv := scaled.cancel_left_of_coprime gc
  have sqmod : (u : ZMod N)^2 = (v : ZMod N)^2 := by
    simpa only [Nat.cast_pow] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr eqv
  have found := PrimeFactors.maskedRelations_short sqmod different size
  change 1 < (Nat.sqrt (U/g) + Nat.sqrt (V/g)).gcd N ∧ _
  have uroot : Nat.sqrt (U/g) = u := by rw [hu, Nat.mul_div_cancel_left _ gp, Nat.sqrt_eq']
  have vroot : Nat.sqrt (V/g) = v := by rw [hv, Nat.mul_div_cancel_left _ gp, Nat.sqrt_eq']
  change 1 < (Nat.sqrt (U/g) + Nat.sqrt (V/g)).gcd N ∧
    (Nat.sqrt (U/g) + Nat.sqrt (V/g)).gcd N < N ∧ (Nat.sqrt (U/g) + Nat.sqrt (V/g)).gcd N ∣ N
  rw [uroot,vroot]
  exact ⟨found.1,found.2,Nat.gcd_dvd_right _ _⟩

private theorem row_units {N a b : ℕ} [NeZero N] {r : ZMod N}
    (unit : IsUnit r) (primitive : b.Coprime a) (row : (a : ZMod N)*r = b) :
    a.Coprime N ∧ b.Coprime N := by
  have modEq : b ≡ a*r.val [MOD N] := (ZMod.natCast_eq_natCast_iff ..).mp
    (by simpa only [Nat.cast_mul,ZMod.natCast_zmod_val] using row.symm)
  have ha : a.Coprime N := by
    apply Nat.dvd_one.mp
    rw [← primitive.gcd_eq_one]
    apply Nat.dvd_gcd _ (Nat.gcd_dvd_left _ _)
    exact (modEq.dvd_iff (Nat.gcd_dvd_right a N)).mpr
      ((Nat.gcd_dvd_left a N).trans (dvd_mul_right _ _))
  have hr : r.val.Coprime N := (ZMod.isUnit_iff_coprime _ _).mp (by simpa using unit)
  exact ⟨ha,modEq.gcd_eq.trans (ha.mul hr)⟩

/-- Multiplication by a unit cannot identify the two short normalized roots
up to a global sign. Here U is the common cross product modulo N. -/
private theorem cross_signs {N U V z : ℕ} [NeZero N] (upos : 0 < U) (vpos : 0 < V)
    (distinct : U ≠ V) (unit : U.Coprime N) (square : U*V = z^2) (short : 2*z < N) :
    (U : ZMod N) ≠ z ∧ (U : ZMod N) ≠ -z := by
  let g := U.gcd V
  obtain ⟨u,v,hu,_,root,different,size⟩ := short_data upos vpos distinct square short
  change U = g*u^2 at hu
  change g*u*v = z at root
  have mu : IsUnit ((g*u : ℕ) : ZMod N) := (ZMod.isUnit_iff_coprime _ _).mpr
    (unit.of_dvd_left ⟨u, by rw [hu,sq,mul_assoc]⟩)
  have uc : (U : ZMod N) = (g*u : ℕ)*(u : ZMod N) := by
    rw [← Nat.cast_mul,hu,sq,mul_assoc]
  have zc : (z : ZMod N) = (g*u : ℕ)*(v : ZMod N) := by rw [← Nat.cast_mul,root]
  rw [uc,zc,← mul_neg]
  constructor
  · intro e
    exact different (((ZMod.natCast_eq_natCast_iff ..).mp (mu.mul_right_inj.mp e)).eq_of_lt_of_lt
      (by omega) (by omega))
  · intro e
    have h : ((u+v : ℕ) : ZMod N) = 0 := by
      rw [Nat.cast_add,mu.mul_right_inj.mp e,neg_add_cancel]
    exact Nat.not_dvd_of_pos_of_lt (by omega) size ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp h)

private theorem positive_signs {N a b c d z : ℕ} [NeZero N] {r : ZMod N} (unit : IsUnit r)
    (ap : 0 < a) (bp : 0 < b) (cp : 0 < c) (dp : 0 < d)
    (ba : b.Coprime a) (dc : d.Coprime c) (different : (b,a) ≠ (d,c))
    (left : (a : ZMod N)*r = b) (right : (c : ZMod N)*r = d)
    (short₁ : 2*(a*b)<N) (short₂ : 2*(c*d)<N) (square : (a*b)*(c*d)=z^2) :
    (a : ZMod N)*c*r ≠ z ∧ (a : ZMod N)*c*r ≠ -z := by
  have differentCross : a*d ≠ c*b := by
    intro h
    obtain ⟨eqn₁,eqn₂⟩ := PrimeFactors.rationalSquare_reduced_unique ap cp ba dc
      (by simpa [Nat.mul_comm] using h.symm)
    exact different (Prod.ext eqn₁ eqn₂)
  have small : 2*z < N := by
    have bound := (Nat.mul_le_mul_right (2*(c*d)) short₁.le).trans_lt
      (Nat.mul_lt_mul_of_pos_left short₂ (NeZero.pos N))
    have eqn : (2*z)^2 = (2*(a*b))*(2*(c*d)) := by rw [mul_pow,←square]; ring
    have h₂ : (2*z)^2 < N^2 := by simpa only [eqn,sq] using bound
    exact lt_of_not_ge fun h => (not_le_of_gt h₂) (Nat.pow_le_pow_left h _)
  have crossSq : (a*d)*(c*b) = z^2 := by rw [← square]; ring
  have result := cross_signs (Nat.mul_pos ap dp) (Nat.mul_pos cp bp) differentCross
    ((row_units unit ba left).1.mul (row_units unit dc right).2) crossSq small
  have repr : ((a*d : ℕ) : ZMod N) = (a : ZMod N)*c*r := by rw [Nat.cast_mul, ←right,mul_assoc]
  rwa [repr] at result

/-- Two distinct primitive signed short fractions from the same unit residue
always split the modulus when their signed norms multiply to a square.
The gcd uses the ordinary dependency root a*c*r and the positive root z. -/
theorem signed_rows {N a c z : ℕ} [NeZero N] {b d : ℤ} {r : ZMod N} (unit : IsUnit r)
    (ap : 0 < a) (cp : 0 < c) (bn : b ≠ 0) (dn : d ≠ 0)
    (ba : b.natAbs.Coprime a) (dc : d.natAbs.Coprime c) (different : (b,a) ≠ (d,c))
    (left : (a : ZMod N)*r = (b : ZMod N)) (right : (c : ZMod N)*r = (d : ZMod N))
    (short₁ : 2*(a*b.natAbs)<N) (short₂ : 2*(c*d.natAbs)<N)
    (square : ((a : ℤ)*b)*((c : ℤ)*d)=(z : ℤ)^2) :
    let factor := ((a : ZMod N)*c*r-z).val.gcd N
    1 < factor ∧ factor < N ∧ factor ∣ N := by
  have squareAbs : (a*b.natAbs)*(c*d.natAbs)=z^2 := by
    simpa only [Int.natAbs_mul,Int.natAbs_ofNat,Int.natAbs_pow] using congrArg Int.natAbs square
  have nonneg : 0 ≤ ((a : ℤ)*c)*(b*d) := by
    calc
      _ ≤ (z : ℤ)^2 := sq_nonneg _
      _ = _ := by rw [← square]; ring
  have acpos : (0 : ℤ) < a*c := by exact_mod_cast Nat.mul_pos ap cp
  have signs := mul_nonneg_iff.mp ((mul_nonneg_iff_of_pos_left acpos).mp nonneg)
  have differentAbs : (b.natAbs,a) ≠ (d.natAbs,c) := by
    intro h
    have he := congrArg (fun n : ℕ => (n : ℤ)) (congrArg Prod.fst h)
    change (b.natAbs : ℤ) = (d.natAbs : ℤ) at he
    rw [Int.natCast_natAbs, Int.natCast_natAbs] at he
    apply different
    have hac : a = c := congrArg Prod.snd h
    refine Prod.ext ?_ hac
    rcases signs with ⟨hb,hd⟩ | ⟨hb,hd⟩
    · simpa [abs_of_nonneg hb,abs_of_nonneg hd] using he
    · simpa [abs_of_nonpos hb,abs_of_nonpos hd] using he
  have apart : (a : ZMod N)*c*r ≠ z ∧ (a : ZMod N)*c*r ≠ -z := by
    rcases signs with ⟨hb,hd⟩ | ⟨hb,hd⟩
    · exact positive_signs unit ap (Int.natAbs_pos.mpr bn) cp (Int.natAbs_pos.mpr dn)
        ba dc differentAbs (by simpa [Nat.cast_natAbs,abs_of_nonneg hb] using left)
        (by simpa [Nat.cast_natAbs,abs_of_nonneg hd] using right) short₁ short₂ squareAbs
    · have h := positive_signs unit.neg ap (Int.natAbs_pos.mpr bn) cp (Int.natAbs_pos.mpr dn)
        ba dc differentAbs (by simp [mul_neg,left,Nat.cast_natAbs,abs_of_nonpos hb])
        (by simp [mul_neg,right,Nat.cast_natAbs,abs_of_nonpos hd]) short₁ short₂ squareAbs
      rw [mul_neg] at h
      exact ⟨fun e => h.2 (congrArg Neg.neg e), fun e => h.1 (by simp [e])⟩
  have sqmod : ((a : ZMod N)*c*r)^2=(z : ZMod N)^2 := by
    calc
      _ = ((a : ZMod N)*b)*(c*(d : ZMod N)) := by rw [←left,←right]; ring
      _ = _ := by simpa only [Int.cast_mul,Int.cast_pow,Int.cast_natCast] using
          congrArg (fun n : ℤ => (n : ZMod N)) square
  have split := PrimeFactors.maskedRelations_split sqmod apart.1 apart.2
  exact ⟨split.1,split.2,Nat.gcd_dvd_right _ _⟩

/-- Modulo 437 the residue 9 gives the fractions 9/1 and 4/49.
Their norm square root is 42, while the modular dependency root is 441. -/
theorem example_437 :
    49*9 % 437 = 4 ∧ 2*(49*4) < 437 ∧ 2*9 < 437 ∧ 9*(49*4) = 42^2 ∧
    (441-42).gcd 437 = 19 ∧ (21+2).gcd 437 = 23 ∧ 19*23 = 437 := by decide

end PrimeFactors.SameSourcePair
