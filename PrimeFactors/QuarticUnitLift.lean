import PrimeFactors.LeastPrimitiveQuarticDenominator

/-! Uniqueness of unit fourth roots in each residue class modulo an odd
denominator. Double use of the difference-of-squares identity handles
every power of the denominator, including powers of composite denominators. -/
namespace PrimeFactors.QuarticUnitLift

private theorem square_unique {d e z w : ℕ} (odd : Odd d) (unit : w.Coprime d)
    (same : z ≡ w [MOD d]) (hit : z^2 ≡ w^2 [MOD d^e]) : z ≡ w [MOD d^e] := by
  have sum : z+w ≡ 2*w [MOD d] := by simpa only [two_mul] using same.add_right w
  have cop : (z+w).Coprime d := by
    change Nat.gcd (z+w) d=1
    rw [sum.gcd_eq]
    exact (odd.coprime_two_right.mul_right unit.symm).symm
  apply Nat.ModEq.cancel_right_of_coprime ((cop.symm).pow_left e)
  convert hit.add_right (z*w) using 1 <;> ring

/-- Each unit residue modulo d has at most one lift that is a fourth root
of a prescribed residue modulo d^e. Only one of the two unit assumptions
is needed because the roots already agree modulo d. -/
theorem fourth_unique {d e z w : ℕ} (odd : Odd d) (unit : w.Coprime d)
    (same : z ≡ w [MOD d]) (hit : z^4 ≡ w^4 [MOD d^e]) : z ≡ w [MOD d^e] := by
  apply square_unique odd unit same
  apply square_unique odd (unit.pow_left 2) (same.pow 2)
  simpa only [← pow_mul] using hit

/-- The coefficient four can also be cancelled at every odd denominator. -/
theorem scaled_fourth_unique {d e z w : ℕ} (odd : Odd d) (unit : w.Coprime d)
    (same : z ≡ w [MOD d]) (hit : 4*z^4 ≡ 4*w^4 [MOD d^e]) : z ≡ w [MOD d^e] := by
  apply fourth_unique odd unit same
  exact Nat.ModEq.cancel_left_of_coprime ((odd.coprime_two_right.pow_right 2).pow_left e) hit

/-- In a primitive representation each coordinate is a unit at the denominator. -/
theorem primitive_units {n a b d : ℕ} (prim : a.Coprime b)
    (repr : d^4*n=a^4+4*b^4) : Odd d ∧ a.Coprime d ∧ b.Coprime d := by
  have odd := Nat.coprime_two_left.mp (Nat.prime_two.coprime_iff_not_dvd.mpr
    (LeastPrimitiveQuarticDenominator.two_not_dvd prim repr))
  have four : Nat.Coprime 4 d := odd.coprime_two_left.pow_left 2
  have same {p : ℕ} (hp : p.Prime) (pd : p∣d) : p∣a ↔ p∣b := by
    have total : p∣a^4+4*b^4 := repr ▸ dvd_mul_of_dvd_left (pd.trans (dvd_pow_self d (by decide : 4≠0))) n
    constructor
    · intro pa
      have prod := (Nat.dvd_add_iff_right (pa.trans (dvd_pow_self a (by decide : 4≠0)))).mpr total
      exact hp.dvd_of_dvd_pow ((hp.dvd_mul.mp prod).resolve_left (fun h =>
        (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p,hp,h,pd⟩) four))
    · intro pb
      exact hp.dvd_of_dvd_pow ((Nat.dvd_add_iff_left
        (dvd_mul_of_dvd_right (pb.trans (dvd_pow_self b (by decide : 4≠0))) 4)).mpr total)
  refine ⟨odd,?_,?_⟩
  · by_contra bad
    obtain ⟨p,hp,pa,pd⟩ := Nat.Prime.not_coprime_iff_dvd.mp bad
    exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p,hp,pa,(same hp pd).mp pa⟩) prim
  · by_contra bad
    obtain ⟨p,hp,pb,pd⟩ := Nat.Prime.not_coprime_iff_dvd.mp bad
    exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p,hp,(same hp pd).mpr pb,pb⟩) prim

private theorem zero_of_repr {n a b d : ℕ} (repr : d^4*n=a^4+4*b^4) :
    a^4+4*b^4 ≡ 0 [MOD d^4] :=
  Nat.modEq_zero_iff_dvd.mpr ⟨n,repr.symm⟩

/-- Two products at the same denominator sharing b and a modulo d also
share the entire residue of a modulo d^4. -/
theorem same_b {d n m a c b : ℕ} (prim : c.Coprime b)
    (first : d^4*n=a^4+4*b^4) (second : d^4*m=c^4+4*b^4)
    (same : a ≡ c [MOD d]) : a ≡ c [MOD d^4] := by
  obtain ⟨odd,unit,_⟩ := primitive_units prim second
  exact fourth_unique odd unit same (Nat.ModEq.add_right_cancel' (4*b^4)
    ((zero_of_repr first).trans (zero_of_repr second).symm))

/-- The same conclusion holds for b when the two products share a. -/
theorem same_a {d n m a b c : ℕ} (prim : a.Coprime c)
    (first : d^4*n=a^4+4*b^4) (second : d^4*m=a^4+4*c^4)
    (same : b ≡ c [MOD d]) : b ≡ c [MOD d^4] := by
  obtain ⟨odd,_,unit⟩ := primitive_units prim second
  exact scaled_fourth_unique odd unit same (Nat.ModEq.add_left_cancel' (a^4)
    ((zero_of_repr first).trans (zero_of_repr second).symm))

/-- All unit coordinates in one full period satisfying the affine fourth-power congruence. -/
noncomputable def roots (d e coeff offset target : ℕ) : Finset ℕ :=
  (Finset.range (d^e)).filter (fun z => z.Coprime d ∧ offset+coeff*z^4 ≡ target [MOD d^e])

/-- Reduction modulo d distinguishes every accepted coordinate in one period. -/
theorem roots_injOn {d e coeff offset target : ℕ} (odd : Odd d) (cop : coeff.Coprime d) :
    Set.InjOn (fun z => z%d) (roots d e coeff offset target : Set ℕ) := by
  intro z hz w hw same
  obtain ⟨zi,_,zh⟩ := Finset.mem_filter.mp (show z∈roots d e coeff offset target from hz)
  obtain ⟨wi,unit,wh⟩ := Finset.mem_filter.mp (show w∈roots d e coeff offset target from hw)
  have scaled := Nat.ModEq.add_left_cancel' offset (zh.trans wh.symm)
  exact (fourth_unique odd unit same (Nat.ModEq.cancel_left_of_coprime (cop.symm.pow_left e) scaled)
    ).eq_of_lt_of_lt (Finset.mem_range.mp zi) (Finset.mem_range.mp wi)

/-- For a fixed short coordinate the other one has at most d residue choices,
both when its fourth power has coefficient one and when the coefficient is four. -/
theorem card_roots {d e coeff offset target : ℕ} (odd : Odd d) (cop : coeff.Coprime d) :
    (roots d e coeff offset target).card≤d := by
  simpa only [Finset.card_range] using Finset.card_le_card_of_injOn
    (t:=Finset.range d) (fun z : ℕ => z%d)
    (fun z _ => Finset.mem_range.mpr (Nat.mod_lt z odd.pos))
    (roots_injOn (e:=e) (offset:=offset) (target:=target) odd cop)

end PrimeFactors.QuarticUnitLift
