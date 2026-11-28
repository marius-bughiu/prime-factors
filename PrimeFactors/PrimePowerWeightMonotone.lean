import PrimeFactors.PrimePowerPairWeight
import PrimeFactors.CoprimeGuessTables

/-! An attained sum at higher prime-power precision has at least as many
ordered representations as its projection onto the first two digits. -/

namespace PrimeFactors.PrimePowerWeightMonotone

open PrimeSquareSumWeights PrimePowerPairWeight CoprimeGuessTables
open scoped Classical

variable {p e n : ℕ} [Fact p.Prime]

noncomputable def reduce (depth : 2≤e) : ZMod (p^e) →+* ZMod (p^2) :=
  ZMod.castHom (pow_dvd_pow p depth) _

omit [Fact p.Prime] in
theorem reduce_label (depth : 2≤e) (s : Labels (p^e) n) :
    AdmissibleSum (n : ZMod (p^2)) (reduce depth s.val) := by
  obtain ⟨x,y,prod,sum⟩ := s.property
  refine ⟨reduce depth x,reduce depth y,?_,?_⟩
  · rw [←map_mul,prod,map_natCast]
  · rw [←map_add,sum]

/-- The two-digit local multiplicity never exceeds that of an attained
lift. A singular two-digit sum forces the factor difference to vanish
modulo p and hence forces at least p representations at every depth. -/
theorem weight_lift (odd : p≠2) (depth : 2≤e) (s : Labels (p^e) n) :
    weight n (reduce depth s.val)≤weight n s.val := by
  have pass := reduce_label depth s
  obtain ⟨x,y,prod,sum⟩ := s.property
  let f := reduce (p:=p) depth
  let d := (x-y).val
  let t := cappedOrder p e d
  have form : weight n s.val=if 2*t<e then 2*p^t else p^(e/2) := by
    rw [←sum]
    exact weight_of_pair odd prod
  have pp := (Fact.out : p.Prime)
  have deep : p≤p^(e/2) := by
    simpa only [pow_one] using Nat.pow_le_pow_right pp.pos (by omega : 1≤e/2)
  have base : 2≤weight n s.val := by
    rw [form]
    split_ifs
    · have := pow_pos pp.pos t
      omega
    · exact pp.two_le.trans deep
  rw [weight_formula odd,if_pos pass]
  split_ifs with z
  · have proj : f ((x-y)^2)=0 := by
      change f ((x-y)^2)=0
      rw [show (x-y)^2=(x+y)^2-4*(x*y) by ring,sum,prod,map_sub,map_pow,map_mul,map_ofNat,map_natCast]
      exact z
    have divides : p^2∣d^2 := by
      apply (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp
      change ((d^2:ℕ):ZMod (p^2))=0
      rw [←map_natCast f (d^2),Nat.cast_pow,show ((d:ℕ):ZMod (p^e))=x-y from ZMod.natCast_zmod_val _]
      exact proj
    have hit : p∣d := (Nat.pow_dvd_pow_iff (by decide : 2≠0)).mp divides
    have tp : 1≤t := by
      unfold t cappedOrder
      split_ifs with zero
      · omega
      · have fact := (pp.pow_dvd_iff_le_factorization zero).mp (by simpa only [pow_one] using hit : p^1∣d)
        omega
    rw [form]
    split_ifs
    · have power : p≤p^t := by simpa only [pow_one] using Nat.pow_le_pow_right pp.pos tp
      omega
    · exact deep
  · exact base

end PrimeFactors.PrimePowerWeightMonotone
