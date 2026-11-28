import PrimeFactors.SemiprimeThreeSquareCone

/-! Ordered three-square representations at an arbitrary modular target.
For a unit target the public Jacobi symbol determines the center of the
two possible signed counts. -/
namespace PrimeFactors.ConeUnitTarget

open ThreeSquareCone SemiprimeThreeSquareCone
open private PrimeFactors.SemiprimeThreeSquareCone.count_product from PrimeFactors.SemiprimeThreeSquareCone

/-- CRT applies to every target, including nonunits and zero. -/
theorem total_mul {m n : ℕ} [NeZero m] [NeZero n] (cop : m.Coprime n) (t : ZMod (m*n)) :
    (points (ZMod (m*n)) t).card =
      (points (ZMod m) (ZMod.chineseRemainder cop t).1).card *
      (points (ZMod n) (ZMod.chineseRemainder cop t).2).card := by
  apply PrimeFactors.SemiprimeThreeSquareCone.count_product cop
  intro v
  simp only [mem_points,SemiprimeThreeSquareCone.split,Equiv.coe_fn_mk]
  let e := ZMod.chineseRemainder cop
  rw [←e.injective.eq_iff,map_add,map_add,map_pow,map_pow,map_pow,Prod.ext_iff]
  rfl

/-- An integer target reduces to that same integer in both local rings. -/
theorem total_mul_int {m n : ℕ} [NeZero m] [NeZero n] (cop : m.Coprime n) (t : ℤ) :
    (points (ZMod (m*n)) t).card=(points (ZMod m) t).card*(points (ZMod n) t).card := by
  rw [total_mul cop,map_intCast]
  rfl

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime]

/-- The local characters at −t give the complete count at pq. The formula
also includes targets that vanish at one or both primes. -/
theorem character_count (ne : p≠q) (op : p≠2) (oq : q≠2) (t : ℤ) :
    ((points (ZMod (p*q)) t).card:ℤ) =
      (p*q:ℤ)*(p+quadraticChar (ZMod p) (-t:ℤ))*(q+quadraticChar (ZMod q) (-t:ℤ)) := by
  have co := (Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : q.Prime)).mpr ne
  rw [total_mul_int co,Nat.cast_mul,field_count _ (by rwa [ZMod.ringChar_zmod_n]),
    field_count _ (by rwa [ZMod.ringChar_zmod_n])]
  simp only [ZMod.card,Int.cast_neg]
  ring

/-- At target −1 the two local character values both equal one. -/
theorem negative_one (ne : p≠q) (op : p≠2) (oq : q≠2) :
    (points (ZMod (p*q)) (-1)).card=(p*q)*(p+1)*(q+1) := by
  have count := character_count ne op oq (-1)
  norm_num at count
  exact_mod_cast count

/-- The center uses only the target, modulus and Jacobi symbol.
The two individual character signs give the signed deviation. -/
theorem centered (ne : p≠q) (op : p≠2) (oq : q≠2) (t : ℤ) :
    ((points (ZMod (p*q)) t).card:ℤ)-(p*q:ℤ)*(p*q+jacobiSym (-t) (p*q)) =
      (p*q:ℤ)*(q*quadraticChar (ZMod p) (-t:ℤ)+p*quadraticChar (ZMod q) (-t:ℤ)) := by
  rw [character_count ne op oq,ExtensionTrace.jacobi_crt]
  ring

private theorem sign_cases (r : ℕ) [Fact r.Prime] (t : ℤ) (cop : t.natAbs.Coprime r) :
    quadraticChar (ZMod r) (-t:ℤ)=1 ∨ quadraticChar (ZMod r) (-t:ℤ)= -1 := by
  have gcd : (-t).gcd (r:ℤ)=1 := by simpa only [Int.gcd,Int.natAbs_neg,Int.natAbs_natCast] using cop
  have cases' := jacobiSym.eq_one_or_neg_one gcd
  rw [←jacobiSym.legendreSym.to_jacobiSym] at cases'
  exact cases'

/-- For a unit target and sorted primes the absolute displacement is the
modulus times the sum when the public Jacobi sign is positive, and the
modulus times the gap when it is negative. -/
theorem abs_excess (lt : p<q) (op : p≠2) (oq : q≠2) (t : ℤ) (unit : t.natAbs.Coprime (p*q)) :
    |((points (ZMod (p*q)) t).card:ℤ)-(p*q:ℤ)*(p*q+jacobiSym (-t) (p*q))| =
      (p*q:ℤ)*(if jacobiSym (-t) (p*q)=1 then (p:ℤ)+q else (q:ℤ)-p) := by
  have cp := sign_cases p t (unit.of_dvd_right (dvd_mul_right p q))
  have cq := sign_cases q t (unit.of_dvd_right (dvd_mul_left q p))
  rw [centered lt.ne op oq,abs_mul,abs_of_nonneg (show (0:ℤ)≤p*q by positivity),
    ExtensionTrace.jacobi_crt]
  congr 1
  have diff : (p:ℤ)<q := by exact_mod_cast lt
  rcases cp with hp|hp <;> rcases cq with hq|hq <;>
    rw [hp,hq] <;> norm_num <;>
    first | (rw [abs_of_nonneg (by omega)]; omega) | (rw [abs_of_nonpos (by omega)]; omega)

end PrimeFactors.ConeUnitTarget
