import PrimeFactors.ThreeSquareCone

/-! Counts of triples on the zero cone modulo a product of two distinct odd
primes. A primitive triple has no prime factor of the modulus dividing all
three coordinates. These are finite ring counts, distinct from the sphere of
an integer radius. -/
namespace PrimeFactors.SemiprimeThreeSquareCone

open Finset ThreeSquareCone

abbrev Triple (m : ℕ) := ZMod m × ZMod m × ZMod m

/-- Primitivity in terms of the modulus and the canonical coordinates only. -/
def Primitive (m : ℕ) (v : Triple m) : Prop :=
  m.Coprime ((v.1.val.gcd v.2.1.val).gcd v.2.2.val)

noncomputable def primitivePoints (m : ℕ) [NeZero m] : Finset (Triple m) := by
  classical exact (points (ZMod m) 0).filter (Primitive m)

/-- Apply the ring CRT to each of the three coordinates and group them
by the two component rings. -/
noncomputable def split {p q : ℕ} (cop : p.Coprime q) :
    Triple (p*q) ≃ Triple p × Triple q := by
  let e := ZMod.chineseRemainder cop
  exact {
    toFun := fun v =>
      (((e v.1).1,(e v.2.1).1,(e v.2.2).1),((e v.1).2,(e v.2.1).2,(e v.2.2).2))
    invFun := fun w =>
      (e.symm (w.1.1,w.2.1),e.symm (w.1.2.1,w.2.2.1),e.symm (w.1.2.2,w.2.2.2))
    left_inv := by intro v; simp
    right_inv := by intro w; simp }

/-- The cone polynomial commutes with the CRT in both components. -/
theorem splits {p q : ℕ} [NeZero p] [NeZero q] (cop : p.Coprime q) (v : Triple (p*q)) :
    v∈points (ZMod (p*q)) 0 ↔
    (split cop v).1∈points (ZMod p) 0 ∧ (split cop v).2∈points (ZMod q) 0 := by
  simp only [mem_points,split,Equiv.coe_fn_mk]
  let e := ZMod.chineseRemainder cop
  rw [←e.injective.eq_iff,map_add,map_add,map_pow,map_pow,map_pow,map_zero,Prod.ext_iff]
  rfl

private theorem projections {p q : ℕ} [NeZero p] [NeZero q] (cop : p.Coprime q)
    (x : ZMod (p*q)) : ZMod.chineseRemainder cop x=((x.val:ZMod p),(x.val:ZMod q)) := by
  simpa only [ZMod.natCast_zmod_val] using map_natCast (ZMod.chineseRemainder cop) x.val

/-- The gcd condition is equivalent to avoiding the origin at both primes,
including for triples with a zero coordinate. -/
theorem primitive_iff {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (v : Triple (p*q)) :
    Primitive (p*q) v ↔ (split cop v).1≠(0,0,0) ∧ (split cop v).2≠(0,0,0) := by
  have vanish (r x y z : ℕ) :
      ((x : ZMod r),(y : ZMod r),(z : ZMod r))=(0,0,0) ↔ r∣x ∧ r∣y ∧ r∣z := by
    constructor
    · intro h
      exact ⟨(ZMod.natCast_zmod_eq_zero_iff_dvd x r).mp (congrArg Prod.fst h),
        (ZMod.natCast_zmod_eq_zero_iff_dvd y r).mp (congrArg (fun a : Triple r => a.2.1) h),
        (ZMod.natCast_zmod_eq_zero_iff_dvd z r).mp (congrArg (fun a : Triple r => a.2.2) h)⟩
    · rintro ⟨hx,hy,hz⟩
      exact Prod.ext ((ZMod.natCast_zmod_eq_zero_iff_dvd x r).mpr hx)
        (Prod.ext ((ZMod.natCast_zmod_eq_zero_iff_dvd y r).mpr hy)
          ((ZMod.natCast_zmod_eq_zero_iff_dvd z r).mpr hz))
  have pp := (Fact.out : p.Prime)
  have qp := (Fact.out : q.Prime)
  simp only [Primitive,Nat.coprime_mul_iff_left,pp.coprime_iff_not_dvd,qp.coprime_iff_not_dvd,
    Nat.dvd_gcd_iff,split,Equiv.coe_fn_mk,projections cop,Prod.mk.injEq,
    ZMod.natCast_zmod_eq_zero_iff_dvd]
  simp only [ne_eq,vanish]
  tauto

/-- Cardinality transfer for any finite condition that splits into its two
local components under the triple CRT. -/
private theorem count_product {p q : ℕ} [NeZero p] [NeZero q] (cop : p.Coprime q)
    (S : Finset (Triple (p*q))) (A : Finset (Triple p)) (B : Finset (Triple q))
    (mem : ∀ v, v∈S ↔ (split cop v).1∈A ∧ (split cop v).2∈B) :
    S.card=A.card*B.card := by
  classical
  have eq : S.map (split cop).toEmbedding=A×ˢB := by
    ext w
    obtain ⟨v,rfl⟩ := (split cop).surjective w
    simpa only [mem_map_equiv,Equiv.symm_apply_apply,mem_product] using mem v
  simpa using congrArg Finset.card eq

/-- The total cone count multiplies across any two coprime positive moduli. -/
theorem total_mul {m n : ℕ} [NeZero m] [NeZero n] (cop : m.Coprime n) :
    (points (ZMod (m*n)) 0).card =
      (points (ZMod m) 0).card * (points (ZMod n) 0).card :=
  count_product cop _ _ _ (splits cop)

/-- All ordered triples on the cone, including the origin. -/
theorem total {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (ne : p≠q)
    (op : p≠2) (oq : q≠2) : (points (ZMod (p*q)) 0).card=(p*q)^2 := by
  have co := (Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : q.Prime)).mpr ne
  rw [total_mul co,prime_zero p op,prime_zero q oq,mul_pow]

/-- Precisely the two nonzero local cone components survive the primitivity
condition on the ordered modular triples. -/
theorem primitive_card {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (ne : p≠q)
    (op : p≠2) (oq : q≠2) : (primitivePoints (p*q)).card=(p^2-1)*(q^2-1) := by
  classical
  have co := (Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : q.Prime)).mpr ne
  have mem (v : Triple (p*q)) : v∈primitivePoints (p*q) ↔
      (split co v).1∈(points (ZMod p) 0).erase (0,0,0) ∧
      (split co v).2∈(points (ZMod q) 0).erase (0,0,0) := by
    rw [primitivePoints,mem_filter,splits,primitive_iff]
    simp only [mem_erase]
    tauto
  rw [count_product co _ _ _ mem,prime_nonzero_points p op,prime_nonzero_points q oq]

/-- Subtracting the externally supplied primitive count from the public
square leaves the exact square of the factor sum. -/
theorem sum_square {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (ne : p≠q)
    (op : p≠2) (oq : q≠2) :
    (p*q+1)^2-(primitivePoints (p*q)).card=(p+q)^2 := by
  rw [primitive_card ne op oq]
  have hp : 1≤p^2 := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have hq : 1≤q^2 := Nat.one_le_pow _ _ (Fact.out : q.Prime).pos
  apply Nat.sub_eq_of_eq_add
  zify [hp,hq]
  ring

end PrimeFactors.SemiprimeThreeSquareCone
