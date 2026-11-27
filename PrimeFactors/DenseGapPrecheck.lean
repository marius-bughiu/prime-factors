import PrimeFactors.WeightedOffGap
import PrimeFactors.ReducedSmoothReadout

/-! What a complete interval of right-entry prechecks proves about local
periods. A finite sparse menu also has a public duplicate-removal rule. -/
namespace PrimeFactors.DenseGapPrecheck
open WeightedOffGap TraceFoldedRight

/-- A missed precheck gives the same divisibility answer at the two primes. -/
def AgreesOn (a b : ℕ) (gaps : Finset ℕ) := ∀ e ∈ gaps, a ∣ e ↔ b ∣ e

/-- Testing every positive index up to D either encounters a split, leaves
both coprime periods larger than D, or finds both periods trivial. -/
theorem dense {a b D : ℕ} (ap : 0<a) (bp : 0<b) (cop : a.Coprime b)
    (agrees : AgreesOn a b (Finset.Icc 1 D)) :
    (a=1 ∧ b=1) ∨ (D<a ∧ D<b) := by
  have eq_of_small (aa : a≤D) (bb : b≤D) : a=1 ∧ b=1 := by
    have h := (agrees a (Finset.mem_Icc.mpr ⟨ap,aa⟩)).mp (dvd_refl a)
    have k := (agrees b (Finset.mem_Icc.mpr ⟨bp,bb⟩)).mpr (dvd_refl b)
    have same := Nat.dvd_antisymm k h
    have one := cop.eq_one_of_dvd k
    exact ⟨one,same ▸ one⟩
  by_cases aa : a≤D
  · have h := (agrees a (Finset.mem_Icc.mpr ⟨ap,aa⟩)).mp (dvd_refl a)
    exact Or.inl (eq_of_small aa ((Nat.le_of_dvd ap h).trans aa))
  by_cases bb : b≤D
  · have k := (agrees b (Finset.mem_Icc.mpr ⟨bp,bb⟩)).mpr (dvd_refl b)
    exact Or.inl (eq_of_small ((Nat.le_of_dvd bp k).trans bb) bb)
  exact Or.inr ⟨by omega,by omega⟩

/-- The signed gap search uses the half-predecessor period L. A dense setup
with no split and at least one nontrivial reduced period forces L>2D. -/
theorem period_minimum {a b D L : ℕ} (ap : 0<a) (bp : 0<b) (cp : a.Coprime b)
    (agree : AgreesOn a b (Finset.Icc 1 D)) (live : a≠1 ∨ b≠1)
    (lp : 0<L) (joint : a*b∣L) : (D+1)^2≤L ∧ 2*D<L := by
  rcases dense ap bp cp agree with dead|large
  · tauto
  have v := Nat.mul_le_mul large.1 large.2
  have mult := Nat.le_of_dvd lp joint
  rw [←pow_two] at v
  exact ⟨v.trans mult,by nlinarith only [v,mult,Nat.zero_le (D^2)]⟩

private theorem no_split_same_zero {N : ℕ} [NeZero N] {F K : Type*} [Field F] [Field K]
    (E : ZMod N ≃+* F × K) (z : ZMod N) (miss : z.val.gcd N=1 ∨ z.val.gcd N=N) :
    (E z).1=0 ↔ (E z).2=0 := by
  rcases miss with cop|whole
  · have unit : IsUnit z := (ZMod.natCast_zmod_val z) ▸ (ZMod.isUnit_iff_coprime z.val N).mpr cop
    have p := (unit.map ((RingHom.fst F K).comp E.toRingHom)).ne_zero
    have q := (unit.map ((RingHom.snd F K).comp E.toRingHom)).ne_zero
    exact ⟨fun h => (p h).elim,fun h => (q h).elim⟩
  · have zero := (ZMod.val_eq_zero z).mp
      (Nat.eq_zero_of_dvd_of_lt (Nat.gcd_eq_right_iff_dvd.mp whole) (ZMod.val_lt z))
    simp [zero]

private theorem at_field {N : ℕ} {F : Type*} [Field F] (f : ZMod N →+* F) (v : (ZMod N)ˣ) (e : ℕ) :
    orderOf ((Units.map f.toMonoidHom v)^2)∣e ↔ f ((v:ZMod N)^(2*e)-1)=0 := by
  rw [orderOf_dvd_iff_pow_eq_one,←pow_mul,map_sub,map_pow,map_one,sub_eq_zero,Units.ext_iff]
  rfl

/-- This hypothesis is directly supplied by the two possible trivial gcd
outputs on the actual public prechecks. It applies to an arbitrary menu. -/
theorem from_gcd {N : ℕ} [NeZero N] {F K : Type*} [Field F] [Field K]
    (E : ZMod N ≃+* F × K) (v : (ZMod N)ˣ) (gaps : Finset ℕ)
    (miss : ∀ e ∈ gaps, let g := (((v:ZMod N)^(2*e)-1).val.gcd N); g=1 ∨ g=N) :
    AgreesOn (orderOf ((coords E v).1^2)) (orderOf ((coords E v).2^2)) gaps := by
  intro e inside
  have p := at_field ((RingHom.fst F K).comp E.toRingHom) v e
  have q := at_field ((RingHom.snd F K).comp E.toRingHom) v e
  exact p.trans ((no_split_same_zero E _ (miss e inside)).trans q.symm)

private theorem twist_invol {G H : Type*} [Group G] [Group H] (y : G × H) :
    twist (twist y)=y := by ext <;> simp [twist]

private theorem twist_inv {G H : Type*} [Group G] [Group H] (y : G × H) :
    twist y⁻¹=(twist y)⁻¹ := by ext <;> simp [twist]

/-- A public sparse substitute: any two clean useful entries for the same
left coordinate are the identical unit or its global inverse. -/
theorem same_or_inverse {G H : Type*} [Group G] [Group H] {x y z : G × H}
    (hy : Mixed x y) (hz : Mixed x z) : y=z ∨ y=z⁻¹ := by
  have inj : Function.Injective (twist (G:=G) (H:=H)) :=
    Function.LeftInverse.injective twist_invol
  rcases hy with a|a <;> rcases hz with b|b
  · exact Or.inl (inj (a.symm.trans b))
  · exact Or.inr (inj ((a.symm.trans b).trans (twist_inv z).symm))
  · have eq := congrArg Inv.inv (a.symm.trans b)
    exact Or.inr (inj ((by simpa using eq : twist y=(twist z)⁻¹).trans (twist_inv z).symm))
  · exact Or.inl (inj (inv_inj.mp (a.symm.trans b)))

/-- The sparse rule at actual public units, with the gcd extraction included. -/
theorem sparse {N : ℕ} [NeZero N] {F K : Type*} [Field F] [Field K]
    (E : ZMod N ≃+* F × K) (x y z : (ZMod N)ˣ)
    (cy : IsUnit ((y:ZMod N)^2-1)) (cz : IsUnit ((z:ZMod N)^2-1))
    (hy : trace 1 x=trace 1 y ∧ 1<((x:ZMod N)-(y:ZMod N)).val.gcd N ∧
      ((x:ZMod N)-(y:ZMod N)).val.gcd N<N)
    (hz : trace 1 x=trace 1 z ∧ 1<((x:ZMod N)-(z:ZMod N)).val.gcd N ∧
      ((x:ZMod N)-(z:ZMod N)).val.gcd N<N) : y=z ∨ y=z⁻¹ := by
  rcases same_or_inverse ((observe E x y cy).mp hy) ((observe E x z cz).mp hz) with a|b
  · exact Or.inl ((coords E).injective a)
  · rw [←map_inv] at b
    exact Or.inr ((coords E).injective b)

/-- On inserting a duplicate right *trace*, either its global inversion
orbit was already stored or setup itself obtains a proper divisor. -/
theorem right_collision {N : ℕ} [NeZero N] (y z : (ZMod N)ˣ) (matchKey : trace 1 y=trace 1 z) :
    y=z ∨ y=z⁻¹ ∨
    (1<((y:ZMod N)-(z:ZMod N)).val.gcd N ∧ ((y:ZMod N)-(z:ZMod N)).val.gcd N<N) := by
  simpa only [mul_eq_one_iff_eq_inv] using classify 1 y z matchKey

/-- Compose the tested divisibilities with the predecessor coprimality and
joint-order theorem. If any reduced period survives, fixed coordinates have
at most one positive useful gap throughout the dense menu. -/
theorem semiprime {p q h D : ℕ} (hp : p.Prime) (hq : q.Prime) (odd : p*q=2*h+1)
    (x : (ZMod p)ˣ) (y : (ZMod q)ˣ)
    (agrees : AgreesOn (orderOf (x^(p*q-1))) (orderOf (y^(p*q-1))) (Finset.Icc 1 D)) :
    let v := (x,y)^h
    (orderOf (x^(p*q-1))=1 ∧ orderOf (y^(p*q-1))=1) ∨
    ((D+1)^2≤orderOf v ∧ ∀ z e f, 0<e → e≤D → f≤D →
      Mixed z (v^e) → Mixed z (v^f) → f=e) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero q := ⟨hq.ne_zero⟩
  dsimp only
  by_cases dead : orderOf (x^(p*q-1))=1 ∧ orderOf (y^(p*q-1))=1
  · exact Or.inl dead
  have live : orderOf (x^(p*q-1))≠1 ∨ orderOf (y^(p*q-1))≠1 := by tauto
  have h := period_minimum (orderOf_pos _) (orderOf_pos _) (reduced_periods_coprime hp hq x y)
    agrees live (orderOf_pos ((x,y)^h)) (reduced_period hp hq odd x y)
  exact Or.inr ⟨h.1, fun z _ _ ep ed fd a b => short_unique z _ ep ed fd h.2 a b⟩

/-- Either the duplicate right key factors N, or the previously stored
representative produces a proper divisor at every clean successful left hit. -/
theorem representative {N : ℕ} [NeZero N] {F K : Type*} [Field F] [Field K]
    (E : ZMod N ≃+* F × K) (x y z : (ZMod N)ˣ) (cy : IsUnit ((y:ZMod N)^2-1))
    (hit : trace 1 x=trace 1 y ∧ 1<((x:ZMod N)-(y:ZMod N)).val.gcd N ∧
      ((x:ZMod N)-(y:ZMod N)).val.gcd N<N) (keys : trace 1 y=trace 1 z) :
    (1<((y:ZMod N)-(z:ZMod N)).val.gcd N ∧ ((y:ZMod N)-(z:ZMod N)).val.gcd N<N) ∨
    (trace 1 x=trace 1 z ∧ 1<((x:ZMod N)-(z:ZMod N)).val.gcd N ∧
      ((x:ZMod N)-(z:ZMod N)).val.gcd N<N) := by
  rcases right_collision y z keys with eq|inv|factor
  · exact Or.inr (eq ▸ hit)
  · right
    have cz := (clear_trace z).mpr (keys ▸ (clear_trace y).mp cy)
    apply (observe E x z cz).mpr
    have mixed := (observe E x y cy).mp hit
    rw [inv,map_inv] at mixed
    simpa only [Mixed,twist_inv,inv_inv,or_comm] using mixed
  · exact Or.inl factor

private theorem map_readout {G H : Type*} [Monoid G] [Monoid H] [DecidableEq G] [DecidableEq H]
    (f : G ≃* H) (u : G) (blocks : List ℕ) :
    f (ReducedSmoothReadout.readout u blocks)=ReducedSmoothReadout.readout (f u) blocks := by
  induction blocks generalizing u with
  | nil => rfl
  | cons m ms ih =>
    simp only [ReducedSmoothReadout.readout,←map_pow,←map_one f,f.injective.eq_iff]
    split_ifs <;> simp_all

/-- A sparse alternative to D dense gcds. Start with the nonidentity
reduced base u (the product-predecessor power) and run the existing public
prime-power readout through D. A single final gcd of one certifies that both
orders exceed D. The scheduled exponent still has to be applied. -/
theorem single_gcd {N : ℕ} [NeZero N] {F K : Type*} [Field F] [Field K] [Finite F] [Finite K]
    (E : ZMod N ≃+* F × K) (u : (ZMod N)ˣ) (D : ℕ) (active : u≠1)
    (cop : (orderOf (coords E u).1).Coprime (orderOf (coords E u).2))
    (miss : let w := ReducedSmoothReadout.readout u (ReducedSmoothReadout.schedule D D)
            ((w:ZMod N)-1).val.gcd N=1) :
    D<orderOf (coords E u).1 ∧ D<orderOf (coords E u).2 := by
  classical
  let blocks := ReducedSmoothReadout.schedule D D
  let w := ReducedSmoothReadout.readout u blocks
  have small (r : ℕ) (rp : 0<r) (rd : r≤D) : r∣blocks.prod :=
    ReducedSmoothReadout.smooth_dvd_schedule rp rd (fun _ _ h => (Nat.le_of_dvd rp h).trans rd)
  have active' : coords E u≠1 := by
    intro eq
    apply active
    apply (coords E).injective
    simpa using eq
  have notSeparated : ¬ReducedSmoothReadout.separated (coords E w) := by
    have eq := no_split_same_zero E ((w:ZMod N)-1) (Or.inl miss)
    rw [map_sub,map_one] at eq
    change (E (w:ZMod N)).1-1=0 ↔ (E (w:ZMod N)).2-1=0 at eq
    simp only [sub_eq_zero] at eq
    have ids : (coords E w).1=1 ↔ (coords E w).2=1 := by
      rw [Units.ext_iff,Units.ext_iff]
      exact eq
    rintro (⟨l,r⟩|⟨l,r⟩)
    · exact r (ids.mp l)
    · exact l (ids.mpr r)
  rw [show coords E w=ReducedSmoothReadout.readout (coords E u) blocks from map_readout ..]
    at notSeparated
  have exclude := fun h => notSeparated (ReducedSmoothReadout.readout_separates blocks
    (ReducedSmoothReadout.schedule_powers D D) _ _ cop active' h)
  constructor
  · by_contra! bad
    exact exclude (Or.inl (small _ (orderOf_pos _) bad))
  · by_contra! bad
    exact exclude (Or.inr (small _ (orderOf_pos _) bad))

end PrimeFactors.DenseGapPrecheck
