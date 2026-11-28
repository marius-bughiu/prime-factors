import PrimeFactors.FiveSquareSignRanks
import Mathlib.Algebra.Group.Pi.Units

/-! Count square/nonsquare patterns of unit product residues at five fixed
prime squares. Every count is over a complete local or global residue space. -/
namespace PrimeFactors.FiveSquareSignPopulation

open Finset
open FiveSquareGuessRanks (primes)
open FiveSquareSignRanks (Pattern sign)
open private PrimeFactors.CoprimeGuessTables.coprime from PrimeFactors.CoprimeGuessTables

noncomputable abbrev m := CoprimeGuessTables.modulus primes

private def flag (p n : ℕ) : Bool := (List.range p).any (fun x => x*x%p == n%p)

private theorem flag_true {p : ℕ} [NeZero p] (n : ℕ) : flag p n = true ↔ IsSquare (n:ZMod p) := by
  simp only [flag,List.any_eq_true,List.mem_range,beq_iff_eq,isSquare_iff_exists_sq]
  constructor
  · rintro ⟨r,_,eq⟩
    refine ⟨r,?_⟩
    rw [sq,←Nat.cast_mul]
    exact (ZMod.natCast_eq_natCast_iff' n (r*r) p).mpr eq.symm
  · rintro ⟨r,h⟩
    refine ⟨r.val,r.val_lt,?_⟩
    apply (ZMod.natCast_eq_natCast_iff' (r.val*r.val) n p).mp
    simpa only [Nat.cast_mul,ZMod.natCast_zmod_val,pow_two] using h.symm

private def localCells (p : ℕ) [NeZero (p^2)] (b : Bool) := (univ : Finset (ZMod (p^2))).filter
  (fun z => z.val.Coprime (p^2) ∧ flag p z.val=b)

private def half : Fin 5 → ℕ := ![10,21,55,78,136]

private theorem local_tables : ∀ i : Fin 5, ∀ b : Bool, (localCells (primes i) b).card=half i := by
  decide +kernel

private abbrev U (i : Fin 5) := (ZMod ((primes i)^2))ˣ
private def localFlag (i : Fin 5) (u : U i) := flag (primes i) (u.val.val)

private theorem local_card (i : Fin 5) (b : Bool) :
    Nat.card {u : U i // localFlag i u=b}=half i := by
  let P := primes i
  let e := ZMod.unitsEquivCoprime (n:=P^2)
  let eq : {u : U i // localFlag i u=b} ≃ ↥(localCells P b) := {
    toFun := fun u => ⟨(e u.val).val,mem_filter.mpr ⟨mem_univ _,(e u.val).property,u.property⟩⟩
    invFun := fun z =>
      let v := mem_filter.mp z.property
      let u := e.symm ⟨z.val,v.2.1⟩
      ⟨u, by
        have same : (e u).val=z.val := congrArg Subtype.val (e.apply_symm_apply _)
        change flag P (e u).val.val=b
        rw [same]
        exact v.2.2⟩
    left_inv := fun u => Subtype.ext (e.symm_apply_apply u.val)
    right_inv := by
      intro z
      let w : {x : ZMod (P^2) // x.val.Coprime (P^2)} := ⟨z.val,(mem_filter.mp z.property).2.1⟩
      have same : (e (e.symm w)).val=z.val := congrArg Subtype.val (e.apply_symm_apply w)
      exact Subtype.ext same }
  exact (Nat.card_congr eq).trans ((Nat.card_eq_finsetCard _).trans (local_tables i b))

private noncomputable def ringEquiv : ZMod m ≃+* (∀ i : Fin 5, ZMod ((primes i)^2)) :=
  ZMod.prodEquivPi (fun i => (primes i)^2)
    (PrimeFactors.CoprimeGuessTables.coprime primes (by decide +kernel))

private noncomputable def unitsEquiv : (ZMod m)ˣ ≃ (∀ i : Fin 5, U i) :=
  ((Units.mapEquiv ringEquiv.toMulEquiv).trans MulEquiv.piUnits).toEquiv

private theorem agree (u : (ZMod m)ˣ) (i : Fin 5) :
    sign u.val.val i = localFlag i (unitsEquiv u i) := by
  classical
  have rep : (unitsEquiv u i).val=(u.val.val:ZMod ((primes i)^2)) := by
    change ringEquiv u.val i=_
    nth_rw 1 [← ZMod.natCast_zmod_val u.val]
    exact congrFun (map_natCast ringEquiv u.val.val) i
  unfold localFlag
  rw [rep,ZMod.val_natCast]
  have dv : primes i ∣ (primes i)^2 := by rw [pow_two]; exact Nat.dvd_mul_right ..
  unfold flag
  simp only [Nat.mod_mod_of_dvd u.val.val dv]
  change decide (IsSquare (u.val.val:ZMod (primes i)))=flag (primes i) u.val.val
  cases f : flag (primes i) u.val.val <;> simp only [decide_eq_false_iff_not,decide_eq_true_eq]
  · exact fun good => Bool.false_ne_true (f.symm.trans ((flag_true _).mpr good))
  · exact (flag_true _).mp f

/-- Every pattern of the five quadratic signs is attained by the same number
of unit product residues modulo 7,239,457,225. -/
theorem pattern_count (b : Pattern) :
    ((univ : Finset (ZMod m)ˣ).filter (fun u => sign u.val.val = b)).card=122522400 := by
  classical
  let e : {u : (ZMod m)ˣ // sign u.val.val=b} ≃ (∀ i, {x : U i // localFlag i x=b i}) :=
    (unitsEquiv.subtypeEquiv (fun u => by
      change sign u.val.val=b ↔ ∀ i, localFlag i (unitsEquiv u i)=b i
      rw [funext_iff]; simp_rw [agree])).trans Equiv.subtypePiEquivPi
  have counts := (Nat.card_congr e).trans Nat.card_pi
  simp_rw [local_card] at counts
  have product : ∏ i, half i=122522400 := by decide +kernel
  rw [product,Nat.card_eq_fintype_card,Fintype.card_subtype] at counts
  exact counts

/-- Any additive statistic depending only on the pattern can be summed over
32 patterns, without iterating over the global product residues. -/
theorem sum_by_pattern {α : Type*} [AddCommMonoid α] (f : Pattern → α) :
    (∑ u : (ZMod m)ˣ, f (sign u.val.val)) = 122522400 • (∑ b : Pattern, f b) := by
  classical
  have groups := sum_fiberwise_of_maps_to' (s:=(univ : Finset (ZMod m)ˣ))
    (t:=(univ : Finset Pattern)) (g:=fun u => sign u.val.val) (fun _ _ => mem_univ _) f
  simpa only [sum_const,pattern_count,←Finset.smul_sum] using groups.symm

private theorem size_from_sum {X Y : Type*} [Fintype X] [Fintype Y]
    (h : (∑ _ : X, (1 : ℕ)) = 122522400 • (∑ _ : Y, (1 : ℕ)))
    (hy : Fintype.card Y = 32) : Fintype.card X = 3920716800 := by
  simpa only [sum_const, card_univ, nsmul_eq_mul, Nat.cast_id, mul_one, hy, Nat.reduceMul] using h

private theorem normalize {k : ℕ} {a b : ℚ} (hk : k = 3920716800) (hab : a = 122522400 • b) :
    a / k = b / 32 := by
  rw [hk, hab, nsmul_eq_mul]
  push_cast
  ring

/-- Uniformly averaging over products therefore assigns probability 1/32 to
each pattern. The statistic may have a different mean for every pattern. -/
theorem mean_by_pattern (f : Pattern → ℚ) :
    (∑ u : (ZMod m)ˣ, f (sign u.val.val)) / Fintype.card (ZMod m)ˣ =
      (∑ b : Pattern, f b)/32 := by
  have n : Fintype.card Pattern = 32 := by simp [FiveSquareSignRanks.Pattern, Fintype.card_pi]
  have k := size_from_sum (X := (ZMod m)ˣ) (Y := Pattern) (sum_by_pattern (α := ℕ) (fun _ => 1)) n
  exact normalize k (sum_by_pattern f)

end PrimeFactors.FiveSquareSignPopulation
