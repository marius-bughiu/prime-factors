import PrimeFactors.TwelveCollisionBatch
import PrimeFactors.NormBatchGCD
import Mathlib.Tactic.ReduceModChar
import PrimeFactors.WeightedGlobalTrace

/-! Batch comparisons of geometric right powers with arbitrary left keys.
A full-modulus equality contributes no proper divisor. Removing it before a
batch is evaluated gives a useful converse for a saturated batch. -/
namespace PrimeFactors.LocalGapProducts
open Finset Polynomial

variable {R : Type*} [CommRing R] [DecidableEq R]

noncomputable def rootPoly (A : Finset R) : R[X] := ∏ x∈A, (X-C x)

/-- A shared exact key calls for a derivative, since its own difference is zero. -/
noncomputable def probe (A : Finset R) (y : R) : R :=
  if y ∈ A then (derivative (rootPoly A)).eval y else (rootPoly A).eval y

theorem probe_eq (A : Finset R) (y : R) : probe A y = ∏ x∈A.erase y, (y-x) := by
  by_cases h : y ∈ A
  · simpa [probe, h, rootPoly] using TwelveCollisionBatch.derivative_at_key h
  · simp [probe, h, rootPoly, Finset.erase_eq_of_not_mem h, Polynomial.eval_prod]

omit [DecidableEq R] in
/-- Both orientations are necessary when a folded weighted key agrees at
only one prime. Each orientation is a comparison of ordinary ring elements. -/
theorem signed_local {F : Type*} [Field F] (f : R →+* F) (x y : Rˣ) :
    TraceFoldedRight.trace 1 (Units.map f.toMonoidHom x) =
      TraceFoldedRight.trace 1 (Units.map f.toMonoidHom y) ↔
      f (x:R) = f (y:R) ∨ f (x:R) = f ((↑(y⁻¹)):R) := by
  rw [TraceFoldedRight.field_match, mul_eq_one_iff_eq_inv,
    ← map_inv (Units.map f.toMonoidHom)]
  exact or_congr Units.ext_iff Units.ext_iff

/-- Each projected batch vanishes exactly when there is a locally equal,
globally different residue. -/
theorem local_iff {F : Type*} [Field F] (f : R →+* F) (A : Finset R) (y : R) :
    f (probe A y) = 0 ↔ ∃ x ∈ A, x ≠ y ∧ f x = f y := by
  rw [probe_eq, map_prod, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨x, h, eq⟩
    exact ⟨x, (mem_erase.mp h).2, (mem_erase.mp h).1,
      (sub_eq_zero.mp (by simpa using eq : f y-f x=0)).symm⟩
  · rintro ⟨x, h, diff, eq⟩
    exact ⟨x, mem_erase.mpr ⟨diff,h⟩, by simp [eq]⟩

/-- If both projections vanish, there is an individual difference that
vanishes at the first coordinate alone, and another at the second alone. -/
theorem saturated {F K : Type*} [Field F] [Field K] (f : R →+* F) (g : R →+* K)
    (A : Finset R) (y : R) (sep : ∀ x, f x=f y → g x=g y → x=y)
    (hf : f (probe A y)=0) (hg : g (probe A y)=0) :
    (∃ x ∈ A, f x=f y ∧ g x≠g y) ∧ (∃ x ∈ A, g x=g y ∧ f x≠f y) := by
  obtain ⟨x, h, ne, eq⟩ := (local_iff f A y).mp hf
  obtain ⟨w, hw, nw, ew⟩ := (local_iff g A y).mp hg
  exact ⟨⟨x,h,eq,fun e => ne (sep x eq e)⟩, ⟨w,hw,ew,fun e => nw (sep w e ew)⟩⟩

/-- In Z/(pq) CRT gives precisely the separation hypothesis, without
any restriction on the base order or on repetitions in either local field. -/
theorem at_semiprime {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (A : Finset (ZMod (p*q))) (y : ZMod (p*q)) (h : probe A y=0) :
    let c := ZMod.chineseRemainder cop
    (∃ x ∈ A, (c x).1=(c y).1 ∧ (c x).2≠(c y).2) ∧
    (∃ x ∈ A, (c x).2=(c y).2 ∧ (c x).1≠(c y).1) := by
  intro c
  let f := (RingHom.fst (ZMod p) (ZMod q)).comp c.toRingHom
  let g := (RingHom.snd (ZMod p) (ZMod q)).comp c.toRingHom
  exact saturated f g A y (fun _ hf hg => c.injective (Prod.ext hf hg))
    (by rw [h, map_zero]) (by rw [h, map_zero])

/-- Converting the two CRT coordinates of a scalar to the two local
divisibility tests gives the actual numerical gcd. -/
theorem first_gcd {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (z : ZMod (p*q)) (h : ((ZMod.chineseRemainder cop) z).1=0)
    (k : ((ZMod.chineseRemainder cop) z).2≠0) : z.val.gcd (p*q)=p := by
  let e := ZMod.chineseRemainder cop
  have val : e z = (z.val : ℕ) := by rw [← map_natCast e, ZMod.natCast_zmod_val]
  have l := congrArg Prod.fst val
  have r := congrArg Prod.snd val
  change (e z).1 = (z.val : ZMod p) at l
  change (e z).2 = (z.val : ZMod q) at r
  apply NormBatchGCD.one_batch (Fact.out : q.Prime)
  · exact (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp (l.symm.trans h)
  · intro dv
    exact k (r.trans ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mpr dv))

/-- The individually recoverable factor from a saturated, corrected batch.
By the preceding theorem the other coordinate also has its own witness. -/
theorem saturated_split {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (A : Finset (ZMod (p*q))) (y : ZMod (p*q)) (h : probe A y=0) :
    ∃ x ∈ A, (y-x).val.gcd (p*q)=p := by
  obtain ⟨x,hx,hit,miss⟩ := (at_semiprime cop A y h).1
  refine ⟨x,hx,first_gcd cop _ ?_ ?_⟩
  · rw [map_sub]; exact sub_eq_zero.mpr hit.symm
  · rw [map_sub]; exact sub_ne_zero.mpr (Ne.symm miss)

/-- The independent panel's first added split. The first modular check
identifies X through its inverse, thereby avoiding negative natural powers.
The two powered keys have different whole-modulus traces. -/
theorem example_gain :
    let n : ℕ := 1433779
    let h := n/2
    let x : ℕ := 352359
    let y : ℕ := 855882
    (x : ZMod 1433779) * 2^((h+1)*4-4150) = 1 ∧
      (2 : ZMod 1433779)^(h*12) = y ∧
      (x : ZMod 1433779)*586811=1 ∧ (y : ZMod 1433779)*352053=1 ∧
      (x : ZMod 1433779)+586811 ≠ (y : ZMod 1433779)+352053 ∧
      (y-x).gcd n=1097 ∧ n=1097*1307 ∧ Nat.Prime 1097 ∧ Nat.Prime 1307 := by
  dsimp only
  have inverse : (2 : ZMod 1433779)^2863410=586811 := by reduce_mod_char
  constructor
  · change (352359 : ZMod 1433779)*2^2863410=1
    rw [inverse]
    decide +kernel
  constructor
  · change (2 : ZMod 1433779)^8602668=855882
    reduce_mod_char
  · decide +kernel

end PrimeFactors.LocalGapProducts
