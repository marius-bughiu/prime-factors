import PrimeFactors.EarlyPersistentMidpoints
import Mathlib.Order.KonigLemma

/-! Compatible modular witnesses for locally square midpoint discriminants. -/
namespace PrimeFactors.CoherentMidpointRoots

/-- Reduction from finer to coarser precision in one power tower. -/
noncomputable def reduce (p : ℕ) {i j : ℕ} (le : i≤j) : ZMod (p^j) →+* ZMod (p^i) :=
  ZMod.castHom (pow_dvd_pow p le) _

def Compatible {p : ℕ} (x : ∀ e : ℕ, ZMod (p^e)) : Prop :=
  ∀ ⦃i j : ℕ⦄ (le : i≤j), reduce p le (x j)=x i

/-- A predicate stable under reduction has a compatible sequence of witnesses
if it has a witness at every finite precision. The individual reductions need
not be surjective on the sets of witnesses. -/
theorem compatible_witnesses (p : ℕ) [NeZero p] (P : (e : ℕ) → ZMod (p^e) → Prop)
    (exists_at : ∀ e, ∃ x, P e x)
    (stable : ∀ ⦃i j⦄ (h : i≤j) x, P j x → P i (reduce p h x)) :
    ∃ x : ∀ e, ZMod (p^e), Compatible x ∧ ∀ e, P e (x e) := by
  let R (e : ℕ) := {x : ZMod (p^e) // P e x}
  letI (e : ℕ) : Finite (R e) := by dsimp [R]; infer_instance
  letI (e : ℕ) : Nonempty (R e) := (exists_at e).elim (fun x hx => ⟨⟨x,hx⟩⟩)
  let proj {i j : ℕ} (le : i≤j) (x : R j) : R i := ⟨reduce p le x.val,stable le x.val x.property⟩
  have refl (i : ℕ) (x : R i) : proj (le_refl i) x=x := by
    apply Subtype.ext
    change ZMod.castHom dvd_rfl _ x.val=x.val
    rw [ZMod.castHom_self,RingHom.id_apply]
  have comp {i j k : ℕ} (ij : i≤j) (jk : j≤k) (x : R k) : proj ij (proj jk x)=proj (ij.trans jk) x := by
    apply Subtype.ext
    exact RingHom.congr_fun (ZMod.castHom_comp (pow_dvd_pow p ij) (pow_dvd_pow p jk)) x.val
  obtain ⟨f,compat⟩ := exists_seq_forall_proj_of_forall_finite (α:=R) (fun h => proj h)
    (fun {i} x => refl i x) (fun {i j k} ij jk x => comp ij jk x) (fun _ _ => Set.toFinite _)
  exact ⟨fun e => (f e).val,fun _ _ le => congrArg Subtype.val (compat le),fun e => (f e).property⟩

/-- One square-root sequence for all levels, with every deeper root reducing
to the specified shallower root. This includes the dyadic case. -/
theorem coherent_roots (p : ℕ) [NeZero p] (d : ℤ) (squares : ∀ e : ℕ, IsSquare (d : ZMod (p^e))) :
    ∃ r : ∀ e, ZMod (p^e), Compatible r ∧ ∀ e, (r e)^2=(d : ZMod (p^e)) := by
  apply compatible_witnesses p (fun e x => x^2=(d : ZMod (p^e)))
  · intro e
    obtain ⟨x,h⟩ := squares e
    exact ⟨x,by simpa only [pow_two] using h.symm⟩
  · intro i j le x hx
    simpa only [map_pow,map_intCast] using congrArg (reduce p le) hx

/-- Two ordered, compatible residue sequences whose products and sums are
prescribed at every prime-power depth. -/
def HasFactors (p : ℕ) (N h : ℤ) : Prop := ∃ a b : ∀ e, ZMod (p^e),
  Compatible a ∧ Compatible b ∧ ∀ e, a e*b e=(N : ZMod (p^e)) ∧ a e+b e=2*(h : ZMod (p^e))

theorem factor_tower (p : ℕ) [NeZero p] (N h : ℤ) :
    (∀ e : ℕ, IsSquare ((h^2-N : ℤ) : ZMod (p^e))) ↔ HasFactors p N h := by
  constructor
  · intro square
    obtain ⟨r,compat,roots⟩ := coherent_roots p (h^2-N) square
    refine ⟨fun e => h+r e,fun e => h-r e,?_,?_,?_⟩
    · intro i j le
      simp only [map_add,map_intCast,compat le]
    · intro i j le
      simp only [map_sub,map_intCast,compat le]
    · intro e
      have sq := roots e
      push_cast at sq
      exact ⟨by linear_combination -sq,by ring⟩
  · rintro ⟨a,b,_,_,laws⟩ e
    obtain ⟨prod,sum⟩ := laws e
    have hb : b e=2*(h : ZMod (p^e))-a e := by linear_combination sum
    rw [hb] at prod
    refine ⟨a e-h,?_⟩
    push_cast
    rw [←prod]
    ring

/-- Each persistent midpoint admits a simultaneous choice of two compatible
factor residues for every tested prime and every depth. -/
theorem simultaneous {N h : ℕ} (pass : EarlyPersistentMidpoints.Passes N h) :
    ∃ a b : (p : {p // p ∈ PersistentLocalSurvivors.smallPrimes 643}) → (e : ℕ) → ZMod (p.val^e),
      ∀ p, Compatible (a p) ∧ Compatible (b p) ∧
        ∀ e, a p e*b p e=(N : ZMod (p.val^e)) ∧ a p e+b p e=2*(h : ZMod (p.val^e)) := by
  have towers (p : {p // p ∈ PersistentLocalSurvivors.smallPrimes 643}) : HasFactors p.val N h := by
    have prime : p.val.Prime := (Finset.mem_filter.mp p.property).2
    haveI : NeZero p.val := ⟨prime.ne_zero⟩
    exact (factor_tower p.val N h).mp (pass p.val p.property)
  choose a b laws using towers
  exact ⟨a,b,fun p => by simpa only [Int.cast_natCast] using laws p⟩

/-- For 143 = 11·13, the proposed midpoint 20 has discriminant 257. It
admits a compatible pair at every dyadic depth despite its nonsquare integer discriminant. -/
theorem dyadic_false_midpoint : 11*13=143 ∧ ¬IsSquare (257 : ℕ) ∧ HasFactors 2 143 20 := by
  refine ⟨by decide,by decide +kernel,(factor_tower 2 143 20).mp ?_⟩
  intro e
  exact PersistentLocalSurvivors.dyadic_unit_square 32 e

end PrimeFactors.CoherentMidpointRoots
