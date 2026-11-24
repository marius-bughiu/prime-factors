import Mathlib.Data.Fintype.Prod

/-! A local sign is encoded by a bit, with false for +1. The product of the
two Legendre signs supplies their XOR at the public modulus. -/

namespace PrimeFactors.NormSignList

abbrev Signs := Bool × Bool

def zero : Signs := (false, false)

def combine (x y : Signs) : Signs := (xor x.1 y.1, xor x.2 y.2)

def parity (x : Signs) : Bool := xor x.1 x.2

def anchor (p : Signs) (b : Bool) : Signs := if b then p else zero

def adjust (p : Signs) (b : Bool) (g : Signs) : Signs :=
  if parity g = b then g else combine p g

/-- The branch decisions use only public parities. With a pivot, the first
candidate is either the pivot or 1, followed by one candidate per remaining
generator. Without a pivot every product has even parity. -/
noncomputable def candidates (gs : List Signs) (b : Bool) : List Signs :=
  match gs.find? parity with
  | none => if b then [] else zero :: gs
  | some p => anchor p b :: (gs.eraseP parity).map (adjust p b)

theorem length_candidates_le (gs : List Signs) (b : Bool) :
    (candidates gs b).length ≤ gs.length + 1 := by
  unfold candidates
  split
  · cases b <;> simp
  · simp only [List.length_cons, List.length_map]
    exact Nat.succ_le_succ List.length_eraseP_le

/-- All signs obtained from finite products, including the empty product. -/
inductive Generated (gs : List Signs) : Signs → Prop where
  | unit : Generated gs zero
  | step {x g} : Generated gs x → g ∈ gs → Generated gs (combine x g)

/-- The three nonzero linear functionals on pairs of sign bits. -/
abbrev Character := Option Bool

def Character.left : Character := some false

def Character.right : Character := some true

def Character.joint : Character := none

def Character.value : Character → Signs → Bool
  | some false, x => x.1
  | some true, x => x.2
  | none, x => parity x

theorem Character.value_combine (c : Character) :
    ∀ x y : Signs, c.value (combine x y) = xor (c.value x) (c.value y) := by
  rcases c with _ | (_ | _) <;> decide

theorem Generated.vanishes {gs : List Signs} {t : Signs} (ht : Generated gs t)
    (c : Character) (h : ∀ g ∈ gs, c.value g = false) : c.value t = false := by
  induction ht with
  | unit => rcases c with _ | (_ | _) <;> rfl
  | step _ mem ih => rw [c.value_combine, ih, h _ mem]; rfl

private def pivotCharacter (p : Signs) : Character := if p.1 then .right else .left

-- The two signs at a fixed public parity differ in both coordinates.
private theorem pivot_dichotomy : ∀ p t : Signs, parity p = true →
    t ≠ anchor p (parity t) →
      (pivotCharacter p).value t = true ∧ (pivotCharacter p).value p = false ∧
      ∀ g : Signs, t ≠ adjust p (parity t) g → (pivotCharacter p).value g = false := by
  decide

private theorem even_dichotomy : ∀ t : Signs, parity t = false → t ≠ zero →
    t.1 = true ∧ ∀ g : Signs, parity g = false → t ≠ g → g.1 = false := by
  decide

private theorem other_mem_erasePivot {gs : List Signs} {g p : Signs}
    (hp : gs.find? parity = some p) (hg : g ∈ gs) (ne : g ≠ p) :
    g ∈ gs.eraseP parity := by
  induction gs with
  | nil => simp at hg
  | cons x xs ih =>
    by_cases hx : parity x = true
    · simp [List.find?, hx] at hp
      subst p
      simpa [List.eraseP, hx] using (List.mem_cons.mp hg).resolve_left ne
    · simp [List.find?, hx] at hp
      simpa [List.eraseP, hx] using (List.mem_cons.mp hg).imp_right fun h => ih hp h

/-- A missed target is detected by a particular one of the three characters.
It is nontrivial at the target and trivial at every generator. -/
theorem separator_of_miss {gs : List Signs} {t : Signs}
    (miss : t ∉ candidates gs (parity t)) :
    ∃ c : Character, c.value t = true ∧ ∀ g ∈ gs, c.value g = false := by
  cases hp : gs.find? parity with
  | none =>
    have even (g) (hg : g ∈ gs) : parity g = false :=
      by simpa using List.find?_eq_none.mp hp g hg
    cases ht : parity t with
    | true => exact ⟨.joint, ht, even⟩
    | false =>
      simp [candidates, hp, ht] at miss
      obtain ⟨target, each⟩ := even_dichotomy t ht miss.1
      refine ⟨.left, target, fun g hg => each g (even g hg) ?_⟩
      exact fun e => miss.2 (e ▸ hg)
  | some p =>
    simp only [candidates, hp, List.mem_cons, List.mem_map, not_or] at miss
    obtain ⟨target, pivot, each⟩ := pivot_dichotomy p t (List.find?_some hp) miss.1
    refine ⟨pivotCharacter p, target, fun g hg => ?_⟩
    by_cases eq : g = p
    · exact eq ▸ pivot
    · exact each g fun e => miss.2 ⟨g, other_mem_erasePivot hp hg eq, e.symm⟩

/-- The product-selected list tests every attainable target at its public
parity, for arbitrary list length and allowing repeated sign pairs. -/
theorem mem_candidates_of_generated {gs : List Signs} {t : Signs}
    (ht : Generated gs t) : t ∈ candidates gs (parity t) := by
  by_contra miss
  obtain ⟨c, target, killed⟩ := separator_of_miss miss
  rw [ht.vanishes c killed] at target
  contradiction

private theorem single {gs : List Signs} {g : Signs} (hg : g ∈ gs) : Generated gs g := by
  have identity : ∀ x : Signs, combine zero x = x := by decide
  simpa only [identity] using Generated.step Generated.unit hg

/-- Each candidate is an empty product, a generator, or the product of the
pivot and one generator. This direction works for either requested parity. -/
theorem generated_of_mem_candidates {gs : List Signs} {b : Bool} {t : Signs}
    (ht : t ∈ candidates gs b) : Generated gs t := by
  cases hp : gs.find? parity with
  | none =>
    cases b with
    | true => simp [candidates, hp] at ht
    | false =>
      simp [candidates, hp] at ht
      rcases ht with rfl | member
      · exact .unit
      · exact single member
  | some p =>
    have pivot := single (List.mem_of_find?_eq_some hp)
    simp only [candidates, hp, List.mem_cons, List.mem_map] at ht
    rcases ht with rfl | ⟨g, hg, rfl⟩
    · cases b <;> first | exact .unit | exact pivot
    · have hg' := List.mem_of_mem_eraseP hg
      unfold adjust
      split
      · exact single hg'
      · exact .step pivot hg'

theorem mem_candidates_iff_generated {gs : List Signs} {t : Signs} :
    t ∈ candidates gs (parity t) ↔ Generated gs t :=
  ⟨generated_of_mem_candidates, mem_candidates_of_generated⟩

theorem miss_iff_separator {gs : List Signs} {t : Signs} :
    t ∉ candidates gs (parity t) ↔
      ∃ c : Character, c.value t = true ∧ ∀ g ∈ gs, c.value g = false := by
  refine ⟨separator_of_miss, ?_⟩
  rintro ⟨c, target, killed⟩ hit
  rw [(generated_of_mem_candidates hit).vanishes c killed] at target
  contradiction

end PrimeFactors.NormSignList
