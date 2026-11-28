import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-! Recognizing a special family of values of Sophie Germain's identity.
The two coordinates are recovered from the input whenever its leading fourth
power is the fourth power immediately below it. -/
namespace PrimeFactors.RecognizingQuarticProducts

def fourthRoot (n : ℕ) : ℕ := n.sqrt.sqrt

theorem le_fourthRoot {n x : ℕ} : x ≤ fourthRoot n ↔ x^4 ≤ n := by
  rw [fourthRoot, Nat.le_sqrt', Nat.le_sqrt', ← pow_mul]

theorem fourthRoot_eq_iff {n x : ℕ} :
    fourthRoot n = x ↔ x^4 ≤ n ∧ n < (x+1)^4 := by
  have upper : fourthRoot n < x+1 ↔ n < (x+1)^4 := by
    rw [← not_le, ← not_le, le_fourthRoot]
  constructor
  · intro h
    exact ⟨le_fourthRoot.mp h.ge,upper.mp (by omega)⟩
  · rintro ⟨low,high⟩
    have a := le_fourthRoot.mpr low
    have b := upper.mpr high
    omega

theorem fourthRoot_pow (x : ℕ) : fourthRoot (x^4) = x :=
  fourthRoot_eq_iff.mpr ⟨le_rfl,Nat.pow_lt_pow_left (by omega) (by decide)⟩

def factors (x y : ℕ) : ℕ × ℕ :=
  (x^2+2*y^2-2*x*y,x^2+2*y^2+2*x*y)

private theorem no_truncation (x y : ℕ) : 2*x*y≤x^2+2*y^2 := by
  have h := two_mul_le_add_sq x y
  omega

theorem factor_product (x y : ℕ) : (factors x y).1 * (factors x y).2 = x^4+4*y^4 := by
  unfold factors
  dsimp
  zify [no_truncation]
  ring

theorem factor_sum (x y : ℕ) : (factors x y).1 + (factors x y).2 = 2*x^2+4*y^2 := by
  unfold factors
  dsimp
  zify [no_truncation]
  ring

/-- Both factors are strictly between one and their product, except at x=y=1. -/
theorem proper_iff {x y : ℕ} (xp : 0<x) (yp : 0<y) :
    (1<(factors x y).1 ∧ (factors x y).1<(factors x y).2 ∧
      (factors x y).2<x^4+4*y^4) ↔ (x,y)≠(1,1) := by
  constructor
  · rintro ⟨lower,_,_⟩ e
    have ex : x=1 := congrArg Prod.fst e
    have ey : y=1 := congrArg Prod.snd e
    subst x; subst y
    norm_num [factors] at lower
  · intro distinct
    have h₁ := two_mul_le_add_sq x y
    have bound : y^2≤(factors x y).1 := by dsimp [factors]; omega
    have lower : 1<(factors x y).1 := by
      by_cases one : y=1
      · subst y
        have ne : x≠1 := fun h => distinct (Prod.ext h rfl)
        have big : 2≤x := by omega
        have scaled := Nat.mul_le_mul_right x big
        simp only [factors, pow_two, one_mul, mul_one]
        omega
      · have big : 2≤y := by omega
        have sq := Nat.pow_le_pow_left big 2
        omega
    have xy : 0<2*x*y := by positivity
    have ord : (factors x y).1<(factors x y).2 := by
      dsimp [factors]
      omega
    refine ⟨lower,ord,?_⟩
    rw [← factor_product]
    have := Nat.mul_lt_mul_of_pos_right lower (Nat.zero_lt_of_lt ord)
    simpa only [one_mul] using this

/-- Public recognition uses two integer fourth roots. Exact reconstruction
rejects a remainder with a nonzero residue modulo four or a non-fourth power. -/
def recognize (n : ℕ) : Option (ℕ × ℕ) :=
  let x := fourthRoot n
  let r := n-x^4
  let y := fourthRoot (r/4)
  if 0<x ∧ 0<y ∧ r=4*y^4 then some (factors x y) else none

theorem complete {n x y : ℕ} (xp : 0<x) (yp : 0<y) (repr : n=x^4+4*y^4)
    (upper : n<(x+1)^4) : recognize n = some (factors x y) := by
  have root : fourthRoot n=x := fourthRoot_eq_iff.mpr ⟨by omega,upper⟩
  unfold recognize
  simp only [root]
  simp [repr, fourthRoot_pow, xp, yp]

theorem sound {n : ℕ} {ab : ℕ × ℕ} (hit : recognize n=some ab) :
    ∃ x y : ℕ, 0<x ∧ 0<y ∧ n=x^4+4*y^4 ∧ n<(x+1)^4 ∧ ab=factors x y := by
  let x := fourthRoot n
  let y := fourthRoot ((n-x^4)/4)
  have bounds : x^4≤n ∧ n<(x+1)^4 := fourthRoot_eq_iff.mp rfl
  change (if 0<x ∧ 0<y ∧ n-x^4=4*y^4 then some (factors x y) else none) = some ab at hit
  split at hit
  · rename_i h
    exact ⟨x,y,h.1,h.2.1,by omega,bounds.2,(Option.some.inj hit).symm⟩
  · contradiction

theorem recognizes_iff {n : ℕ} : (recognize n).isSome = true ↔
    ∃ x y : ℕ, 0<x ∧ 0<y ∧ n=x^4+4*y^4 ∧ n<(x+1)^4 := by
  constructor
  · intro hit
    cases eq : recognize n with
    | none => simp [eq] at hit
    | some ab =>
      obtain ⟨x,y,xp,yp,repr,upper,_⟩ := sound eq
      exact ⟨x,y,xp,yp,repr,upper⟩
  · rintro ⟨x,y,xp,yp,repr,upper⟩
    rw [complete xp yp repr upper]
    rfl

theorem returned_product {n a b : ℕ} (hit : recognize n=some (a,b)) : a*b=n := by
  obtain ⟨x,y,_,_,repr,_,eq⟩ := sound hit
  exact (congrArg (fun t : ℕ×ℕ => t.1*t.2) eq).trans ((factor_product x y).trans repr.symm)

/-- The factor sum is determined by the two computed fourth roots. -/
theorem returned_sum {n a b : ℕ} (hit : recognize n=some (a,b)) :
    a+b=2*(fourthRoot n)^2+4*(fourthRoot ((n-(fourthRoot n)^4)/4))^2 := by
  obtain ⟨x,y,xp,yp,repr,upper,eq⟩ := sound hit
  have root : fourthRoot n=x := fourthRoot_eq_iff.mpr ⟨by omega,upper⟩
  rw [root,repr,Nat.add_sub_cancel_left,Nat.mul_div_cancel_left _ (by decide : 0<4),fourthRoot_pow]
  exact (congrArg (fun t : ℕ×ℕ => t.1+t.2) eq).trans (factor_sum x y)

theorem example_recognized :
    recognize 151847041 = some (10301,14741) ∧ Nat.Prime 10301 ∧ Nat.Prime 14741 := by
  have hit := complete (n:=151847041) (x:=111) (y:=10) (by decide) (by decide)
    (by norm_num) (by norm_num)
  exact ⟨hit.trans (by norm_num [factors]),by norm_num,by norm_num⟩

/-- Crossing exactly one fourth-power boundary can obscure a balanced pair. -/
theorem example_crossing :
    1291357674469 = 1065^4+4*(187:ℕ)^4 ∧ factors 1065 187 = (805853,1602473) ∧
    Nat.Prime 805853 ∧ Nat.Prime 1602473 ∧ 1602473<2*(805853:ℕ) ∧
    fourthRoot 1291357674469 = 1066 ∧ recognize 1291357674469 = none := by
  have root : fourthRoot 1291357674469 = 1066 :=
    fourthRoot_eq_iff.mpr ⟨by norm_num,by norm_num⟩
  refine ⟨by norm_num, by norm_num [factors], by norm_num, by norm_num, by decide, root, ?_⟩
  cases hit : recognize 1291357674469 with
  | none => rfl
  | some ab =>
    obtain ⟨x,y,_,_,repr,upper,_⟩ := sound hit
    have eq : fourthRoot 1291357674469=x := fourthRoot_eq_iff.mpr ⟨by omega,upper⟩
    have ex : x=1066 := eq.symm.trans root
    rw [ex] at repr
    norm_num at repr
    omega

end PrimeFactors.RecognizingQuarticProducts
