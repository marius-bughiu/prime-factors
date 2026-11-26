import PrimeFactors.UniformDivisorCount
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Public residues and exact lifts of a shifted product on the local factor
hyperbola. The coverage obstruction concerns all local orientations. -/

namespace PrimeFactors.ShiftedEndpointProduct
open Finset

set_option exponentiation.threshold 100000

/-- All odd first-factor residues give the same shifted product as x=1. -/
def Pinned (m n a b : ℤ) : Prop :=
  ∀ x y : ℤ, Odd x → m∣x*y-n → m∣(x-a)*(y-b)-(1-a)*(n-b)

private theorem finite_differences (m n a b : ℤ) :
    (∀ j : ℤ, m∣(2*j)*(b*(1+2*j)-a*n)) ↔
      m∣2*(3*b-a*n) ∧ m∣8*b := by
  constructor
  · intro h
    obtain ⟨u,hu⟩ := h 1
    obtain ⟨v,hv⟩ := h 2
    exact ⟨⟨u,by linarith only [hu]⟩,⟨v-2*u,by linarith only [hu,hv]⟩⟩
  · rintro ⟨⟨u,hu⟩,⟨v,hv⟩⟩ j
    obtain ⟨t,ht⟩ := Int.even_mul_pred_self j
    refine ⟨u*j+v*t,?_⟩
    linear_combination j*hu+t*hv+4*b*ht

/-- A complete characterization of constant predictions over a dyadic
modulus. Necessity already follows from the orientations x=3 and x=5. -/
theorem pinned_iff (k : ℕ) (n a b : ℤ) :
    Pinned (2^k) n a b ↔ (2:ℤ)^k∣2*(3*b-a*n) ∧ (2:ℤ)^k∣8*b := by
  rw [←finite_differences]
  let m := (2:ℤ)^k
  have cop (x : ℤ) (h : Odd x) : IsCoprime m x := by
    obtain ⟨j,hj⟩ := h
    have h₂ : IsCoprime (2:ℤ) x := ⟨-j,1,by linarith only [hj]⟩
    exact h₂.pow_left
  have id (x y : ℤ) : x*((x-a)*(y-b)-(1-a)*(n-b))=
      (x-a)*(x*y-n)-(x-1)*(b*x-a*n) := by ring
  constructor
  · intro pin j
    let x := 1+2*j
    have ox : Odd x := ⟨j,by dsimp [x];ring⟩
    obtain ⟨s,t,bez⟩ := cop x ox
    let y := n*t
    have xy : m∣x*y-n := ⟨-n*s,by dsimp [y]; linear_combination n*bez⟩
    have dd := dvd_mul_of_dvd_right (pin x y ox xy) x
    have div := dvd_sub (dvd_mul_of_dvd_right xy (x-a)) dd
    have eq : (x-a)*(x*y-n)-x*((x-a)*(y-b)-(1-a)*(n-b))=(2*j)*(b*(1+2*j)-a*n) := by
      rw [id]; dsimp [x]; ring
    rwa [eq] at div
  · intro differences x y ox xy
    obtain ⟨j,hj⟩ := ox
    have h := differences j
    have eq : (x-1)*(b*x-a*n)=(2*j)*(b*(1+2*j)-a*n) := by rw [hj]; ring
    apply (cop x ⟨j,hj⟩).dvd_of_dvd_mul_left
    rw [id,eq]
    exact dvd_sub (dvd_mul_of_dvd_right xy (x-a)) h

/-- One *exact* lift of the shifted product gives a single weighted
discriminant; this identity permits checking it without factoring the lift. -/
theorem discriminant {p q a b w n : ℤ} (prod : p*q=n) (lift : (p-a)*(q-b)=w) :
    n+a*b-w=b*p+a*q ∧ (n+a*b-w)^2-4*a*b*n=(b*p-a*q)^2 := by
  subst n w
  constructor <;> ring

/-- Alternative first-factor residues when the two integer origins may be
translated by any multiples of m. Including both signs is necessary. -/
private def residues (m a w : ℤ) : Finset ℤ :=
  (w.natAbs.divisors.image fun d : ℕ => (a+(d:ℤ))%m) ∪
  (w.natAbs.divisors.image fun d : ℕ => (a-(d:ℤ))%m)

private theorem mem_residues {m a w x t : ℤ} (nw : w≠0) (dv : t∣w)
    (match_ : x=(a+t)%m) : x∈residues m a w := by
  have mem := Nat.mem_divisors.mpr ⟨Int.natAbs_dvd_natAbs.mpr dv,(Int.natAbs_pos.mpr nw).ne'⟩
  rcases Int.natAbs_eq t with hp|hn
  · exact mem_union_left _ (mem_image.mpr ⟨t.natAbs,mem,by rw [←hp,←match_]⟩)
  · apply mem_union_right _
    apply mem_image.mpr
    exact ⟨t.natAbs,mem,by rw [sub_eq_add_neg,←hn,←match_]⟩

private theorem card_residues (m a w : ℤ) :
    (residues m a w).card ≤ 2*w.natAbs.divisors.card := by
  unfold residues
  exact (card_union_le _ _).trans ((Nat.add_le_add card_image_le card_image_le).trans_eq (two_mul _).symm)

/-- Counts even menus which were chosen using the entire public input.
An entry gives the first origin modulo m and one nonzero signed product lift. -/
theorem menu_count {ι : Type*} [DecidableEq ι] (menu : Finset ι) (xset : Finset ℤ) (m : ℤ)
    (a w : ι→ℤ) (covers : ∀ x∈xset, ∃ i∈menu, w i≠0 ∧ ∃ t : ℤ, t∣w i ∧ x=(a i+t)%m) :
    xset.card ≤ ∑ i∈menu, 2*(w i).natAbs.divisors.card := by
  have inside : xset ⊆ menu.biUnion (fun i => residues m (a i) (w i)) := by
    intro x hx
    obtain ⟨i,im,ne,t,dt,eq⟩ := covers x hx
    exact mem_biUnion.mpr ⟨i,im,mem_residues ne dt eq⟩
  exact (card_le_card inside).trans (card_biUnion_le.trans (sum_le_sum fun i _ => card_residues ..))

/-- At M=2^640, covering every odd first residue with exact nonzero products
of absolute size below M² requires more than 2^471 entries. -/
theorem many_lifts {ι : Type*} [DecidableEq ι] (menu : Finset ι) (a w : ι→ℤ)
    (cap : ∀ i∈menu, (w i).natAbs<2^1280)
    (covers : ∀ j : ℕ, j<2^639 → ∃ i∈menu, w i≠0 ∧ ∃ t : ℤ, t∣w i ∧
      2*(j:ℤ)+1=(a i+t)%2^640) : 2^471<menu.card := by
  let f (j : ℕ) : ℤ := 2*(j:ℤ)+1
  have inject : Function.Injective f := by intro i j h; dsimp [f] at h; omega
  have lower := menu_count menu ((range (2^639)).image f) (2^640) a w (by
    intro x hx
    obtain ⟨j,mem,rfl⟩ := mem_image.mp hx
    exact covers j (mem_range.mp mem))
  rw [card_image_of_injective _ inject,card_range] at lower
  have nz : menu.Nonempty := by
    obtain ⟨i,mem,_⟩ := covers 0 (by decide)
    exact ⟨i,mem⟩
  have row (i) (mem : i∈menu) : 2*(w i).natAbs.divisors.card < 2^168 := by
    by_cases z : w i=0
    · simp [z]
    · have h := UniformDivisorCount.below_power_two (Int.natAbs_pos.mpr z) (cap i mem)
      have t : (w i).natAbs.divisors.card<2^167 := by
        apply (Nat.pow_lt_pow_iff_left (by decide : 336≠0)).mp
        rw [←pow_mul]
        exact h.trans_le (Nat.pow_le_pow_right (by decide) (by decide))
      omega
  have strict := sum_lt_sum_of_nonempty nz row
  simp only [sum_const,nsmul_eq_mul] at strict
  by_contra! small
  have upper := Nat.mul_le_mul_right (2^168) small
  have bad := lower.trans_lt (strict.trans_le upper)
  exact (by decide : ¬(2^639<(2:ℕ)^471*2^168)) bad

/-- A public endpoint, its rounded partner, and the centered lift modulo 256
recover the two factors by one weighted discriminant. -/
theorem endpoint_example :
    let n : ℕ := 4707529
    let a := 2^(n.log2/2)
    let b := 256*((n+128*a)/(256*a))
    let w : ℤ := ((n:ℤ)+128)%256-128
    let t := ((n:ℤ)+a*b-w).toNat
    let gap := 34048
    a=2048 ∧ b=2304 ∧ w= -55 ∧ gap^2+4*a*b*n=t^2 ∧ n.gcd ((t+gap)/2)=2053 ∧ n.gcd ((t-gap)/2)=2293 := by
  have lo := (Nat.le_log2 (by decide : (4707529:ℕ)≠0)).mpr (by decide : 2^22≤(4707529:ℕ))
  have hi := (Nat.log2_lt (by decide : (4707529:ℕ)≠0)).mpr (by decide : (4707529:ℕ)<2^23)
  dsimp only
  rw [show Nat.log2 4707529=22 by omega]
  decide +kernel

end PrimeFactors.ShiftedEndpointProduct
