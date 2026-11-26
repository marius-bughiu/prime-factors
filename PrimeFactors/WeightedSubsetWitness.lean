import PrimeFactors.WeightedSubsetMenu
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-! A finite list of small primes per row isolates that row's sign and thereby
certifies the absence of square products for every nonempty subset of a menu. -/
namespace PrimeFactors.WeightedSubsetWitness
open Finset

/-- Euler's criterion evaluated on a small residue representative. -/
def reading (p a : ℕ) : ℤ :=
  let e := ((a%p)^(p/2))%p
  if e=0 then 0 else if e=1 then 1 else -1

theorem reading_eq {p : ℕ} (prime : p.Prime) (odd : 2<p) (a : ℕ) :
    reading p a=jacobiSym (a:ℤ) p := by
  letI : Fact p.Prime := ⟨prime⟩
  have h := congrArg ZMod.val (legendreSym.eq_pow p (a:ℤ))
  rw [jacobiSym.legendreSym.to_jacobiSym] at h
  push_cast at h
  rw [←Nat.cast_pow,ZMod.val_natCast,Nat.pow_mod] at h
  rcases jacobiSym.trichotomy (a:ℤ) p with eq|eq|eq
  · rw [eq,Int.cast_zero,ZMod.val_zero] at h
    simp [reading,←h,eq]
  · rw [eq,Int.cast_one,ZMod.val_one'' (by omega : p≠1)] at h
    simp [reading,←h,eq]
  · cases p with
    | zero => omega
    | succ b =>
      rw [eq,Int.cast_neg,Int.cast_one,ZMod.val_neg_one] at h
      simp [reading,←h,eq,show b≠0 by omega,show b≠1 by omega]

/-- This product of Euler readings equals the Jacobi symbol at the product modulus. -/
noncomputable def pooled (primes : List ℕ) (a : ℕ) : ℤ := (primes.map (fun p => reading p a)).prod

theorem pooled_eq {primes : List ℕ} (hp : ∀ p∈primes, p.Prime ∧ 2<p) (a : ℕ) :
    pooled primes a=jacobiSym (a:ℤ) primes.prod := by
  induction primes with
  | nil => simp [pooled,jacobiSym.one_right]
  | cons p ps ih =>
    obtain ⟨prime,odd⟩ := hp p (by simp)
    have rest (q : ℕ) (hq : q∈ps) := hp q (List.mem_cons_of_mem p hq)
    have nz : ps.prod≠0 := List.prod_ne_zero (fun h => (rest _ h).1.ne_zero rfl)
    simp only [pooled,List.map_cons,List.prod_cons]
    rw [jacobiSym.mul_right' _ prime.ne_zero nz,reading_eq prime odd,←ih rest]
    rfl

/-- A single negative Jacobi symbol certifies that every subset containing
the distinguished row has nonsquare product when all the other signs are +1. -/
theorem excludes {ι : Type*} [DecidableEq ι] (D : ι → ℕ) (primes : ι → List ℕ)
    (hp : ∀ i p, p∈primes i → p.Prime ∧ 2<p)
    (signs : ∀ i j, pooled (primes i) (D j) = if i=j then -1 else 1)
    (S : Finset ι) (nonempty : S.Nonempty) (z : ℕ) : (∏ i∈S, D i)≠z^2 := by
  obtain ⟨i,hi⟩ := nonempty
  let m := (primes i).prod
  let χ : ℕ →* ℤ :=
    { toFun := fun a => jacobiSym (a:ℤ) m
      map_one' := by simp [jacobiSym.one_left]
      map_mul' := by intro a b; simp [jacobiSym.mul_left] }
  have value (j : ι) : χ (D j) = if i=j then -1 else 1 :=
    (pooled_eq (hp i) (D j)).symm.trans (signs i j)
  have rest : ∏ j∈S.erase i, χ (D j) = 1 :=
    prod_eq_one (fun j hj => by rw [value,if_neg (ne_of_mem_erase hj).symm])
  have total : χ (∏ j∈S, D j) = -1 := by
    rw [map_prod,←S.mul_prod_erase (fun j => χ (D j)) hi,rest,value,if_pos rfl,mul_one]
  intro sq
  rw [sq,map_pow] at total
  linarith only [sq_nonneg (χ z), total]

/-- With one omitted pivot, the sign of that pivot in each other probe fixes
all membership bits once the pivot bit is chosen. -/
theorem only_possible {ι : Type*} [DecidableEq ι] (D : ι → ℕ) (probes : ι → List ℕ)
    (pivot : ι) (K : Finset ι) (hasPivot : pivot∈K)
    (hp : ∀ i p, p∈probes i → p.Prime ∧ 2<p)
    (signs : ∀ i, i≠pivot → ∀ j, pooled (probes i) (D j) =
      (if i=j then -1 else 1)*(if pivot=j then (if i∈K then -1 else 1) else 1))
    (S : Finset ι) (nonempty : S.Nonempty) {z : ℕ} (sq : (∏ j∈S, D j)=z^2) : S=K := by
  classical
  have bits (i : ι) (ne : i≠pivot) : i∈S ↔ pivot∈S ∧ i∈K := by
    let m := (probes i).prod
    let χ : ℕ →* ℤ :=
      { toFun := fun a => jacobiSym (a:ℤ) m
        map_one' := by simp [jacobiSym.one_left]
        map_mul' := by intro a b; simp [jacobiSym.mul_left] }
    have val (j : ι) := (pooled_eq (hp i) (D j)).symm.trans (signs i ne j)
    have eval : χ (∏ j∈S, D j) =
        (if i∈S then -1 else 1)*(if pivot∈S then (if i∈K then -1 else 1) else 1) := by
      rw [map_prod]
      change (∏ j∈S, jacobiSym (D j) m) = _
      simp_rw [show ∀ j, jacobiSym (D j) m = _ from val]
      rw [prod_mul_distrib,prod_ite_eq,prod_ite_eq]
    rw [sq,map_pow] at eval
    have pos := sq_nonneg (χ z)
    by_cases a : i∈S <;> by_cases b : pivot∈S <;> by_cases c : i∈K <;>
      simp_all only [if_pos,if_neg,not_false_eq_true,and_self,and_true,true_and,
        false_and,and_false,mul_one,one_mul,neg_mul] <;> omega
  have p : pivot∈S := by
    obtain ⟨i,hi⟩ := nonempty
    by_cases eq : i=pivot
    · exact eq ▸ hi
    · exact ((bits i eq).mp hi).1
  ext i
  by_cases eq : i=pivot
  · subst i; exact iff_of_true p hasPivot
  · simpa only [p,true_and] using bits i eq

abbrev Id := Fin 8 × Fin 2

/-- The first two ranks of each of the eight weighted label progressions. -/
def excess (n : ℕ) (i : Id) : ℕ :=
  (WeightedSubsetMenu.vector n i.1 i.2)^2-4*(i.1.val+1)*n

/-- Evaluate the public row starting at a supplied, separately checked ceiling. -/
def evaluated (n : ℕ) (ceiling : Fin 8 → ℕ) (i : Id) : ℕ :=
  let w := i.1.val+1
  let s := Nat.gcd 24 (2*(w+n))
  let a := ceiling i.1
  (a+((w+n)%s+s-a%s)%s+s*i.2.val)^2-4*w*n

theorem exact_rows (n : ℕ) (ceiling : Fin 8 → ℕ) (bounds : ∀ w : Fin 8,
    (ceiling w-1)^2 < 4*(w.val+1)*n ∧ 4*(w.val+1)*n ≤ (ceiling w)^2) (i : Id) :
    excess n i = evaluated n ceiling i := by
  obtain ⟨below,above⟩ := bounds i.1
  have ce : ceilSqrt (4*(i.1.val+1)*n)=ceiling i.1 := by
    apply le_antisymm (ceilSqrt_le_iff.mpr above)
    by_contra! low
    have lo := ceilSqrt_le_iff.mp (show ceilSqrt (4*(i.1.val+1)*n) ≤ ceiling i.1-1 by omega)
    omega
  simp only [excess,evaluated,WeightedSubsetMenu.vector,WeightedMultiplierLabels.labelAt,ce]

/-- A small integer-array interface whose premises allow evaluation in the Lean kernel. -/
theorem certify (n : ℕ) (ceiling : Fin 8 → ℕ) (primes : Fin 8 → Fin 2 → List ℕ)
    (bounds : ∀ w : Fin 8, (ceiling w-1)^2<4*(w.val+1)*n ∧ 4*(w.val+1)*n≤(ceiling w)^2)
    (hp : ∀ w r, (primes w r).all (fun p => decide (p.Prime ∧ 2<p)) = true)
    (signs : ∀ w r w' r', pooled (primes w r) (evaluated n ceiling (w',r')) =
      if w=w' ∧ r=r' then -1 else 1)
    (S : Finset Id) (nonempty : S.Nonempty) (z : ℕ) : (∏ i∈S, excess n i)≠z^2 := by
  apply excludes (excess n) (fun i : Id => primes i.1 i.2) _ _ S nonempty z
  · rintro ⟨w,r⟩ p h
    exact of_decide_eq_true (List.all_eq_true.mp (hp w r) p h)
  · rintro ⟨w,r⟩ ⟨w',r'⟩
    rw [exact_rows n ceiling bounds]
    simpa only [Prod.mk.injEq] using signs w r w' r'

/-- The same endpoint checks plus a concrete square give the exact unique
nonempty subset when the probes distinguish all rows except a single pivot. -/
theorem certify_unique (n : ℕ) (ceiling : Fin 8 → ℕ) (probes : Fin 8 → Fin 2 → List ℕ)
    (pivot : Id) (K : Finset Id) (z : ℕ) (hasPivot : pivot∈K)
    (bounds : ∀ w : Fin 8, (ceiling w-1)^2<4*(w.val+1)*n ∧ 4*(w.val+1)*n≤(ceiling w)^2)
    (hp : ∀ w r, (probes w r).all (fun p => decide (p.Prime ∧ 2<p)) = true)
    (signs : ∀ w r w' r', (w,r)≠pivot → pooled (probes w r) (evaluated n ceiling (w',r')) =
      (if w=w' ∧ r=r' then -1 else 1)*(if pivot=(w',r') then (if (w,r)∈K then -1 else 1) else 1))
    (witness : (∏ i∈K, evaluated n ceiling i)=z^2)
    (S : Finset Id) (nonempty : S.Nonempty) : (∃ y : ℕ, (∏ i∈S, excess n i)=y^2) ↔ S=K := by
  constructor
  · rintro ⟨y,eq⟩
    apply only_possible (excess n) (fun i : Id => probes i.1 i.2) pivot K hasPivot _ _ S nonempty eq
    · rintro ⟨w,r⟩ p h
      exact of_decide_eq_true (List.all_eq_true.mp (hp w r) p h)
    · rintro ⟨w,r⟩ ne ⟨w',r'⟩
      rw [exact_rows n ceiling bounds]
      simpa only [Prod.mk.injEq] using signs w r w' r' ne
  · rintro rfl
    exact ⟨z,(prod_congr rfl (fun i _ => exact_rows n ceiling bounds i)).trans witness⟩

end PrimeFactors.WeightedSubsetWitness
