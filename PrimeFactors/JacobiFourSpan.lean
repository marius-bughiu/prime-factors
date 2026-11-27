import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Tauto

/-!
# Four integer positions with no singleton residue classes

In a window shorter than twice the larger modulus, congruent positions must
be one modulus apart. This determines the layout of two pairs. Requiring the
same four positions to be paired for a second modulus fixes the minimum span.
-/

namespace PrimeFactors.JacobiFourSpan

open Finset

/-- Every occupied class modulo m has at least two distinct positions. -/
def NoSingleton (m : ℕ) (S : Finset ℕ) : Prop :=
  ∀ x ∈ S, ∃ y ∈ S, y ≠ x ∧ x ≡ y [MOD m]

theorem noSingleton_of_zero_buckets {R : Type*} [AddCommMonoid R] {m : ℕ}
    (pos : 0 < m) (S : Finset ℕ) (w : ℕ → R) (nz : ∀ x ∈ S, w x ≠ 0)
    (buckets : ∀ r < m, (∑ x ∈ S.filter (fun k => k % m = r), w x) = 0) :
    NoSingleton m S := by
  intro x hx
  by_contra! h
  have eqn : S.filter (fun k => k % m = x % m) = {x} := by
    ext k
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hk, eq⟩
      exact Classical.byContradiction fun ne => h k hk ne eq.symm
    · rintro rfl
      exact ⟨hx,rfl⟩
  have zero := buckets (x%m) (Nat.mod_lt _ pos)
  rw [eqn,sum_singleton] at zero
  exact nz x hx zero

theorem untranslate {m : ℕ} (s : ℕ) (S : Finset ℕ)
    (translated : NoSingleton m (S.image (s + ·))) : NoSingleton m S := by
  intro x hx
  obtain ⟨v, hv, ne, same⟩ := translated (s+x) (mem_image_of_mem _ hx)
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hv
  exact ⟨y, hy, fun e => ne (congrArg (s+·) e), same.add_left_cancel' s⟩

private theorem mod_small {m k : ℕ} (cap : k < 2*m) :
    k%m = if k<m then k else k-m := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem two_rows {m x y z : ℕ} (xpos : 0 < x) (xy : x < y) (yz : y < z)
    (span : z < 2*m) (paired : NoSingleton m {0,x,y,z}) :
    y = m ∧ z = m+x := by
  have mates (i : ℕ) (hi : i ∈ ({0,x,y,z} : Finset ℕ)) :
      ∃ j ∈ ({0,x,y,z} : Finset ℕ), i+m = j ∨ j+m = i := by
    obtain ⟨j,hj,ne,eqn⟩ := paired i hi
    have cap (k : ℕ) (hk : k ∈ ({0,x,y,z} : Finset ℕ)) : k < 2*m := by
      simp only [mem_insert, mem_singleton] at hk
      omega
    change i%m = j%m at eqn
    rw [mod_small (cap i hi), mod_small (cap j hj)] at eqn
    refine ⟨j,hj,?_⟩
    split_ifs at eqn <;> omega
  have a := mates 0 (by simp)
  simp only [exists_mem_insert, mem_singleton, exists_eq_left, Nat.zero_add] at a
  have at_zero : m=x ∨ m=y ∨ m=z := by omega
  clear a
  rcases at_zero with e | e | e
  · subst x
    have c := mates y (by simp)
    simp only [exists_mem_insert, mem_singleton, exists_eq_left, Nat.zero_add] at c
    omega
  · subst y
    have c := mates x (by simp)
    simp only [exists_mem_insert, mem_singleton, exists_eq_left, Nat.zero_add] at c
    omega
  · subst z
    have c := mates x (by simp)
    simp only [exists_mem_insert, mem_singleton, exists_eq_left, Nat.zero_add] at c
    omega

/-- Below the usual span, the only possible support is {0,a/2,b,2a}
and b is exactly 3a/2. -/
theorem four_short {a b x y z : ℕ} (ab : a < b) (ba : b < 2*a)
    (xpos : 0 < x) (xy : x < y) (yz : y < z) (short : z < a+b)
    (pa : NoSingleton a {0,x,y,z}) (pb : NoSingleton b {0,x,y,z}) :
    2*b = 3*a ∧ x = b-a ∧ y = b ∧ z = 2*a := by
  obtain ⟨rfl, dz⟩ := two_rows xpos xy yz (by omega) pb
  have xa : x<a := by omega
  have h0 := pa 0 (by simp)
  have hx := pa x (by simp)
  simp only [exists_mem_insert, mem_singleton, exists_eq_left, ne_eq, not_true_eq_false,
    false_and, false_or, Nat.ModEq, Nat.zero_mod] at h0 hx
  have xm := Nat.mod_eq_of_lt xa
  have ym : y%a = y-a := by rw [mod_small ba, if_neg (by omega)]
  have zm : z%a = if z<2*a then z-a else z-2*a := by
    rw [Nat.mod_eq_sub_mod (by omega), mod_small (show z-a < 2*a by omega)]
    split_ifs <;> omega
  split_ifs at zm <;> omega

theorem four_short_from {a b l v w h : ℕ} (ab : a < b) (ba : b < 2*a)
    (lv : l < v) (vw : v < w) (wh : w < h) (short : h-l < a+b)
    (pa : NoSingleton a {l,v,w,h}) (pb : NoSingleton b {l,v,w,h}) :
    2*b = 3*a ∧ v-l = b-a ∧ w-l = b ∧ h-l = 2*a := by
  let S : Finset ℕ := {0,v-l,w-l,h-l}
  have rep : S.image (l+·) = {l,v,w,h} := by
    simp [S, Nat.add_sub_of_le (show l≤v by omega), Nat.add_sub_of_le (show l≤w by omega),
      Nat.add_sub_of_le (show l≤h by omega)]
  rw [← rep] at pa pb
  exact four_short ab ba (by omega) (by omega) (by omega) short
    (untranslate l S pa) (untranslate l S pb)

/-- At span a+b, the two inner positions must be a and b. -/
theorem standard_shape {a b x y : ℕ} (ab : a < b) (xpos : 0 < x) (xy : x < y)
    (yz : y < a+b) (pb : NoSingleton b {0,x,y,a+b}) : x = a ∧ y = b := by
  obtain ⟨h,e⟩ := two_rows xpos xy yz (by omega) pb
  omega

/-- Candidate spans of a normalized support of exactly four distinct positions. -/
def spans (a b : ℕ) : Set ℕ :=
  {z | ∃ x y, 0 < x ∧ x < y ∧ y < z ∧ NoSingleton a {0,x,y,z} ∧ NoSingleton b {0,x,y,z}}

private theorem pairs {m r s u v : ℕ} {S : Finset ℕ} (eqn : S = {r,s,u,v})
    (rs : r < s) (uv : u < v) (left : m ∣ s-r) (right : m ∣ v-u) :
    NoSingleton m S := by
  subst S
  have leq := (Nat.modEq_iff_dvd' rs.le).2 left
  have req := (Nat.modEq_iff_dvd' uv.le).2 right
  intro i hi
  simp only [mem_insert,mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact ⟨s,by simp,rs.ne',leq⟩
  · exact ⟨r,by simp,rs.ne,leq.symm⟩
  · exact ⟨v,by simp,uv.ne',req⟩
  · exact ⟨u,by simp,uv.ne,req.symm⟩

private theorem ordinary {a b : ℕ} (ab : a < b) (pos : 0 < a) : a+b ∈ spans a b := by
  refine ⟨a,b,pos,ab,by omega,?_,?_⟩
  · refine pairs (r := 0) (s := a) (u := b) (v := a+b) rfl (by omega) (by omega) ?_ ?_
    · simp
    · simp
  · refine pairs (r := 0) (s := b) (u := a) (v := a+b) ?_ (by omega) (by omega) ?_ ?_
    · ext i
      simp only [mem_insert,mem_singleton]
      tauto
    · simp
    · simp

private theorem special {a b : ℕ} (ab : a < b) (rat : 2*b = 3*a) : 2*a ∈ spans a b := by
  refine ⟨b-a,b,by omega,by omega,by omega,?_,?_⟩
  · refine pairs (r := 0) (s := 2*a) (u := b-a) (v := b) ?_ (by omega) (by omega) ?_ ?_
    · ext i
      simp only [mem_insert,mem_singleton]
      tauto
    · exact ⟨2,by omega⟩
    · exact ⟨1,by omega⟩
  · refine pairs (r := 0) (s := b) (u := b-a) (v := 2*a) ?_ (by omega) (by omega) ?_ ?_
    · ext i
      simp only [mem_insert,mem_singleton]
      tauto
    · exact ⟨1,by omega⟩
    · exact ⟨1,by omega⟩

/-- Exact minimum under the two no-singleton conditions, with no coefficients assumed. -/
theorem least_span {a b : ℕ} (ab : a < b) (ba : b < 2*a) :
    IsLeast (spans a b) (if 2*b=3*a then 2*a else a+b) := by
  constructor
  · split_ifs with h
    · exact special ab h
    · exact ordinary ab (by omega)
  · rintro z ⟨x,y,hx,hxy,hyz,pa,pb⟩
    by_cases short : z < a+b
    · obtain ⟨rat,_,_,last⟩ := four_short ab ba hx hxy hyz short pa pb
      simp [rat,last]
    · split_ifs <;> omega

end PrimeFactors.JacobiFourSpan
