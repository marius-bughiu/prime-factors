import PrimeFactors.FactorialBlockExclusion
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-! A division-free checker for polynomial Bézout identities over Z/nZ.
Coefficient lists are in ascending degree; trailing zero coefficients are
permitted. The executable checker uses natural-number modular arithmetic,
independently of the polynomial representation used in its soundness proof.
For a offsets and b nodes, constructing their products uses a(a+1)/2 and
b(b+1)/2 modular multiply-adds. The two Horner products use |U|(a+1) and
|V|(b+1) further multiply-adds, followed by linear-time combination and
coefficient checks. Generating the witnesses has a separate cost. -/

namespace PrimeFactors.BlockExclusionCheck

open Polynomial

/-- Interpret a dense list of natural residues as a polynomial. -/
noncomputable def poly (n : ℕ) : List ℕ → Polynomial (ZMod n)
  | [] => 0
  | a::as => C (a : ZMod n) + X * poly n as

/-- Coefficients of a times the first list plus the second list. -/
private def addScaled (n a : ℕ) : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | x::xs, [] => (a*x % n) :: addScaled n a xs []
  | x::xs, y::ys => ((a*x+y) % n) :: addScaled n a xs ys

private theorem poly_addScaled (n a : ℕ) (xs ys : List ℕ) :
    poly n (addScaled n a xs ys) = C (a : ZMod n)*poly n xs + poly n ys := by
  induction xs generalizing ys with
  | nil => simp [addScaled,poly]
  | cons x xs ih =>
    cases ys with
    | nil =>
      simp only [addScaled,poly,ih,ZMod.natCast_mod,Nat.cast_mul,map_mul]
      ring
    | cons y ys =>
      simp only [addScaled,poly,ih,ZMod.natCast_mod,Nat.cast_add,Nat.cast_mul,map_add,map_mul]
      ring

/-- Horner multiplication; each multiply-add is reduced modulo n. -/
private def times (n : ℕ) : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | a::as, bs => addScaled n (a%n) bs (0 :: times n as bs)

private theorem poly_times (n : ℕ) (as bs : List ℕ) :
    poly n (times n as bs) = poly n as * poly n bs := by
  induction as with
  | nil => simp [times,poly]
  | cons a as ih =>
    simp only [times,poly_addScaled,poly,Nat.cast_zero,map_zero,ZMod.natCast_mod,ih]
    ring

/-- Coefficients of carry + (X+a)P, with a single pass over P. -/
private def linear (n a carry : ℕ) : List ℕ → List ℕ
  | [] => [carry]
  | b::bs => ((a*b+carry)%n) :: linear n a b bs

private theorem poly_linear (n a carry : ℕ) (bs : List ℕ) :
    poly n (linear n a carry bs) = C (carry : ZMod n) + (X+C (a:ZMod n))*poly n bs := by
  induction bs generalizing carry with
  | nil => simp [poly,linear]
  | cons b bs ih =>
    simp only [linear,poly,ih,ZMod.natCast_mod,Nat.cast_add,Nat.cast_mul,map_add,map_mul]
    ring

private def factors (n : ℕ) (constantTerm : ℕ → ℕ) : List ℕ → List ℕ
  | [] => [1]
  | a::as => linear n (constantTerm a) 0 (factors n constantTerm as)

private theorem poly_factors (n : ℕ) (c : ℕ → ℕ) (as : List ℕ) :
    poly n (factors n c as) = (as.map (fun a => X+C (c a : ZMod n))).prod := by
  induction as with
  | nil => simp [factors,poly]
  | cons a as ih => simp [factors,poly_linear,ih]

private def isOne (n : ℕ) : List ℕ → Bool
  | [] => false
  | a::as => (a%n == 1%n) && as.all (fun b => b%n == 0)

private theorem zero_tail (n : ℕ) {as : List ℕ} (h : as.all (fun b => b%n == 0) = true) :
    poly n as = 0 := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [List.all_cons,Bool.and_eq_true,beq_iff_eq] at h
    have ha : (a:ZMod n)=0 := by rw [←ZMod.natCast_mod a n,h.1,Nat.cast_zero]
    simp [poly,ha,ih h.2]

private theorem isOne_sound (n : ℕ) {as : List ℕ} (h : isOne n as = true) :
    poly n as = 1 := by
  cases as with
  | nil => cases h
  | cons a as =>
    simp only [isOne,Bool.and_eq_true,beq_iff_eq] at h
    have ha : (a:ZMod n)=1 := by rw [←ZMod.natCast_mod a n,h.1,ZMod.natCast_mod,Nat.cast_one]
    simp [poly,ha,zero_tail n h.2]

private def reduced (n : ℕ) : List ℕ → List ℕ
  | [] => []
  | a::as => a%n :: reduced n as

private theorem poly_reduce (n : ℕ) (as : List ℕ) :
    poly n (reduced n as) = poly n as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [reduced,poly,ZMod.natCast_mod,ih]

/-- Check U*A+V*B=1 using four ascending coefficient lists. -/
def coefficientsCheck (n : ℕ) (u a v b : List ℕ) : Bool :=
  isOne n (addScaled n 1 (times n u (reduced n a)) (times n v (reduced n b)))

theorem coefficients_sound {n : ℕ} {u a v b : List ℕ}
    (ok : coefficientsCheck n u a v b = true) :
    poly n u * poly n a + poly n v * poly n b = 1 := by
  simpa only [coefficientsCheck,poly_addScaled,poly_times,poly_reduce,Nat.cast_one,map_one,one_mul] using
    (isOne_sound n ok)

/-- Build A=∏(X+offset) and B=∏(X−node) from public labels, then verify the
two supplied Bézout coefficients U,V. This needs no primality assumption. -/
def check (n : ℕ) (offsets nodes u v : List ℕ) : Bool :=
  coefficientsCheck n u (factors n (fun i => i%n) offsets)
    v (factors n (fun i => n-i%n) nodes)

theorem check_sound {n : ℕ} {offsets nodes u v : List ℕ}
    (hn : 0<n) (ok : check n offsets nodes u v = true) :
    poly n u * (offsets.map (fun a : ℕ => X+C (a : ZMod n))).prod +
    poly n v * (nodes.map (fun b : ℕ => X-C (b : ZMod n))).prod = 1 := by
  have plus (i : ℕ) : ((i%n : ℕ):ZMod n)=i := ZMod.natCast_mod i n
  have minus (i : ℕ) : ((n-i%n : ℕ):ZMod n) = -(i:ZMod n) := by
    rw [Nat.cast_sub (Nat.mod_lt i hn).le,ZMod.natCast_self,ZMod.natCast_mod,zero_sub]
  have h := coefficients_sound (n:=n) (u:=u) (a:=factors n (fun i => i%n) offsets)
    (v:=v) (b:=factors n (fun i => n-i%n) nodes) ok
  simpa only [poly_factors,plus,minus,map_neg,sub_eq_add_neg] using h

/-- Every offset plus a node is coprime to n whenever the public lists
and the two coefficient witnesses pass the checker. -/
theorem rectangle {n : ℕ} {offsets nodes u v : List ℕ} (hn : 0<n)
    (ok : check n offsets nodes u v = true) {a b : ℕ}
    (ha : a ∈ offsets) (hb : b ∈ nodes) : (a+b).Coprime n := by
  simpa only [Nat.add_comm b a] using
    FactorialBlockExclusion.list_rectangle (check_sound hn ok) ha hb

/-- Consecutive offsets and equally spaced nodes cover every integer of
the half-open interval [base, base + side*count). The hypotheses also
cover empty intervals without requiring a positive side or block count. -/
theorem interval {n base side count x : ℕ} {u v : List ℕ} (hn : 0<n)
    (ok : check n (List.range side) ((List.range count).map (fun j => base+side*j)) u v = true)
    (lo : base≤x) (hi : x<base+side*count) : x.Coprime n := by
  have positive : 0<side := by
    by_contra! h
    have z : side=0 := by omega
    simp only [z,zero_mul,add_zero] at hi
    omega
  have slot : (x-base)/side<count := (Nat.div_lt_iff_lt_mul positive).mpr (by
    rw [Nat.mul_comm]; omega)
  have row : (x-base)%side ∈ List.range side := List.mem_range.mpr (Nat.mod_lt _ positive)
  have node : base+side*((x-base)/side) ∈ (List.range count).map (fun j => base+side*j) :=
    List.mem_map.mpr ⟨(x-base)/side,List.mem_range.mpr slot,rfl⟩
  have cover := rectangle hn ok row node
  have combine := Nat.mod_add_div (x-base) side
  rwa [show (x-base)%side+(base+side*((x-base)/side))=x by omega] at cover

end PrimeFactors.BlockExclusionCheck
