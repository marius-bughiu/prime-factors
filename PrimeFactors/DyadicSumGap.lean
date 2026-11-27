import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-! Coupled dyadic lifts for h=(p+q)/2 and d=(q−p)/2.
At modulus M the compatibility test uses the public target modulo 2M. The two
individual projections are modular hyperbola sum and difference sets, as in
Bower, Evans, Luo and Miller (https://arxiv.org/abs/1212.2930). -/
namespace PrimeFactors.DyadicSumGap
open Finset

/-- The extra bit is visible because squares modulo 2M depend only on an argument modulo even M. -/
abbrev Compatible (n M h d : ℤ) : Prop := 2*M ∣ h^2-d^2-n

theorem of_factors (p q h d : ℤ) (hp : p=h-d) (hq : q=h+d) (M : ℤ) :
    Compatible (p*q) M h d := by rw [hp,hq]; unfold Compatible; convert dvd_zero _ using 1; ring

/-- Once the lower pair is known, its signed residual k determines the next-bit constraint. -/
theorem child_iff {n M h d k : ℤ} (pos : 0<M) (four : 4 ∣ M)
    (parent : h^2-d^2-n=2*M*k) (u v : ℤ) :
    Compatible n (2*M) (h+M*u) (d+M*v) ↔
      (k:ZMod 2) + (h:ZMod 2)*u - (d:ZMod 2)*v=0 := by
  obtain ⟨s,hs⟩ := four
  have expand : (h+M*u)^2-(d+M*v)^2-n = (2*M)*(k+h*u-d*v+2*(s*(u^2-v^2))) := by
    calc
      _ = (h^2-d^2-n)+2*M*(h*u-d*v)+M^2*(u^2-v^2) := by ring
      _ = _ := by rw [parent,hs]; ring
  unfold Compatible
  rw [expand,show 2*(2*M)=(2*M)*2 by ring,mul_dvd_mul_iff_left (by positivity : 2*M≠0),
    dvd_add_left (dvd_mul_right 2 _)]
  change ((2:ℕ):ℤ) ∣ _ ↔ _
  rw [←ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rfl

/-- Recover the parent compatibility directly from any child, even if the proposed lower
coordinates were chosen without testing them first. -/
private theorem parent_of_child {n M h d u v : ℤ} (four : 4∣M)
    (hit : Compatible n (2*M) (h+M*u) (d+M*v)) : Compatible n M h d := by
  obtain ⟨k,hk⟩ := hit
  obtain ⟨s,rfl⟩ := four
  refine ⟨2*k-h*u+d*v-2*s*(u^2-v^2),?_⟩
  linear_combination hk

private theorem opposite {n M h d k : ℤ} (odd : (n:ZMod 2)=1)
    (parent : h^2-d^2-n=2*M*k) : (h:ZMod 2)≠(d:ZMod 2) := by
  intro same
  have eq := congrArg (fun z : ℤ => (z : ZMod 2)) parent
  push_cast at eq
  rw [same,odd,show (2:ZMod 2)=0 by decide] at eq
  norm_num at eq

private def red : ZMod 4 →+* ZMod 2 := ZMod.castHom (by decide : 2∣4) _

/-- N modulo four identifies the coordinate whose next binary digit is forced. -/
theorem parity {n M h d k : ℤ} (four : 4∣M) (parent : h^2-d^2-n=2*M*k) :
    ((n:ZMod 4)=1 → (h:ZMod 2)=1 ∧ (d:ZMod 2)=0) ∧
    ((n:ZMod 4)=3 → (h:ZMod 2)=0 ∧ (d:ZMod 2)=1) := by
  obtain ⟨s,rfl⟩ := four
  have eq := congrArg (fun z : ℤ => (z : ZMod 4)) parent
  push_cast at eq
  rw [show (4:ZMod 4)=0 by decide] at eq
  have hs : (h:ZMod 4)^2 - (d:ZMod 4)^2=(n:ZMod 4) := by linear_combination eq
  have table : ∀ x y : ZMod 4,
    (x^2-y^2=1 → red x=1 ∧ red y=0) ∧ (x^2-y^2=3 → red x=0 ∧ red y=1) := by decide +kernel
  simpa only [map_intCast,hs] using table (h:ZMod 4) (d:ZMod 4)

/-- For each admitted pair the linear bit constraint has two solutions out of four,
including pairs with a highly even or zero gap. -/
theorem child_count {n M h d : ℤ} (odd : (n:ZMod 2)=1) (pos : 0<M) (four : 4∣M) :
    (univ.filter (fun b : Fin 2 × Fin 2 => Compatible n (2*M)
      (h+M*(b.1:ℕ)) (d+M*(b.2:ℕ)))).card = if Compatible n M h d then 2 else 0 := by
  by_cases valid : Compatible n M h d
  · rw [if_pos valid]
    obtain ⟨k,hk⟩ := valid
    have table : ∀ H D K : ZMod 2, H≠D → (univ.filter (fun b : Fin 2 × Fin 2 =>
      K+H*(b.1:ℕ)-D*(b.2:ℕ)=0)).card=2 := by decide +kernel
    convert table (h:ZMod 2) (d:ZMod 2) (k:ZMod 2) (opposite odd hk) using 1
    congr 1; ext b
    simp only [mem_filter,mem_univ,true_and,child_iff pos four hk,Int.cast_natCast]
  · rw [if_neg valid,card_eq_zero,filter_eq_empty_iff]
    exact fun _ _ child => valid (parent_of_child four child)

/-- Every admissible pair extends to arbitrary dyadic precision. Further local lifting
cannot invalidate its low bits, even when a corresponding univariate square root is singular. -/
theorem lift_to {n M h d : ℤ} (odd : (n:ZMod 2)=1) (pos : 0<M) (four : 4∣M)
    (valid : Compatible n M h d) (j : ℕ) :
    ∃ u v : ℤ, Compatible n (M*2^j) (h+M*u) (d+M*v) := by
  induction j with
  | zero => exact ⟨0,0,by simpa using valid⟩
  | succ j ih =>
    obtain ⟨u,v,was⟩ := ih
    have count := child_count (h:=h+M*u) (d:=d+M*v) odd (mul_pos pos (by positivity : 0<(2:ℤ)^j))
      (dvd_mul_of_dvd_left four ((2:ℤ)^j))
    rw [if_pos was] at count
    obtain ⟨b,hb⟩ := Finset.card_pos.mp (count ▸ (by decide : 0<2))
    have hit := (mem_filter.mp hb).2
    refine ⟨u+2^j*(b.1:ℕ),v+2^j*(b.2:ℕ),?_⟩
    convert hit using 1 <;> ring

/-- M-periodicity of both input coordinates, despite testing a square modulo 2M. -/
theorem periodic {n M h d : ℤ} (even : 2∣M) (u v : ℤ) :
    Compatible n M (h+M*u) (d+M*v) ↔ Compatible n M h d := by
  obtain ⟨s,rfl⟩ := even
  have expand : (h+2*s*u)^2-(d+2*s*v)^2-n =
    (h^2-d^2-n)+(2*(2*s))*(h*u-d*v+s*(u^2-v^2)) := by ring
  unfold Compatible; rw [expand,dvd_add_left (dvd_mul_right _ _)]

/-- Looking only at the midpoint recovers precisely the usual square-discriminant test at 2M. -/
theorem midpoint_projection (n h : ℤ) (M : ℕ) (pos : 0<M) :
    (∃ d : ℤ, Compatible n M h d) ↔ IsSquare (((h^2-n : ℤ) : ZMod (2*M))) := by
  letI : NeZero (2*M) := ⟨by omega⟩
  constructor
  · rintro ⟨d,hd⟩
    have div : (((2*M:ℕ):ℤ)) ∣ h^2-d^2-n := by simpa using hd
    have z := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr div
    refine ⟨(d:ZMod (2*M)),?_⟩
    push_cast at z ⊢
    linear_combination z
  · rintro ⟨r,hr⟩
    refine ⟨r.val,?_⟩
    have z : (((h^2-(r.val:ℤ)^2-n : ℤ) : ZMod (2*M))) = 0 := by
      push_cast at hr ⊢
      rw [ZMod.natCast_zmod_val]
      linear_combination hr
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp z

/-- The gap projection likewise coincides with the exact square test on that coordinate. -/
theorem gap_projection (n d : ℤ) (M : ℕ) (pos : 0<M) :
    (∃ h : ℤ, Compatible n M h d) ↔ IsSquare (((d^2+n : ℤ) : ZMod (2*M))) := by
  have swapped (h : ℤ) : Compatible n M h d ↔ Compatible (-n) M d h := by
    unfold Compatible
    rw [show d^2-h^2- -n = -(h^2-d^2-n) by ring,dvd_neg]
  simpa only [sub_neg_eq_add] using (exists_congr swapped).trans (midpoint_projection (-n) d M pos)

/-- If r is the proposed factor remainder h−d mod M, the joint check is a linear
congruence for h. For an odd r modulo a power of two its coefficient is a unit. -/
theorem factor_residue_iff {n M h d r c : ℤ} (even : 2∣M) (residue : M∣h-d-r)
    (half : n+r^2=2*c) : Compatible n M h d ↔ M ∣ r*h-c := by
  obtain ⟨k,hk⟩ := residue
  obtain ⟨s,rfl⟩ := even
  have deq : d=h-r-2*s*k := by linarith only [hk]
  have expand : h^2-d^2-n=2*((r*h-c)+(2*s)*(k*(h-r)-s*k^2)) := by
    rw [deq]; linear_combination -half
  unfold Compatible
  rw [expand,mul_dvd_mul_iff_left (by decide : (2:ℤ)≠0),dvd_add_left (dvd_mul_right _ _)]

/-- Finite canonical representatives for the joint midpoint and signed half-gap. -/
noncomputable def states (n : ℤ) (M : ℕ) :=
  univ.filter (fun v : Fin M × Fin M => Compatible n M (v.1:ℕ) (v.2:ℕ))

private noncomputable def combine (M : ℕ) : ((Fin M × Fin M) × (Fin 2 × Fin 2)) ≃ (Fin (2*M) × Fin (2*M)) :=
  ((Equiv.prodComm _ _).trans (Equiv.prodProdProdComm _ _ _ _)).trans (finProdFinEquiv.prodCongr finProdFinEquiv)

theorem count_double (n : ℤ) (M : ℕ) (odd : (n:ZMod 2)=1) (pos : 0<M) (four : 4∣M) :
    (states n (2*M)).card = 2*(states n M).card := by
  classical
  let P (v : Fin (2*M) × Fin (2*M)) := Compatible n (2*M:ℕ) (v.1:ℕ) (v.2:ℕ)
  let pred (x : Fin M × Fin M) (b : Fin 2 × Fin 2) := P (combine M (x,b))
  let e := (Equiv.subtypeEquivOfSubtype (p:=P) (combine M)).symm.trans (Equiv.subtypeProdEquivSigmaSubtype pred)
  calc
    _ = Fintype.card {v // P v} := (Fintype.card_subtype P).symm
    _ = ∑ x, (univ.filter (pred x)).card := by simp only [Fintype.card_congr e,Fintype.card_sigma,Fintype.card_subtype]
    _ = ∑ x : Fin M × Fin M, if Compatible n M (x.1:ℕ) (x.2:ℕ) then 2 else 0 := by
      apply sum_congr rfl; intro x _
      have h := child_count (h:=(x.1:ℕ)) (d:=(x.2:ℕ)) odd (show 0<(M:ℤ) by exact_mod_cast pos)
        (show (4:ℤ)∣(M:ℤ) by exact_mod_cast four)
      convert h using 1
    _ = _ := by rw [←sum_filter]; simp [states,Nat.mul_comm]

private theorem base_four (n : ℤ) (odd : (n:ZMod 2)=1) : (states n 4).card=2 := by
  have same : states n 4 = states (n%8) 4 := by
    ext v
    simp only [states,mem_filter,mem_univ,true_and,Compatible]
    change 8 ∣ _ ↔ 8 ∣ _
    omega
  have parity : 2∣n-1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp (by push_cast; rw [odd]; simp)
  have small : n%8=1 ∨ n%8=3 ∨ n%8=5 ∨ n%8=7 := by omega
  rw [same]
  rcases small with h|h|h|h <;> rw [h] <;> decide +kernel

/-- At modulus M=2^(e+2), precisely M/2 joint pairs survive, for every odd target. -/
theorem count (n : ℤ) (odd : (n:ZMod 2)=1) (e : ℕ) :
    (states n (2^(e+2))).card=2^(e+1) := by
  induction e with
  | zero => exact base_four n odd
  | succ e ih =>
    have four : 4 ∣ 2^(e+2) := pow_dvd_pow 2 (show 2≤e+2 by omega)
    rw [show 2^(e+1+2)=2*(2^(e+2)) by ring,count_double n _ odd (by positivity) four,ih]
    ring

/-- An example for the full independent marginal filters on the same target, at the same precision. -/
theorem example_77 : (states 77 64).card=32 ∧ ((states 77 64).image Prod.fst).card=8 ∧
    ((states 77 64).image Prod.snd).card=16 ∧
    (7 : Fin 64) ∈ (states 77 64).image Prod.fst ∧
    ((7,2) : Fin 64 × Fin 64) ∉ states 77 64 ∧ ((9,2) : Fin 64 × Fin 64) ∈ states 77 64 := by
  decide +kernel

end PrimeFactors.DyadicSumGap
