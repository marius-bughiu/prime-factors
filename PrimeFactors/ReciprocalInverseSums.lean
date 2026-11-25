import PrimeFactors.StationaryRadixLimit
import PrimeFactors.Fermat
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.Tactic.NormNum.Prime

/-! Public factor-sum candidates from modular inverse reciprocity. -/

namespace PrimeFactors.ReciprocalInverseSums

theorem reciprocity {p q u v : ℕ} (cop : p.Coprime q) (hp : 1 < p) (hq : 1 < q)
    (hu : 0 < u) (uq : u < q) (hv : 0 < v) (vp : v < p)
    (iu : p*u ≡ 1 [MOD q]) (iv : q*v ≡ 1 [MOD p]) :
    p*u + q*v = p*q+1 := by
  have zp : p*u ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right ..)
  have zq : q*v ≡ 0 [MOD q] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right ..)
  have h := (Nat.modEq_and_modEq_iff_modEq_mul cop).mp
    ⟨show p*u+q*v ≡ 1 [MOD p] by simpa using zp.add iv,
     show p*u+q*v ≡ 1 [MOD q] by simpa using iu.add zq⟩
  have lower : 1 < p*u+q*v := by nlinarith only [hp, Nat.mul_le_mul_left p hu, Nat.mul_le_mul_left q hv]
  have upper : p*u+q*v < 2*(p*q) := by
    nlinarith only [Nat.mul_lt_mul_of_pos_left uq (by omega : 0<p),
      Nat.mul_lt_mul_of_pos_left vp (by omega : 0<q)]
  have lower' := h.symm.add_le_of_lt lower
  have same : p*u+q*v ≡ p*q+1 [MOD p*q] := h.trans (by simp [Nat.ModEq])
  exact Nat.le_antisymm (same.le_of_lt_add (by omega)) (by omega)

/-- For a zero difference, divisibility by the sum is both necessary and sufficient. -/
theorem equal_iff_sum_dvd {p q u v : ℕ} (cop : p.Coprime q) (uq : u < q)
    (vp : v < p) (relation : p*u+q*v=p*q+1) : u=v ↔ p+q ∣ p*q+1 := by
  constructor
  · rintro rfl
    exact ⟨u, by nlinarith only [relation]⟩
  · intro div
    have z : p*u+q*v ≡ 0 [MOD p+q] := Nat.modEq_zero_iff_dvd.mpr (relation ▸ div)
    have zz : p*v+q*v ≡ 0 [MOD p+q] := Nat.modEq_zero_iff_dvd.mpr ⟨v, by ring⟩
    have h : p*u ≡ p*v [MOD p+q] := Nat.ModEq.add_right_cancel' _ (z.trans zz.symm)
    exact (Nat.ModEq.cancel_left_of_coprime (Nat.coprime_self_add_right.mpr cop).symm h
      ).eq_of_lt_of_lt (by omega) (by omega)

/-- The product-only divisor and the smaller fixed-p divisor, with the signed convention e=u-v. -/
theorem signed_divisors {p q u v : ℤ} (rel : p*u+q*v=p*q+1) :
    p+q ∣ (p*q+1)^2 + p*q*(u-v)^2 ∧ p+q ∣ p^2+(u-v)*p-1 := by
  constructor
  · refine ⟨(p+q)*v^2+2*v*p*(u-v)+p*(u-v)^2, ?_⟩
    rw [←rel]
    ring
  · refine ⟨p-v, ?_⟩
    linear_combination rel

/-- Odd factors have an even signed difference, including when one inverse is larger. -/
theorem even_difference {p q u v : ℤ} (hp : Odd p) (hq : Odd q)
    (rel : p*u+q*v=p*q+1) : Even (u-v) := by
  obtain ⟨a, rfl⟩ := hp
  obtain ⟨b, rfl⟩ := hq
  refine ⟨2*a*b+a+b+1-a*u-b*v-v, ?_⟩
  linear_combination rel

/-- Extract only the powers of the predetermined bases dividing N+1. -/
def smoothPart : List ℕ → ℕ → ℕ
  | [], _ => 1
  | p :: rest, n => p^(p.maxPowDiv (n+1)) * smoothPart rest n

/-- Check the single extracted sum on the band for p ≤ q ≤ 2p. -/
def checkSum (n s : ℕ) : Option (ℕ × ℕ) := Id.run do
  if s%2 ≠ 0 ∨ s^2 < 4*n ∨ 9*n < 2*s^2 then return none
  let z := (s^2-4*n).sqrt
  if z^2 ≠ s^2-4*n then return none
  let p := (s-z)/2
  let q := (s+z)/2
  if 1<p ∧ p*q=n then return some (p,q)
  return none

/-- The public acceptance band includes every balanced odd pair, at both ends. -/
theorem check_true_sum {p q : ℕ} (hp : 1 < p) (le : p≤q) (balanced : q ≤ 2*p)
    (par : Even (p+q)) : checkSum (p*q) (p+q) = some (p,q) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le le
  have parity : (p+(p+d))%2=0 := Nat.even_iff.mp par
  have band : 2*(p+(p+d))^2 ≤ 9*(p*(p+d)) := by
    have b : d ≤ p := by omega
    nlinarith only [Nat.mul_le_mul_right (p+2*d) b]
  have gap : (p+(p+d))^2 = 4*(p*(p+d))+d^2 := by ring
  have e : (p+(p+d))^2-4*(p*(p+d))=d^2 := by omega
  have h : ¬ (p+(p+d))^2 < 4*(p*(p+d)) := by omega
  simp [checkSum, Id.run, parity, h, not_lt.mpr band, e, Nat.sqrt_eq', hp, show (p+(p+d)-d)/2=p by omega,
    show (p+(p+d)+d)/2=p+d by omega]

open StationaryRadixLimit in
/-- For a smooth factor sum, each possible smaller factor is one of a few square roots of one. -/
theorem smooth_sum_card {s : ℕ} (hs : 0<s) (support : s.primeFactors ⊆ {2,3})
    (candidates : Finset ℕ) (valid : ∀ p ∈ candidates, p<s ∧ p^2 ≡ 1 [MOD s]) :
    candidates.card ≤ 8 := by
  classical
  haveI : NeZero s := ⟨hs.ne'⟩
  let embed (x : candidates) : Roots s := by
    let p := x.val
    have root : (p : ZMod s)^2=1 := by
      simpa using (ZMod.natCast_eq_natCast_iff (x.val^2) 1 s).mpr (valid _ x.property).2
    let u : (ZMod s)ˣ := ⟨p,p,by simpa [sq] using root,by simpa [sq] using root⟩
    exact ⟨u, Units.ext (by simpa [u] using root)⟩
  have inject : Function.Injective embed := by
    intro x y equal
    apply Subtype.ext
    have eqcast : (x.val : ZMod s) = y.val :=
      congrArg (fun t : Roots s => (t.val : ZMod s)) equal
    exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp eqcast).eq_of_lt_of_lt
      (valid _ x.property).1 (valid _ y.property).1
  have count := (Nat.card_le_card_of_injective embed inject).trans (roots_le hs)
  have sz : s.primeFactors.card ≤ 2 := (Finset.card_le_card support).trans (by decide)
  simpa using count.trans (show 2^(s.primeFactors.card+1) ≤ 2^3 by gcongr <;> omega)

/-- A dyadic band fixes the power of two as soon as the odd part is fixed. -/
theorem dyadic_unique {L m a b : ℕ}
    (a0 : L ≤ 2^a*m) (a1 : 2^a*m < 2*L) (b0 : L ≤ 2^b*m) (b1 : 2^b*m < 2*L) :
    a=b := by
  have step {i j : ℕ} (less : i<j) : 2*(2^i*m) ≤ 2^j*m := by
    have h := Nat.mul_le_mul_right m (Nat.pow_le_pow_right (by decide : 0<2) less)
    simpa [pow_succ, Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_comm] using h
  rcases lt_trichotomy a b with h|h|h
  · have hh := step h
    omega
  · exact h
  · have hh := step h
    omega

set_option exponentiation.threshold 2048 in
/-- The entire 1,024-bit prime-pair range admits at most 647 such smooth sums. -/
theorem dyadic_sums_card (sums : Finset ℕ) (valid : ∀ s ∈ sums,
    2^1024≤s ∧ s<2^1025 ∧ ∃ a b : ℕ, s=2^a*3^b) : sums.card ≤ 647 := by
  classical
  choose a b h using fun (s : sums) => (valid s s.property).2.2
  have cap : 2^1025 < 3^647 := by norm_num1
  have size (s : sums) : b s < 647 := by
    have le : 3^(b s) ≤ s.val := by
      rw [h s]
      exact Nat.le_mul_of_pos_left _ (by positivity)
    apply lt_of_not_ge
    intro no
    have too := Nat.pow_le_pow_right (by decide : 0<3) no
    exact (not_lt_of_ge (le_trans too le)) (lt_trans (valid s s.property).2.1 cap)
  let f (s : sums) : Fin 647 := ⟨b s,size s⟩
  have inj : Function.Injective f := by
    intro s t same
    have eqb : b s=b t := congrArg Fin.val same
    obtain ⟨s0,s1,_⟩ := valid s s.property
    obtain ⟨t0,t1,_⟩ := valid t t.property
    rw [h s,eqb] at s0 s1
    rw [h t] at t0 t1
    have two : (2:ℕ)^1025=2*(2^1024) := pow_succ' 2 1024
    rw [two] at s1 t1
    have eqa := dyadic_unique s0 s1 t0 t1
    exact Subtype.ext ((h s).trans (by rw [eqb,eqa,←h t]))
  simpa using Fintype.card_le_of_injective f inj

/-- Equal inverses imply that the smaller factor belongs to the square-root menu for this sum. -/
theorem root_of_sum {p q : ℕ} (sum : p+q ∣ p*q+1) : p^2 ≡ 1 [MOD p+q] := by
  obtain ⟨k, hk⟩ := sum
  apply Nat.modEq_iff_dvd.mpr
  refine ⟨(k:ℤ)-p, ?_⟩
  push_cast
  have cast : (p:ℤ)*q+1 = (p+q)*k := by exact_mod_cast hk
  linear_combination cast

theorem sum_dvd_iff_root {p q : ℕ} : p+q ∣ p*q+1 ↔ p^2 ≡ 1 [MOD p+q] := by
  refine ⟨root_of_sum, fun root => ?_⟩
  obtain ⟨k,hk⟩ := root.dvd
  rw [←Nat.modEq_zero_iff_dvd, Nat.modEq_iff_dvd]
  refine ⟨-(p:ℤ)-k, ?_⟩
  push_cast at *
  linear_combination -hk

/-- The public resultant is always one modulo the product. -/
theorem resultant_neighbor (n e : ℤ) : (n+1)^2+n*e^2=n*(n+2+e^2)+1 := by ring

private theorem support_two_three {s : ℕ} (smooth : ∃ a b : ℕ, s=2^a*3^b) :
    s.primeFactors ⊆ {2,3} := by
  obtain ⟨a,b,rfl⟩ := smooth
  intro l hl
  obtain ⟨hp,hd,_⟩ := Nat.mem_primeFactors.mp hl
  rcases hp.dvd_mul.mp hd with h|h
  · have e := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
    simp [e]
  · have e := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)
    simp [e]

private abbrev sumOf (x : ℕ × ℕ) := x.1+x.2

private def SmoothSum (p q : ℕ) : Prop :=
  2^1024 ≤ p+q ∧ p+q < 2^1025 ∧ (∃ a b : ℕ, p+q=2^a*3^b) ∧ p+q ∣ p*q+1

private theorem oriented_card (pairs : Finset (ℕ × ℕ)) (valid : ∀ x ∈ pairs,
    0<x.2 ∧ SmoothSum x.1 x.2) : pairs.card ≤ 5176 := by
  classical
  let sums := pairs.image sumOf
  have sumInfo s (hs : s ∈ sums) : 2^1024≤s ∧ s<2^1025 ∧ ∃ a b : ℕ, s=2^a*3^b := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨_,lo,hi,sm,_⟩ := valid x hx
    exact ⟨lo,hi,sm⟩
  have each s (hs : s ∈ sums) : (pairs.filter fun x => sumOf x=s).card ≤ 8 := by
    let fiber := pairs.filter fun x => sumOf x=s
    have inject : Set.InjOn (Prod.fst : ℕ × ℕ → ℕ) fiber.toSet := by
      rintro ⟨p,q⟩ hp ⟨r,t⟩ hr e
      obtain ⟨_,hq⟩ := Finset.mem_filter.mp hp
      obtain ⟨_,ht⟩ := Finset.mem_filter.mp hr
      simp only [sumOf] at hq ht
      change p=r at e
      exact Prod.ext e (by omega)
    rw [←Finset.card_image_of_injOn inject]
    obtain ⟨lo,_,smooth⟩ := sumInfo s hs
    apply smooth_sum_card (lt_of_lt_of_le (by positivity) lo) (support_two_three smooth)
    intro p hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hx,eq⟩ := Finset.mem_filter.mp hx
    obtain ⟨hq,_,_,_,div⟩ := valid x hx
    subst s
    exact ⟨by unfold sumOf; omega, root_of_sum div⟩
  calc
    pairs.card = ∑ s ∈ sums, (pairs.filter fun x => sumOf x=s).card :=
      Finset.card_eq_sum_card_image ..
    _ ≤ ∑ _ ∈ sums, 8 := Finset.sum_le_sum each
    _ ≤ 5176 := by simpa using Nat.mul_le_mul_right 8 (dyadic_sums_card sums sumInfo)

/-- In the full permitted sum band, the fixed-support equal-inverse family admits at most
2,588 unordered pairs. The inequality already allows composite factors. -/
theorem fixed_support_card (pairs : Finset (ℕ × ℕ)) (valid : ∀ x ∈ pairs,
    0<x.1 ∧ x.1<x.2 ∧ 2^1024≤x.1+x.2 ∧ x.1+x.2<2^1025 ∧
    (∃ a b : ℕ, x.1+x.2=2^a*3^b) ∧ x.1+x.2 ∣ x.1*x.2+1) : pairs.card ≤ 2588 := by
  classical
  have disjoint : Disjoint pairs (pairs.image Prod.swap) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨y,hy0,rfl⟩ := Finset.mem_image.mp hy
    have h := (valid _ hx).2.1
    exact (not_lt_of_gt (valid _ hy0).2.1) h
  have bound := oriented_card (pairs ∪ pairs.image Prod.swap) (by
    intro x hx
    rcases Finset.mem_union.mp hx with h|h
    · obtain ⟨pos,lt,h⟩ := valid x h
      exact ⟨pos.trans lt,h⟩
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨pos,_,info⟩ := valid y hy
      exact ⟨pos,by change SmoothSum y.2 y.1; unfold SmoothSum; rw [Nat.add_comm y.2 y.1,Nat.mul_comm y.2 y.1]; exact info⟩)
  rw [Finset.card_union_of_disjoint disjoint,
    Finset.card_image_of_injective _ (fun _ _ h => Prod.swap_injective h)] at bound
  omega

/-- The first parity-compatible trace for the given ordered weights. -/
def initialWeightedTrace (n a b : ℕ) : ℕ :=
  let t := PrimeFactors.ceilSqrt (4*a*b*n)
  t + ((a+b+t)%2)

def firstWeightedMiss (n a b : ℕ) : Bool :=
  let t := initialWeightedTrace n a b
  let d := t^2-4*a*b*n
  decide (d.sqrt^2 ≠ d)

private theorem exponent_of_factor {p r : ℕ} (a : ℕ) (hp : 1<p) (hr : 0<r)
    (cop : r%p≠0) : p.maxPowDiv (p^a*r) = a := by
  rw [Nat.maxPowDiv.base_pow_mul hp hr]
  have zero : p.maxPowDiv r=0 := by
    unfold Nat.maxPowDiv
    rw [Nat.maxPowDiv.go, if_neg (by tauto)]
  omega

private theorem exponent_at {p n r : ℕ} (a : ℕ) (e : n=p^a*r) (hp : 1<p) (hr : 0<r)
    (cop : r%p≠0) : p.maxPowDiv n = a := e ▸ exponent_of_factor a hp hr cop

private theorem rounded_eq {n c : ℕ} (lo : c^2<n) (hi : n≤(c+1)^2) :
    PrimeFactors.ceilSqrt n = c+1 := by
  have above : ¬ PrimeFactors.ceilSqrt n ≤ c := by
    intro h
    exact (not_le_of_gt lo) (PrimeFactors.ceilSqrt_le_iff.mp h)
  have below := PrimeFactors.ceilSqrt_le_iff.mpr hi
  omega

/-- Consecutive-square witnesses for the initial rounded weighted Fermat probes. -/
private def witnesses : ℕ → ℕ × ℕ
  | 1 => (5545429, 2522)
  | 2 => (7842421, 4844)
  | 3 => (9604965, 3049)
  | 4 => (11090858, 1810)
  | 5 => (12399957, 4560)
  | 6 => (13583472, 3690)
  | 7 => (14671827, 4921)
  | 8 => (15684843, 7906)
  | 10 => (17536187, 7031)
  | 12 => (19209931, 8696)
  | 14 => (20749096, 1017)
  | 15 => (21477355, 2819)
  | 20 => (24799914, 5797)
  | 21 => (25412350, 9810)
  | 24 => (27166944, 391)
  | 28 => (29343654, 6180)
  | 30 => (30373567, 8258)
  | 35 => (32807202, 8431)
  | 40 => (35072375, 11297)
  | 42 => (35938490, 7714)
  | 56 => (41498193, 9334)
  | _ => (0,0)

private def cert (n a b c g : ℕ) : Prop :=
  let t := c+1+((a+b+(c+1))%2)
  let d := t^2-4*a*b*n
  c^2<4*a*b*n ∧ 4*a*b*n≤(c+1)^2 ∧ g^2<d ∧ d<(g+1)^2

private instance (n a b c g : ℕ) : Decidable (cert n a b c g) := by unfold cert; infer_instance

private theorem cert_miss {n a b c g : ℕ} (h : cert n a b c g) : firstWeightedMiss n a b := by
  obtain ⟨lo,hi,below,above⟩ := h
  have trace : initialWeightedTrace n a b = c+1+((a+b+(c+1))%2) := by
    rw [initialWeightedTrace, rounded_eq lo hi]
  simp only [firstWeightedMiss, trace, decide_eq_true_eq]
  let d := (c+1+((a+b+(c+1))%2))^2-4*a*b*n
  change d.sqrt^2 ≠ d
  change g^2<d at below
  change d<(g+1)^2 at above
  have same : d.sqrt=g := le_antisymm (Nat.le_of_lt_succ (Nat.sqrt_lt'.mpr above))
    (Nat.le_sqrt'.mpr below.le)
  rw [same]
  exact below.ne

private theorem first_trace_certificates : ∀ a b : Fin 8, (a.val+1).Coprime (b.val+1) →
    let pair := witnesses ((a.val+1)*(b.val+1))
    cert 7687946879999 (a.val+1) (b.val+1) pair.1 pair.2 := by decide

theorem three_prime_toy_initial_misses (a b : Fin 8) (cop : (a.val+1).Coprime (b.val+1)) :
    firstWeightedMiss 7687946879999 (a.val+1) (b.val+1) :=
  cert_miss (first_trace_certificates a b cop)

theorem separated_toy :
    smoothPart [2,3] 8590000127 = 196608 ∧
    checkSum 8590000127 196608 = some (65537,131071) ∧
    Nat.Prime 65537 ∧ Nat.Prime 131071 ∧
    98304+1-PrimeFactors.ceilSqrt 8590000127 = 5622 := by
  refine ⟨?_, ?_, by norm_num, by norm_num, ?_⟩
  · have two := exponent_at (p:=2) (n:=8590000127+1) (r:=131073) 16 (by decide)
      (by decide) (by decide) (by decide)
    have three := exponent_at (p:=3) (n:=8590000127+1) (r:=2863333376) 1 (by decide)
      (by decide) (by decide) (by decide)
    norm_num [smoothPart, two, three]
  · rw [show 8590000127=65537*131071 by decide, show 196608=65537+131071 by decide]
    exact check_true_sum (by decide) (by decide) (by decide) (by decide)
  · rw [rounded_eq (c:=92682) (by decide) (by decide)]

theorem three_prime_toy :
    smoothPart [2,3,5] 7687946879999 = 5760000 ∧
    checkSum 7687946879999 5760000 = some (2101249,3658751) ∧
    Nat.Prime 2101249 ∧ Nat.Prime 3658751 ∧
    2880000+1-PrimeFactors.ceilSqrt 7687946879999 = 107286 := by
  refine ⟨?_, ?_, by norm_num, by norm_num, ?_⟩
  · have two := exponent_at (p:=2) (n:=7687946879999+1) (r:=7507760625) 10 (by decide)
      (by decide) (by decide) (by decide)
    have three := exponent_at (p:=3) (n:=7687946879999+1) (r:=854216320000) 2 (by decide)
      (by decide) (by decide) (by decide)
    have five := exponent_at (p:=5) (n:=7687946879999+1) (r:=12300715008) 4 (by decide)
      (by decide) (by decide) (by decide)
    norm_num [smoothPart, two, three, five]
  · rw [show 7687946879999=2101249*3658751 by decide, show 5760000=2101249+3658751 by decide]
    exact check_true_sum (by decide) (by decide) (by decide) (by decide)
  · rw [rounded_eq (c:=2772714) (by decide) (by decide)]

end PrimeFactors.ReciprocalInverseSums
