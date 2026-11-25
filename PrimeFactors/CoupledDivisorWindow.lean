import PrimeFactors.HigherDivisorWindow
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Nat.Sqrt

namespace PrimeFactors.CoupledDivisorWindow

open Polynomial HigherDivisorWindow

/-- The least integer at least N/2^1024. -/
def lower (n : ℕ) := (n+2^1024-1)/2^1024

/-- The least integer at least √N for positive N. -/
def largerLower (n : ℕ) := (n-1).sqrt+1

theorem product_le (n : ℕ) : n≤2^1024*lower n :=
  (ceilDiv_le_iff_le_mul (by positivity : 0<(2:ℕ)^1024)).mp
    (show n ⌈/⌉ (2:ℕ)^1024 ≤ lower n from le_rfl)

theorem lower_le_factor {n d q : ℕ} (pair : n=d*q) (cap : q≤2^1024) : lower n≤d := by
  apply (ceilDiv_le_iff_le_mul (by positivity : 0<(2:ℕ)^1024)).mpr
  rw [pair,Nat.mul_comm d]
  exact Nat.mul_le_mul_right d cap

theorem lower_size {n : ℕ} (large : 2^2047≤n) : 2^1023≤lower n := by
  have main := large.trans (product_le n)
  rw [show (2:ℕ)^2047=2^1024*2^1023 from by rw [← pow_add]] at main
  exact Nat.le_of_mul_le_mul_left main (by positivity)

theorem product_square (n : ℕ) : n≤(largerLower n)^2 := by
  have h := Nat.lt_succ_sqrt' (n-1)
  simp only [Nat.succ_eq_add_one] at h
  unfold largerLower
  omega

theorem larger_le_factor {n d q : ℕ} (hn : 0<n) (pair : n=d*q) (ord : q≤d) :
    largerLower n≤d := by
  apply Nat.succ_le_of_lt
  apply Nat.sqrt_lt'.mpr
  have le : n≤d^2 := by rw [pair,pow_two]; exact Nat.mul_le_mul_left d ord
  omega

private abbrev T (m : ℕ) := m+m.choose 2
private abbrev B (r : ℕ) := r.choose 2

private def boxCost (r w : ℕ) := r^r * ((2:ℕ)^w)^(B r)
private def lllCost (r w : ℕ) := r^(2*r)*(2:ℕ)^((r-1)*r)*(((2:ℕ)^w)^(B r))^4

private theorem box_bound {r h : ℕ} (dim : r≤2^h) (w : ℕ) :
    boxCost r w < 2^(h*r+w*(B r)+1) := by
  apply (Nat.mul_le_mul_right (((2:ℕ)^w)^(B r)) (Nat.pow_le_pow_left dim r)).trans_lt
  rw [← pow_mul,← pow_mul,← pow_add]
  exact Nat.pow_lt_pow_right (by decide) (by omega)

private theorem lll_bound {r e : ℕ} (dim : r^(2*r)<2^e) (w : ℕ) :
    lllCost r w < 2^(e+(r-1)*r+4*w*(B r)) := by
  unfold lllCost
  calc
    _ < (2:ℕ)^e*2^((r-1)*r)*((2^w)^(B r))^4 :=
      Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right dim (by positivity)) (by positivity)
    _ = _ := by simp only [← pow_mul,← pow_add]; congr 1; ring

/-- Transfer a single exponent calculation to every public input using N≤2^1024 D.
The extra D^t from N^t cancels t of the c powers available at the target. -/
private theorem coupled_cost {n a e t c : ℕ} (large : 2^2047≤n)
    (cheap : a<2^e) (tc : t≤c) (budget : e+2047*t≤1023*c) :
    a*n^t < (lower n)^c := by
  have room : (2:ℕ)^e*(2^1024)^t ≤ (lower n)^(c-t) := calc
    _ = 2^(e+1024*t) := by rw [pow_add,pow_mul]
    _ ≤ 2^(1023*(c-t)) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = ((2:ℕ)^1023)^(c-t) := pow_mul _ _ _
    _ ≤ _ := Nat.pow_le_pow_left (lower_size large) _
  have pos : 0<lower n := (by positivity : 0<(2:ℕ)^1023).trans_le (lower_size large)
  calc
    _ ≤ a*(2^1024*lower n)^t := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (product_le n) _)
    _ = (a*(2^1024)^t)*(lower n)^t := by rw [mul_pow,mul_assoc]
    _ < (lower n)^(c-t)*(lower n)^t := Nat.mul_lt_mul_of_pos_right
      ((Nat.mul_lt_mul_of_pos_right cheap (by positivity)).trans_le room) (pow_pos pos _)
    _ = _ := by rw [← pow_add,Nat.sub_add_cancel tc]

/-- For the larger factor, N≤D² and N≥2^2047. Squaring the desired bound avoids
any rounding loss in the half-bit at the bottom of the input range. -/
private theorem larger_cost {n a e t c : ℕ} (large : 2^2047≤n)
    (cheap : a<2^e) (tc : 2*t≤c) (budget : 2*e+2*2047*t≤2047*c) :
    a*n^t < (largerLower n)^c := by
  have positive : 0<n := (by positivity : 0<(2:ℕ)^2047).trans_le large
  have one : a^2 < n^(c-2*t) := calc
    _ < ((2:ℕ)^e)^2 := Nat.pow_lt_pow_left cheap (by decide)
    _ = 2^(2*e) := by rw [← pow_mul,Nat.mul_comm e]
    _ ≤ 2^(2047*(c-2*t)) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = ((2:ℕ)^2047)^(c-2*t) := pow_mul _ _ _
    _ ≤ _ := Nat.pow_le_pow_left large _
  have goal : (a*n^t)^2 < ((largerLower n)^c)^2 := calc
    _ = a^2*n^(2*t) := by rw [mul_pow,← pow_mul,Nat.mul_comm t]
    _ < n^(c-2*t)*n^(2*t) := Nat.mul_lt_mul_of_pos_right one (pow_pos positive _)
    _ = n^c := by rw [← pow_add,Nat.sub_add_cancel tc]
    _ ≤ ((largerLower n)^2)^c := Nat.pow_le_pow_left (product_square n) _
    _ = _ := by rw [← pow_mul,← pow_mul,Nat.mul_comm 2]
  by_contra! ge
  exact (not_lt_of_ge (Nat.pow_le_pow_left ge 2)) goal

/-- Bit costs for equal-width factors with publicly bounded cofactor. -/
def Scale (m r w h e : ℕ) : Prop :=
  0<r ∧ w≤1021 ∧ r≤2^h ∧ r^(2*r)<2^e ∧ T m≤m*r ∧
  (h*r+w*B r+1)+2047*T m≤1023*(m*r) ∧
  (e+(r-1)*r+4*w*B r)+2047*(4*T m)≤1023*(4*(m*r))

/-- Bit costs for targeting the larger of the two equal-width factors. -/
def LargerScale (m r w h e : ℕ) : Prop :=
  0<r ∧ w≤1021 ∧ r≤2^h ∧ r^(2*r)<2^e ∧ 2*T m≤m*r ∧
  2*(h*r+w*B r+1)+2*2047*T m≤2047*(m*r) ∧
  2*(e+(r-1)*r+4*w*B r)+2*2047*(4*T m)≤2047*(4*(m*r))

/-- Both bounds use the actual input N and the actual public divisor threshold D. -/
def Room (n D m r w : ℕ) : Prop :=
  n^(T m)*(r^r*((2:ℕ)^w)^(B r)) < (D^m)^r ∧
  r^(2*r)*(2:ℕ)^((r-1)*r)*(n^(T m)*((2:ℕ)^w)^(B r))^4 < (D^m)^(4*r)

private theorem room_of_costs {n D m r w : ℕ}
    (box : boxCost r w*n^(T m) < D^(m*r))
    (lll : lllCost r w*n^(4*T m) < D^(4*(m*r))) : Room n D m r w := by
  constructor
  · simpa only [boxCost,Nat.mul_comm,← pow_mul] using box
  · calc
      _ = lllCost r w*n^(4*T m) := by unfold lllCost; rw [mul_pow,pow_mul]; ring
      _ < D^(4*(m*r)) := lll
      _ = _ := by simp only [← pow_mul]; congr 1; ring

theorem scale_room {n m r w h e : ℕ} (large : 2^2047≤n) (sc : Scale m r w h e) :
    Room n (lower n) m r w := by
  obtain ⟨_,_,dim,cost,tc,budget,ls⟩ := sc
  apply room_of_costs (coupled_cost large (box_bound dim w) tc budget)
  exact coupled_cost large (lll_bound cost w) (by omega) ls

theorem larger_scale_room {n m r w h e : ℕ} (large : 2^2047≤n) (sc : LargerScale m r w h e) :
    Room n (largerLower n) m r w := by
  obtain ⟨_,_,dim,cost,tc,budget,ls⟩ := sc
  apply room_of_costs (larger_cost large (box_bound dim w) tc budget)
  exact larger_cost large (lll_bound cost w) (by omega) ls

private theorem odd_anchor (n c : ℕ) (hn : Odd n) (hc : Odd c) :
    (n:ℤ) ∣ (c:ℤ)+2*QuarticDivisorWindow.oddAnchor n c := by
  obtain ⟨a,ha⟩ := hn
  obtain ⟨b,hb⟩ := hc
  refine ⟨1,?_⟩
  unfold QuarticDivisorWindow.oddAnchor
  omega

/-- Polynomial and root count at a prescribed odd center. -/
def At (n D r w c : ℕ) : Prop :=
  ∃ F : ℤ[X], F≠0 ∧ F.roots.toFinset.card<r ∧ ∀ x d : ℤ, d∣(n:ℤ) →
    d=(c:ℤ)+2*x → (D:ℤ)≤d → |x|≤(2:ℤ)^w → F.eval x=0

private theorem at_threshold {n D m r w : ℕ} (hn : 0<n) (parity : Odd n)
    (hd : 0<D) (hr : 0<r) (room : Room n D m r w) (c : ℕ) (hc : Odd c) : At n D r w c := by
  let t := QuarticDivisorWindow.oddAnchor n c
  obtain ⟨v,nz,jets,short⟩ := relation_exists hr hn (by positivity) hd room.1 t
  refine ⟨ofFn r v,nz,(Multiset.toFinset_card_le _).trans_lt ((card_roots' _).trans_lt
    (ofFn_natDegree_lt hr v)),?_⟩
  intro x d divisor point lowerBound near
  have unit : IsCoprime (2:ℤ) (n:ℤ) := by exact_mod_cast (Nat.coprime_two_left.mpr parity).isCoprime
  apply root_of_divisor jets divisor (QuarticDivisorWindow.progression_offset unit
    (odd_anchor n c parity hc) divisor point)
  · exact_mod_cast near
  · exact short.trans_le (pow_le_pow_left₀ (Int.natCast_nonneg _) lowerBound _)

theorem at_center {n m r w h e : ℕ} (large : 2^2047≤n) (parity : Odd n)
    (sc : Scale m r w h e) (c : ℕ) (hc : Odd c) : At n (lower n) r w c :=
  at_threshold ((by positivity : 0<(2:ℕ)^2047).trans_le large) parity
    ((by positivity : 0<(2:ℕ)^1023).trans_le (lower_size large)) sc.1
    (scale_room large sc) c hc

theorem at_larger_center {n m r w h e : ℕ} (large : 2^2047≤n) (parity : Odd n)
    (sc : LargerScale m r w h e) (c : ℕ) (hc : Odd c) : At n (largerLower n) r w c :=
  at_threshold ((by positivity : 0<(2:ℕ)^2047).trans_le large) parity
    (Nat.succ_pos _) sc.1 (larger_scale_room large sc) c hc

/-- The entire public family covers all odd divisors in the band that satisfy D≤d. -/
def Cover (n D r w : ℕ) : Prop :=
  ∃ F : Fin (2^(1021-w)) → ℤ[X], (∀ i, F i≠0 ∧ (F i).roots.toFinset.card<r) ∧
    ∀ d : ℕ, Odd d → 2^1023≤d → d<2^1024 → D≤d → d∣n →
      ∃ i : Fin (2^(1021-w)), ∃ x : ℤ,
        (d:ℤ)=center w i+2*x ∧ |x|≤(2:ℤ)^w ∧ x∈(F i).roots.toFinset

private theorem whole {n D r w : ℕ} (width : w≤1021) (atC : ∀ c : ℕ, Odd c → At n D r w c) :
    Cover n D r w := by
  classical
  have each (i : Fin (2^(1021-w))) : At n D r w (center w i) := by
    apply atC
    refine ⟨2^1022+(i.val*2^(w+1)+2^w),?_⟩
    have split : (2:ℕ)^1023=2*2^1022 := by rw [pow_succ,Nat.mul_comm]
    unfold center
    omega
  choose F nz count good using each
  refine ⟨F,fun i => ⟨nz i,count i⟩,?_⟩
  intro d odd lo hi bound divisor
  obtain ⟨i,x,point,near⟩ := odd_address width odd lo hi
  refine ⟨i,x,point,near, Multiset.mem_toFinset.mpr ((mem_roots (nz i)).mpr ?_)⟩
  exact good i x d (by exact_mod_cast divisor) point (by exact_mod_cast bound) near

set_option exponentiation.threshold 65536 in
theorem scales : Scale 24 49 500 6 1440 ∧ Scale 347 695 510 10 13186 := by
  simp only [Scale,T,B,Nat.choose_two_right]
  decide +kernel

set_option exponentiation.threshold 65536 in
theorem larger_scales : LargerScale 23 47 500 6 1564 ∧ LargerScale 208 417 510 9 7904 ∧
    LargerScale 1046 2093 511 12 48116 := by
  simp only [LargerScale,T,B,Nat.choose_two_right]
  decide +kernel

theorem target_covers {n : ℕ} (large : 2^2047≤n) (parity : Odd n) :
    Cover n (lower n) 49 500 ∧ Cover n (lower n) 695 510 ∧
    Cover n (largerLower n) 47 500 ∧ Cover n (largerLower n) 417 510 ∧
    Cover n (largerLower n) 2093 511 :=
  ⟨whole scales.1.2.1 (at_center large parity scales.1),
   whole scales.2.2.1 (at_center large parity scales.2),
   whole larger_scales.1.2.1 (at_larger_center large parity larger_scales.1),
   whole larger_scales.2.1.2.1 (at_larger_center large parity larger_scales.2.1),
   whole larger_scales.2.2.2.1 (at_larger_center large parity larger_scales.2.2)⟩

set_option exponentiation.threshold 4096 in
/-- In the largest new windows, the polynomials are chosen before either factor.
All odd equal-width pairs have their larger factor among the covered roots. -/
theorem larger_pairs {n : ℕ} (large : 2^2047≤n) (parity : Odd n) :
    ∃ F : Fin (2^510) → ℤ[X], (∀ i, F i≠0 ∧ (F i).roots.toFinset.card<2093) ∧
    ∀ p q : ℕ, n=p*q → p≤q → 2^1023≤p → q<2^1024 →
      ∃ i : Fin (2^510), ∃ x : ℤ, (q:ℤ)=center 511 i+2*x ∧ |x|≤(2:ℤ)^511 ∧
        x∈(F i).roots.toFinset := by
  obtain ⟨F,checked,covers⟩ := (target_covers large parity).2.2.2.2
  refine ⟨F,checked,?_⟩
  intro p q pair order lo hi
  have hn : 0<n := (by positivity : 0<(2:ℕ)^2047).trans_le large
  have wholeOdd : Odd (p*q) := pair ▸ parity
  have bound := larger_le_factor hn (pair.trans (Nat.mul_comm _ _)) order
  exact covers q (Nat.odd_mul.mp wholeOdd).2 (lo.trans order) hi bound (pair ▸ dvd_mul_left q p)

/-- At w=511 the cofactor-bound exponent fails at the joint endpoint even with no
dimension penalty. Here m is the jet depth and r is the matrix dimension. -/
theorem coupled_511_barrier (m r : ℤ) (hm : 0≤m) :
    4092*m*r ≤ 4094*m*(m+1)+1023*r*(r-1) := by
  let u := r-2*m
  have consecutive : 0≤u*(u-1) := by
    by_cases h : u≤0
    · exact mul_nonneg_of_nonpos_of_nonpos h (by omega)
    · exact mul_nonneg (by omega) (by omega)
  dsimp [u] at consecutive
  nlinarith [sq_nonneg m]

/-- At w=512 even the larger-factor worst-case sufficient budget fails in every
dimension, after omitting the positive square-root-of-dimension penalty. -/
theorem larger_512_barrier (m r : ℤ) (hr : 1≤r) :
    4094*m*r ≤ 4094*m*(m+1)+1025*r*(r-1) := by
  nlinarith [sq_nonneg (r-1-2*m),
    mul_nonneg (show 0≤r-1 by omega) (show 0≤6*r+4094 by omega)]

end PrimeFactors.CoupledDivisorWindow
