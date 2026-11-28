import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Rotating a binary word left by j positions multiplies its residue by 2^j
modulo 2^w−1. The zero and all-ones words share residue zero and are handled
separately. The root sets below specify finite possibilities; their construction
is not assumed to be cheap at large moduli. -/

namespace PrimeFactors.BinaryRotationProduct

open Finset

def modulus (w : ℕ) := 2^w-1

/-- Represent a class by the unique integer in [1,m], choosing m for residue zero. -/
def positiveRep (m x : ℕ) := if x%m=0 then m else x%m

def rotate (w j p : ℕ) :=
  if p=0 then 0 else positiveRep (modulus w) (2^j*p)

private theorem mp {w : ℕ} (hw : 0<w) : 0<modulus w :=
  Nat.sub_pos_of_lt (one_lt_pow₀ (by decide) hw.ne')

private theorem rep_congr {m a b : ℕ} (h : a ≡ b [MOD m]) : positiveRep m a=positiveRep m b := by
  unfold positiveRep
  rw [show a%m=b%m from h]

private theorem rep_modEq (m x : ℕ) : positiveRep m x ≡ x [MOD m] := by
  change (positiveRep m x)%m=x%m
  by_cases h : x%m=0 <;> simp [positiveRep,h]

private theorem rep_bound {m : ℕ} (pm : 0<m) (x : ℕ) : 0<positiveRep m x ∧ positiveRep m x≤m := by
  unfold positiveRep
  split
  · exact ⟨pm,le_rfl⟩
  · exact ⟨by omega,(Nat.mod_lt x pm).le⟩

private theorem rep_id {m x : ℕ} (xp : 0<x) (xm : x≤m) : positiveRep m x=x := by
  rcases xm.eq_or_lt with rfl|up
  · simp [positiveRep]
  · simp [positiveRep,Nat.mod_eq_of_lt up,xp.ne']

private theorem rep_eq {m x y : ℕ} (xp : 0<x) (xm : x≤m) (yp : 0<y) (ym : y≤m)
    (eq : x ≡ y [MOD m]) : x=y := by
  simpa only [rep_id xp xm,rep_id yp ym] using rep_congr eq

theorem rotate_modEq {w p : ℕ} (_hw : 0<w) (j : ℕ) :
    rotate w j p ≡ 2^j*p [MOD modulus w] := by
  by_cases hp : p=0
  · simp [rotate,hp,Nat.ModEq]
  · simpa only [rotate,if_neg hp] using rep_modEq (modulus w) (2^j*p)

theorem rotate_bound {w : ℕ} (hw : 0<w) (j p : ℕ) : rotate w j p≤modulus w := by
  by_cases hp : p=0
  · simp [rotate,hp]
  · simpa only [rotate,if_neg hp] using (rep_bound (mp hw) (2^j*p)).2

theorem rotate_pos {w p : ℕ} (hw : 0<w) (j : ℕ) (hp : 0<p) : 0<rotate w j p := by
  simpa only [rotate,if_neg hp.ne'] using (rep_bound (mp hw) (2^j*p)).1

theorem period (w : ℕ) : 2^w ≡ 1 [MOD modulus w] :=
  ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by decide))).mpr (dvd_refl _)).symm

theorem rotate_inverse {w j p : ℕ} (hw : 0<w) (shift : j≤w) (bound : p≤modulus w) :
    rotate w (w-j) (rotate w j p)=p := by
  rcases p.eq_zero_or_pos with rfl|hp
  · simp [rotate]
  apply rep_eq (rotate_pos hw _ (rotate_pos hw _ hp)) (rotate_bound hw ..) hp bound
  calc
    _ ≡ 2^(w-j)*rotate w j p [MOD modulus w] := rotate_modEq hw _
    _ ≡ 2^(w-j)*(2^j*p) [MOD modulus w] := (rotate_modEq hw j).mul_left _
    _ = 2^w*p := by rw [←mul_assoc,←pow_add,Nat.sub_add_cancel shift]
    _ ≡ p [MOD modulus w] := by simpa only [one_mul] using (period w).mul_right p

/-- This swaps a j-bit high block and a (w−j)-bit low block. -/
theorem blocks {w j high low : ℕ} (hw : 0<w) (shift : j≤w)
    (hd : high<2^j) (ld : low<2^(w-j)) :
    rotate w j (high*2^(w-j)+low)=low*2^j+high := by
  have product : (2:ℕ)^j*2^(w-j)=2^w := by rw [←pow_add]; congr 1; omega
  have bound : low*2^j+high<2^w := calc
    _ < (low+1)*2^j := by rw [Nat.add_mul,one_mul]; omega
    _ ≤ 2^(w-j)*2^j := Nat.mul_le_mul_right _ ld
    _ = _ := (mul_comm ..).trans product
  by_cases hp : high*2^(w-j)+low=0
  · have big : 0<(2:ℕ)^(w-j) := by positivity
    have hi : high=0 := by
      rcases high.eq_zero_or_pos with e|h
      · exact e
      · have := Nat.mul_pos h big; omega
    simp_all [rotate]
  have pos : 0<low*2^j+high := by
    by_cases hi : high=0
    · subst high; simp only [zero_mul,zero_add] at hp; positivity
    · omega
  apply rep_eq (rotate_pos hw _ (Nat.pos_of_ne_zero hp)) (rotate_bound hw ..) pos
    (show low*2^j+high≤modulus w by unfold modulus; omega)
  calc
    _ ≡ 2^j*(high*2^(w-j)+low) [MOD modulus w] := rotate_modEq hw j
    _ = low*2^j+high*(2^j*2^(w-j)) := by ring
    _ ≡ _ [MOD modulus w] := by
      rw [product]
      simpa only [mul_one] using ((period w).mul_left high).add_left (low*2^j)

def half (j : ℕ) := (j+1)/2

theorem target {w p q j : ℕ} (hw : 0<w) (turn : q=rotate w j p) :
    (2^(half j)*p)^2 ≡ 2^(j%2)*(p*q) [MOD modulus w] := by
  rw [turn]
  calc
    _ = 2^(j%2)*(p*(2^j*p)) := by
      rw [mul_pow,←pow_mul,show half j*2=j%2+j by unfold half; omega,pow_add]
      ring
    _ ≡ _ [MOD modulus w] := (((rotate_modEq hw j).symm.mul_left p).mul_left _)

/-- At odd word widths, adding one complete period to an odd shift makes
its exponent even. Every shift then gives a root of N itself. -/
def oddHalf (w j : ℕ) := (j+(j%2)*w)/2

theorem odd_target {w p q j : ℕ} (odd : Odd w) (turn : q=rotate w j p) :
    (2^(oddHalf w j)*p)^2 ≡ p*q [MOD modulus w] := by
  obtain ⟨a,ha⟩ := odd
  have hw : 0<w := by omega
  have even : oddHalf w j*2=j+(j%2)*w := by
    unfold oddHalf
    rcases Nat.mod_two_eq_zero_or_one j with h|h <;> rw [h] <;> simp <;> omega
  calc
    _ = (2^j*(2^w)^(j%2))*(p*p) := by
      rw [mul_pow,←pow_mul,even,pow_add,←pow_mul,Nat.mul_comm w (j%2),pow_two p]
    _ ≡ (2^j*1)*(p*p) [MOD modulus w] := by
      simpa only [one_pow] using (((period w).pow (j%2)).mul_left (2^j)).mul_right (p*p)
    _ = p*(2^j*p) := by ring
    _ ≡ p*q [MOD modulus w] := by rw [turn]; exact (rotate_modEq hw j).symm.mul_left p

noncomputable def roots (w N r : ℕ) := (range (modulus w)).filter (fun x =>
  x^2 ≡ 2^r*N [MOD modulus w])

theorem mem_roots {w N r x : ℕ} : x∈roots w N r ↔ x<modulus w ∧ x^2 ≡ 2^r*N [MOD modulus w] := by
  simp only [roots,mem_filter,mem_range]

/-- Undo d rotation steps on a normalized root, then apply the proposed
j-step rotation to obtain the second word. -/
def fromRoot (w j d r : ℕ) : ℕ×ℕ :=
  let p := rotate w (w-d) (positiveRep (modulus w) r)
  (p,rotate w j p)

/-- An abstract finite table from a single root class, with exact product validation. -/
noncomputable def pairsAt (w j d N parity : ℕ) :=
  ((roots w N parity).image (fromRoot w j d)).filter (fun pq => pq.1*pq.2=N)

theorem card_pairsAt (w j d N parity : ℕ) :
    (pairsAt w j d N parity).card≤(roots w N parity).card :=
  (card_filter_le ..).trans card_image_le

private theorem sound {w j d N parity p q : ℕ} (hw : 0<w) (hit : (p,q)∈pairsAt w j d N parity) :
    0<p ∧ p≤modulus w ∧ q=rotate w j p ∧ p*q=N := by
  obtain ⟨member,prod⟩ := mem_filter.mp hit
  obtain ⟨r,_,same⟩ := mem_image.mp member
  have eq : rotate w (w-d) (positiveRep (modulus w) r)=p := congrArg Prod.fst same
  refine ⟨eq ▸ rotate_pos hw _ (rep_bound (mp hw) r).1,eq ▸ rotate_bound hw ..,?_,prod⟩
  rw [←eq]
  exact (congrArg Prod.snd same).symm

private theorem complete {w j d N parity p q : ℕ} (hw : 0<w) (inv : d≤w)
    (hp : 0<p) (bound : p≤modulus w) (turn : q=rotate w j p) (prod : p*q=N)
    (sq : (2^d*p)^2 ≡ 2^parity*N [MOD modulus w]) : (p,q)∈pairsAt w j d N parity := by
  let u := rotate w d p
  let r := u%modulus w
  have eq : r ≡ u [MOD modulus w] := Nat.mod_modEq ..
  have root : r∈roots w N parity := mem_roots.mpr ⟨Nat.mod_lt _ (mp hw),
    ((eq.trans (rotate_modEq hw d)).pow 2).trans sq⟩
  have posRep : positiveRep (modulus w) r=u :=
    (rep_congr eq).trans (rep_id (rotate_pos hw d hp) (rotate_bound hw ..))
  have recover : fromRoot w j d r=(p,q) := by
    simp only [fromRoot,posRep,u,rotate_inverse hw inv bound,turn]
  exact mem_filter.mpr ⟨mem_image.mpr ⟨r,root,recover⟩,prod⟩

theorem pairs_iff {w j N p q : ℕ} (hw : 0<w) (shift : j≤w) :
    (p,q)∈pairsAt w j (half j) N (j%2) ↔ 0<p ∧ p≤modulus w ∧ q=rotate w j p ∧ p*q=N := by
  refine ⟨sound hw,?_⟩
  rintro ⟨hp,bound,turn,rfl⟩
  exact complete hw (by unfold half; omega) hp bound turn rfl (target hw turn)

theorem odd_pairs_iff {w j N p q : ℕ} (odd : Odd w) (shift : j≤w) :
    (p,q)∈pairsAt w j (oddHalf w j) N 0 ↔ 0<p ∧ p≤modulus w ∧ q=rotate w j p ∧ p*q=N := by
  have hw : 0<w := by obtain ⟨a,ha⟩ := odd; omega
  refine ⟨sound hw,?_⟩
  rintro ⟨hp,bound,turn,rfl⟩
  have inv : oddHalf w j≤w := by
    unfold oddHalf
    rcases Nat.mod_two_eq_zero_or_one j with h|h <;> rw [h] <;> simp <;> omega
  exact complete hw inv hp bound turn rfl (by simpa only [pow_zero,one_mul] using odd_target odd turn)

/-- A menu for all w rotation offsets, using two root sets. Different
offsets can give the same pair when a word has rotational symmetry. -/
noncomputable def allPairs (w N : ℕ) :=
  (range w).biUnion (fun j => pairsAt w j (half j) N (j%2))

theorem mem_allPairs {w N p q : ℕ} (hw : 0<w) :
    (p,q)∈allPairs w N ↔ 0<p ∧ p≤modulus w ∧ p*q=N ∧ ∃ j<w,q=rotate w j p := by
  constructor
  · intro h
    obtain ⟨j,hj,hit⟩ := mem_biUnion.mp h
    have small := mem_range.mp hj
    obtain ⟨hp,bound,turn,prod⟩ := (pairs_iff hw small.le).mp hit
    exact ⟨hp,bound,prod,j,small,turn⟩
  · rintro ⟨hp,bound,prod,j,small,turn⟩
    exact mem_biUnion.mpr ⟨j,mem_range.mpr small,(pairs_iff hw small.le).mpr ⟨hp,bound,turn,prod⟩⟩

theorem card_allPairs (w N : ℕ) : (allPairs w N).card≤w*max (roots w N 0).card (roots w N 1).card := by
  calc
    _ ≤ ∑ j∈range w,(pairsAt w j (half j) N (j%2)).card := card_biUnion_le
    _ ≤ ∑ _j∈range w,max (roots w N 0).card (roots w N 1).card := sum_le_sum fun j _ => by
      apply (card_pairsAt ..).trans
      rcases Nat.mod_two_eq_zero_or_one j with h|h
      · rw [h]; exact le_max_left ..
      · rw [h]; exact le_max_right ..
    _ = _ := by simp

theorem odd_allPairs {w : ℕ} (odd : Odd w) (N : ℕ) :
    allPairs w N=(range w).biUnion (fun j => pairsAt w j (oddHalf w j) N 0) := by
  have pos : 0<w := by obtain ⟨a,ha⟩ := odd; omega
  apply Finset.biUnion_congr rfl
  intro j hj
  obtain le := (mem_range.mp hj).le
  ext ⟨p,q⟩
  exact (pairs_iff pos le).trans (odd_pairs_iff odd le).symm

theorem card_allPairs_odd {w : ℕ} (odd : Odd w) (N : ℕ) :
    (allPairs w N).card≤w*(roots w N 0).card := by
  rw [odd_allPairs odd]
  calc
    _ ≤ ∑ j∈range w,(pairsAt w j (oddHalf w j) N 0).card := card_biUnion_le
    _ ≤ ∑ _j∈range w,(roots w N 0).card := sum_le_sum fun _ _ => card_pairsAt ..
    _ = _ := by simp

/-- These two six-bit examples realize the two parities, with all modular
roots and both orientations of the word pairs checked on small numbers. -/
theorem even_shift_example : roots 6 2773 0={1,8,55,62} ∧ roots 6 2773 1=∅ ∧
    pairsAt 6 4 (half 4) 2773 0={(47,59)} ∧ pairsAt 6 2 (half 2) 2773 0={(59,47)} ∧
    Nat.Prime 47 ∧ Nat.Prime 59 := by decide +kernel

theorem odd_shift_example : roots 6 2279 0=∅ ∧ roots 6 2279 1={20,29,34,43} ∧
    pairsAt 6 5 (half 5) 2279 1={(43,53)} ∧ pairsAt 6 1 (half 1) 2279 1={(53,43)} ∧
    Nat.Prime 43 ∧ Nat.Prime 53 := by decide +kernel

theorem odd_width_example : roots 5 667 0={4,27} ∧ roots 5 667 1={1,30} ∧
    pairsAt 5 3 (oddHalf 5 3) 667 0={(23,29)} ∧ rotate 5 3 31=31 ∧ rotate 5 3 0=0 := by
  decide +kernel

end PrimeFactors.BinaryRotationProduct
