import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace PrimeFactors

/-- Free binary positions in the k-bit window beginning at e. -/
noncomputable def scatteredWindow (A : Finset ℕ) (e k : ℕ) : Finset ℕ :=
  A.filter fun j => e ≤ j ∧ j < e+k

private def scatteredTag (S : Finset ℕ) (x : ℕ) : Finset ℕ :=
  S.filter fun j => x.testBit j

private theorem scatteredTag_bit {S : Finset ℕ} {x y j : ℕ} (mem : j ∈ S)
    (same : scatteredTag S x = scatteredTag S y) : x.testBit j = y.testBit j := by
  have h : j ∈ scatteredTag S x ↔ j ∈ scatteredTag S y := by rw [same]
  simpa [scatteredTag,mem] using h

/-- A progression of at most 2^k literal integers, with any positive step
2^e u, contains at most one compatible word per assignment to the free
digits in its k-bit window. -/
theorem scatteredFactor_packet (A hits : Finset ℕ) (a e u k : ℕ) (odd : Odd u)
    (packet : ∀ x ∈ hits, ∃ t < 2^k, x = a+2^e*u*t)
    (fixed : ∀ x ∈ hits, ∀ y ∈ hits, ∀ j ∉ A, x.testBit j = y.testBit j) :
    hits.card ≤ 2^(scatteredWindow A e k).card := by
  let W := scatteredWindow A e k
  have inj : Set.InjOn (scatteredTag W) (hits : Set ℕ) := by
    intro x hx y hy tag
    obtain ⟨s,hs,ex⟩ := packet x hx
    obtain ⟨t,ht,ey⟩ := packet y hy
    have low : x/2^e ≡ y/2^e [MOD 2^k] := by
      apply Nat.eq_of_testBit_eq
      intro i
      simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
      by_cases small : i < k
      · simp only [small, decide_true, Bool.true_and]
        by_cases mem : i+e ∈ A
        · exact scatteredTag_bit (S := W) (Finset.mem_filter.mpr ⟨mem, by omega, by omega⟩) tag
        · exact fixed x hx y hy _ mem
      · simp [small]
    rw [ex,ey,Nat.mul_assoc,Nat.mul_assoc,Nat.add_mul_div_left _ _ (by positivity),
      Nat.add_mul_div_left _ _ (by positivity)] at low
    have index : s ≡ t [MOD 2^k] :=
      Nat.ModEq.cancel_left_of_coprime (odd.coprime_two_left.pow_left k)
        (Nat.ModEq.add_left_cancel (Nat.ModEq.refl _) low)
    rw [ex,ey,index.eq_of_lt_of_lt hs ht]
  simpa [W] using Finset.card_le_card_of_injOn (t := W.powerset) (scatteredTag W)
    (fun x _ => Finset.mem_powerset.mpr (Finset.filter_subset ..)) inj

/-- Fixing all free bits outside one window gives a covering by as many
dyadic progressions as there are assignments to those outside bits. -/
theorem scatteredFactor_cover (A words : Finset ℕ) (e k : ℕ)
    (fixed : ∀ x ∈ words, ∀ y ∈ words, ∀ j ∉ A, x.testBit j = y.testBit j) :
    ∃ starts : Finset ℕ, starts.card ≤ 2^(A \ scatteredWindow A e k).card ∧
      ∀ x ∈ words, ∃ a ∈ starts, ∃ t < 2^k, x = a+2^e*t := by
  classical
  let outside := A \ scatteredWindow A e k
  let key := scatteredTag outside
  let rep (s : Finset ℕ) := if h : ∃ x ∈ words, key x = s then h.choose else 0
  let base (y : ℕ) := y%2^e + 2^(e+k)*(y/2^(e+k))
  let starts := outside.powerset.image fun s => base (rep s)
  refine ⟨starts,(Finset.card_image_le.trans (by simp [outside])),?_⟩
  intro x hx
  have witness : ∃ y ∈ words, key y = key x := ⟨x,hx,rfl⟩
  have spec : rep (key x) ∈ words ∧ key (rep (key x)) = key x := by
    simp only [rep,dif_pos witness]
    exact witness.choose_spec
  let y := rep (key x)
  have bit (j : ℕ) (out : j < e ∨ e+k ≤ j) : y.testBit j = x.testBit j := by
    by_cases mem : j ∈ A
    · apply scatteredTag_bit (S := outside) _ spec.2
      apply Finset.mem_sdiff.mpr
      exact ⟨mem,fun h => by have := (Finset.mem_filter.mp h).2; omega⟩
    · exact fixed _ spec.1 _ hx j mem
  have lo : y%2^e = x%2^e := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases h : j < e <;> simp [h, fun (hj : j < e) => bit j (Or.inl hj)]
  have hi : y/2^(e+k) = x/2^(e+k) := by
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [Nat.testBit_div_two_pow]
    exact bit _ (Or.inr (by omega))
  refine ⟨base y,Finset.mem_image.mpr ⟨key x,Finset.mem_powerset.mpr
    (Finset.filter_subset ..),rfl⟩,x/2^e%2^k,Nat.mod_lt _ (by positivity),?_⟩
  change x = y%2^e+2^(e+k)*(y/2^(e+k))+2^e*(x/2^e%2^k)
  rw [lo,hi,pow_add,Nat.mul_assoc,← Nat.div_div_eq_div_mul,Nat.add_assoc,← Nat.mul_add,
    Nat.add_comm (2^k*_) _,Nat.mod_add_div,Nat.mod_add_div]

/-- A list of packets covers at most its length times the largest permitted
window population, even when every packet has a different stride. -/
theorem scatteredFactor_packet_budget {ι : Type*} (I : Finset ι) (A : Finset ℕ)
    (hits : ι → Finset ℕ) (a d : ι → ℕ) (k H : ℕ)
    (positive : ∀ i ∈ I, d i ≠ 0)
    (capacity : ∀ e, (scatteredWindow A e k).card ≤ H)
    (packet : ∀ i ∈ I, ∀ x ∈ hits i, ∃ t < 2^k, x = a i+d i*t)
    (fixed : ∀ i ∈ I, ∀ x ∈ hits i, ∀ y ∈ hits i, ∀ j ∉ A, x.testBit j = y.testBit j) :
    (I.biUnion hits).card ≤ I.card*2^H := by
  calc
    _ ≤ ∑ i ∈ I, (hits i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ I, 2^H := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨e,u,odd,hd⟩ := Nat.exists_eq_two_pow_mul_odd (positive i hi)
      exact (scatteredFactor_packet A (hits i) (a i) e u k odd
        (by simpa only [← hd] using packet i hi) (fixed i hi)).trans
        (Nat.pow_le_pow_right (by decide) (capacity e))
    _ = _ := by simp

/-- A cover of every assignment to the free bits must pay at least one
packet per 2^H assignments. A family realizes every assignment when its
restricted binary tags exhaust the powerset. -/
theorem scatteredFactor_complete_budget {ι : Type*} (I : Finset ι) (A words : Finset ℕ)
    (hits : ι → Finset ℕ) (a d : ι → ℕ) (k H : ℕ)
    (realize : A.powerset ⊆ words.image (fun x => A.filter fun j => x.testBit j))
    (cover : words ⊆ I.biUnion hits) (positive : ∀ i ∈ I, d i ≠ 0)
    (capacity : ∀ e, (scatteredWindow A e k).card ≤ H)
    (packet : ∀ i ∈ I, ∀ x ∈ hits i, ∃ t < 2^k, x = a i+d i*t)
    (fixed : ∀ i ∈ I, ∀ x ∈ hits i, ∀ y ∈ hits i, ∀ j ∉ A, x.testBit j = y.testBit j) :
    2^A.card ≤ I.card*2^H := by
  simpa only [Finset.card_powerset] using (Finset.card_le_card realize).trans
    (Finset.card_image_le.trans ((Finset.card_le_card cover).trans
      (scatteredFactor_packet_budget I A hits a d k H positive capacity packet fixed)))

/-- Every interval of 2k binary positions contains at most k odd positions. -/
theorem scatteredFactor_odd_window (A : Finset ℕ) (e k : ℕ) (odd : ∀ j ∈ A, Odd j) :
    (scatteredWindow A e (2*k)).card ≤ k := by
  let W := scatteredWindow A e (2*k)
  let index (j : ℕ) := (j-e)/2
  have into (j : ℕ) (hj : j ∈ W) : index j ∈ Finset.range k := by
    have bounds := (Finset.mem_filter.mp hj).2
    apply Finset.mem_range.mpr
    dsimp [index]
    omega
  have inj : Set.InjOn index (W : Set ℕ) := by
    intro j hj m hm eq
    obtain ⟨_,lo,_⟩ := Finset.mem_filter.mp hj
    obtain ⟨_,lo',_⟩ := Finset.mem_filter.mp hm
    obtain ⟨v,hv⟩ := odd _ (Finset.mem_filter.mp hj).1
    obtain ⟨w,hw⟩ := odd _ (Finset.mem_filter.mp hm).1
    dsimp [index] at eq
    omega
  simpa using Finset.card_le_card_of_injOn index into inj

/-- The first n positive odd bit positions. -/
noncomputable def scatteredAlternating (n : ℕ) : Finset ℕ :=
  (Finset.range n).map ⟨fun j => 2*j+1,fun x y h => by
    change 2*x+1 = 2*y+1 at h
    omega⟩

private theorem scatteredAlternating_mem {j n : ℕ} :
    j ∈ scatteredAlternating n ↔ ∃ i < n, 2*i+1 = j := by
  simp [scatteredAlternating]

/-- An alternating 1024-bit mask with 511 interior unknown positions
attains a maximum of 256 in a 512-bit window. -/
theorem scatteredFactor_alternating_example :
    (scatteredAlternating 511).card = 511 ∧
      (scatteredWindow (scatteredAlternating 511) 1 512).card = 256 ∧
      ∀ e, (scatteredWindow (scatteredAlternating 511) e 512).card ≤ 256 := by
  have interval : scatteredWindow (scatteredAlternating 511) 1 512 = scatteredAlternating 256 := by
    ext i
    simp only [scatteredWindow, Finset.mem_filter, scatteredAlternating_mem]
    constructor
    · rintro ⟨⟨j,hj,rfl⟩,_,h⟩
      exact ⟨j,by omega,rfl⟩
    · rintro ⟨j,hj,rfl⟩
      exact ⟨⟨j,by omega,rfl⟩,by omega,by omega⟩
  refine ⟨by simp [scatteredAlternating],by rw [interval]; simp [scatteredAlternating],?_⟩
  intro e
  apply scatteredFactor_odd_window _ _ 256
  intro j hj
  obtain ⟨i,_,rfl⟩ := scatteredAlternating_mem.mp hj
  exact ⟨i,rfl⟩

/-- Fix one observed product residue. Once the second factor is fixed and
invertible, at most one first factor lies in the length-X dyadic band. -/
theorem scatteredFactor_residue_count (X a : ℕ) (pairs : Finset (ℕ × ℕ))
    (candidates : Finset ℕ)
    (band : ∀ w ∈ pairs, X ≤ w.1 ∧ w.1 < 2*X)
    (unit : ∀ w ∈ pairs, X.Coprime w.2)
    (residue : ∀ w ∈ pairs, w.1*w.2 ≡ a [MOD X])
    (allowed : ∀ w ∈ pairs, w.2 ∈ candidates) : pairs.card ≤ candidates.card := by
  apply Finset.card_le_card_of_injOn Prod.snd allowed
  rintro ⟨p,q⟩ hp ⟨r,s⟩ hr same
  change q = s at same
  subst s
  have key := (residue _ hp).trans (residue _ hr).symm
  have reduced := Nat.ModEq.cancel_right_of_coprime (unit _ hp) key
  have pband := band _ hp
  have rband := band _ hr
  change X ≤ p ∧ p < 2*X at pband
  change X ≤ r ∧ r < 2*X at rband
  have low : p-X ≡ r-X [MOD X] := by
    apply Nat.ModEq.add_left_cancel (Nat.ModEq.refl X)
    simpa only [Nat.add_sub_of_le pband.1,Nat.add_sub_of_le rband.1] using reduced
  have := low.eq_of_lt_of_lt (by omega) (by omega)
  exact Prod.ext (by omega) rfl

end PrimeFactors
