import PrimeFactors.FactorLaneAdvice
import Mathlib.Data.Nat.Prime.Basic

namespace PrimeFactors.CRTResidueAdvice
open Finset

/-- Relative to any input reaching a branch, the next full remainder refines
the previous class to one class of the least common multiple. -/
theorem refine_transcript {n sample m k : ℕ} :
    (n ≡ sample [MOD m] ∧ n ≡ sample [MOD k]) ↔ n ≡ sample [MOD m.lcm k] :=
  ⟨fun h => Nat.mod_lcm h.1 h.2,
   fun h => ⟨h.of_dvd (Nat.dvd_lcm_left m k), h.of_dvd (Nat.dvd_lcm_right m k)⟩⟩

/-- A newly introduced large prime limits the previous accumulated modulus. -/
theorem before_large_prime {m r L Q X : ℕ} (pos : 0<L) (cap : L≤Q)
    (small : Q<X*X) (large : X≤r) (cop : m.Coprime r) (hm : m ∣ L) (hr : r ∣ L) :
    m≤Q/X ∧ m<X := by
  have combined := Nat.le_of_dvd pos (cop.mul_dvd_of_dvd_of_dvd hm hr)
  have bound := (Nat.mul_le_mul_left m large).trans (combined.trans cap)
  have hx : 0 < X := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at small
  refine ⟨(Nat.le_div_iff_mul_le hx).mpr bound, ?_⟩
  exact lt_of_not_ge fun h => (Nat.not_le_of_gt small)
    ((Nat.mul_le_mul_right X h).trans bound)

/-- Two distinct primes of the population cannot both divide an affordable modulus. -/
theorem unique_large_prime {p q L Q X : ℕ} (hp : p.Prime) (hq : q.Prime)
    (lp : X≤p) (lq : X≤q) (pos : 0<L) (cap : L≤Q) (small : Q<X*X)
    (dp : p ∣ L) (dq : q ∣ L) : p=q := by
  by_contra h
  have both := ((Nat.coprime_primes hp hq).mpr h).mul_dvd_of_dvd_of_dvd dp dq
  exact (Nat.not_le_of_gt small)
    ((Nat.mul_le_mul lp lq).trans ((Nat.le_of_dvd pos both).trans cap))

/-- The part of a transcript's congruence class in an interval of length X+Q. -/
noncomputable def bucket (X Q m a : ℕ) : Finset ℕ :=
  (range (X+Q)).filter fun i => i ≡ a [MOD m]

/-- At a fixed first factor the possible second factors inject into the
same bucket, even though their product, rather than their value, is observed. -/
theorem cell {X Q m a : ℕ} (pos : 0<m) (bounded : m≤Q) (residue : a<m)
    (hits : Finset (ℕ × ℕ)) (shortlist : Finset ℕ)
    (inside : ∀ t ∈ hits, t.1 ∈ shortlist ∧ X≤t.2 ∧ t.2<2*X ∧
      m.Coprime t.1 ∧ t.1*t.2 ≡ a [MOD m]) :
    hits.card ≤ shortlist.card * (bucket X Q m a).card := by
  let code (q : ℕ) := a + m*((q-X)/m)
  rw [← card_product]
  apply card_le_card_of_injOn (fun t : ℕ × ℕ => (t.1,code t.2))
  · intro t ht
    obtain ⟨keep,lo,hi,_,_⟩ := inside t ht
    refine mem_product.mpr ⟨keep, mem_filter.mpr ⟨mem_range.mpr ?_, ?_⟩⟩
    · dsimp [code]
      have bound := Nat.mul_div_le (t.2-X) m
      omega
    · simp [code, Nat.ModEq]
  · rintro ⟨p,q⟩ hp ⟨r,s⟩ hr same
    have first : p=r := congrArg Prod.fst same
    subst r
    obtain ⟨_,hq,_,cop,cq⟩ := inside (p,q) hp
    obtain ⟨_,hs,_,_,cs⟩ := inside (p,s) hr
    have sameQuo : (q-X)/m=(s-X)/m := by
      have eq : a+m*((q-X)/m)=a+m*((s-X)/m) := congrArg Prod.snd same
      exact Nat.eq_of_mul_eq_mul_left pos (Nat.add_left_cancel eq)
    have sameResidue := (cq.trans cs.symm).cancel_left_of_coprime cop
    have shifted : (q-X)+X ≡ (s-X)+X [MOD m] := by
      simpa only [Nat.sub_add_cancel hq,Nat.sub_add_cancel hs] using sameResidue
    have rem := Nat.ModEq.add_right_cancel' X shifted
    change (q-X)%m = (s-X)%m at rem
    have eq : q-X=s-X := by
      rw [← Nat.mod_add_div (q-X) m, rem, sameQuo, Nat.mod_add_div]
    exact Prod.ext rfl (by omega)

/-- Disjoint transcript classes can have unrelated moduli. The interval
bound charges all cells without taking their global least common multiple. -/
theorem disjoint_cells {ι : Type*} (leaves : Finset ι) (modulus residue : ι → ℕ)
    (hits : ι → Finset (ℕ × ℕ)) (shortlist : ι → Finset ℕ) {X Q K : ℕ}
    (parameters : ∀ i ∈ leaves, 0<modulus i ∧ modulus i≤Q ∧ residue i<modulus i ∧
      (shortlist i).card≤K)
    (disjoint : (leaves : Set ι).PairwiseDisjoint (fun i => bucket X Q (modulus i) (residue i)))
    (inside : ∀ i ∈ leaves, ∀ t ∈ hits i,
      t.1 ∈ shortlist i ∧ X≤t.2 ∧ t.2<2*X ∧ (modulus i).Coprime t.1 ∧
      t.1*t.2 ≡ residue i [MOD modulus i]) :
    (leaves.biUnion hits).card ≤ K*(X+Q) := by
  let cells i := bucket X Q (modulus i) (residue i)
  have subs : leaves.biUnion cells ⊆ range (X+Q) := by
    intro t ht
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp ht
    exact (mem_filter.mp hi).1
  have total := card_le_card subs
  rw [card_biUnion disjoint,card_range] at total
  calc
    _ ≤ ∑ i ∈ leaves, (hits i).card := card_biUnion_le
    _ ≤ ∑ i ∈ leaves, K*(cells i).card := by
      apply sum_le_sum
      intro i hi
      obtain ⟨pos, cap, valid, size⟩ := parameters i hi
      exact (cell pos cap valid (hits i) (shortlist i) (inside i hi)).trans
        (Nat.mul_le_mul_right _ size)
    _ = K*∑ i ∈ leaves, (cells i).card := (mul_sum ..).symm
    _ ≤ _ := Nat.mul_le_mul_left _ total

/-- If each leaf selects at most S factor residues and the factor interval
consists of B full radix blocks, at most S*B*(B*R+Q) oriented pairs succeed. -/
theorem residue_bound {ι : Type*} (leaves : Finset ι) (modulus residue : ι → ℕ)
    (hits : ι → Finset (ℕ × ℕ)) (guesses : ι → Finset ℕ) {R B Q S : ℕ}
    (pos : 0<R)
    (parameters : ∀ i ∈ leaves, 0<modulus i ∧ modulus i≤Q ∧ residue i<modulus i ∧
      (guesses i).card≤S)
    (disjoint : (leaves : Set ι).PairwiseDisjoint (fun i => bucket (B*R) Q (modulus i) (residue i)))
    (inside : ∀ i ∈ leaves, ∀ t ∈ hits i,
      B*R≤t.1 ∧ t.1<(2*B)*R ∧ t.1%R ∈ guesses i ∧ B*R≤t.2 ∧ t.2<2*(B*R) ∧
      (modulus i).Coprime t.1 ∧ t.1*t.2 ≡ residue i [MOD modulus i]) :
    (leaves.biUnion hits).card ≤ (S*B)*(B*R+Q) := by
  let candidates i := ((guesses i) ×ˢ Ico B (2*B)).image (fun z => z.1+R*z.2)
  refine disjoint_cells leaves modulus residue hits candidates ?_ disjoint ?_
  · intro i hi
    obtain ⟨hp,cap,hr,hs⟩ := parameters i hi
    refine ⟨hp,cap,hr,(card_image_le).trans ?_⟩
    simpa [two_mul] using (Nat.mul_le_mul_right B hs)
  · intro i hi t ht
    obtain ⟨lo,hi',hg,rest⟩ := inside i hi t ht
    refine ⟨mem_image.mpr ⟨(t.1%R,t.1/R), mem_product.mpr ⟨hg, mem_Ico.mpr ⟨?_,?_⟩⟩,
      Nat.mod_add_div t.1 R⟩,rest⟩
    · exact (Nat.le_div_iff_mul_le pos).mpr lo
    · exact (Nat.div_lt_iff_lt_mul pos).mpr hi'

/-- Fixing the answers to arbitrary product predicates splits success into
at most 2^t families; the families need not be disjoint. -/
theorem with_binary_answers {ι α : Type*} [DecidableEq α]
    (strings : Finset ι) (hits : ι → Finset α) {t W : ℕ}
    (count : strings.card≤2^t) (bound : ∀ i ∈ strings, (hits i).card≤W) :
    (strings.biUnion hits).card ≤ 2^t*W := by
  refine card_biUnion_le.trans ((sum_le_sum bound).trans ?_)
  simpa using Nat.mul_le_mul_right W count

end PrimeFactors.CRTResidueAdvice
