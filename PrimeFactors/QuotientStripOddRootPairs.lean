import PrimeFactors.QuotientStripRectangularEnergy

namespace PrimeFactors.QuotientStripOddRootPairs

open Finset QuotientStripDiscriminantMultiplicity
set_option exponentiation.threshold 4096
set_option maxRecDepth 8000

private theorem roots_one_parity {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q)
    (odd : Odd (p*q)) (labels : Finset ℤ) (D : ℤ)
    (inside : ∀ z∈labels, 0<z ∧ z<(p*q:ℕ))
    (root : ∀ z∈labels, (z:ZMod (p*q))^2=(D:ZMod (p*q)))
    (parity : ∀ z∈labels, z%2=D%2) : labels.card ≤ 2 := by
  classical
  let N := p*q
  let rev := labels.image fun z => (N:ℤ)-z
  obtain ⟨k,hk⟩ := odd
  have no : (N:ℤ)=2*(k:ℤ)+1 := by exact_mod_cast hk
  have dis : Disjoint labels rev := by
    apply disjoint_left.mpr
    intro z hz hr
    obtain ⟨t,ht,eq⟩ := mem_image.mp hr
    change (N:ℤ)-t=z at eq
    have one := parity z hz
    have two := parity t ht
    omega
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  have range (z : ℤ) (hz : z∈labels∪rev) : 0<z ∧ z<(N:ℤ) := by
    rcases mem_union.mp hz with h|h
    · exact inside _ h
    · obtain ⟨a,ha,rfl⟩ := mem_image.mp h
      have h := inside a ha
      omega
  have lower : (labels∪rev).card ≤ (SmoothSampleBound.roots (D:ZMod N)).card := by
    apply card_le_card_of_injOn (fun z : ℤ => (z:ZMod N))
    · intro z hz
      apply mem_filter.mpr ⟨mem_univ _,?_⟩
      rcases mem_union.mp hz with h|h
      · exact root z h
      · obtain ⟨t,ht,eq⟩ := mem_image.mp h
        change (N:ℤ)-t=z at eq
        rw [←eq]
        simpa only [Int.cast_sub,Int.cast_natCast,ZMod.natCast_self,zero_sub,neg_sq] using root t ht
    · intro a ha b hb h
      have eq := (ZMod.intCast_eq_intCast_iff' ..).mp h
      rwa [Int.emod_eq_of_lt (range a ha).1.le (range a ha).2,
        Int.emod_eq_of_lt (range b hb).1.le (range b hb).2] at eq
  have upper := lower.trans (SmoothSampleBound.crtRootCount ((Nat.coprime_primes hp hq).mpr hne) _)
  have equal : rev.card=labels.card := card_image_of_injective _ (by intro a b eq; dsimp only at eq; omega)
  rw [card_union_of_disjoint dis,equal] at upper
  omega

/-- Equal discriminants have equal label parity. Complementary nonzero
roots z and N-z have opposite parity when N is odd, so at most two of the
four CRT roots can contribute a product in the full positive label interval. -/
theorem two_per_discriminant {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q)
    (odd : Odd (p*q)) (rows : Finset Pair) (z : Pair → ℤ)
    (bounds : ∀ s∈rows, 0<z s ∧ z s<(p*q:ℕ)) (D : ℤ) :
    ((rows.filter (fun s => discriminant (p*q) z s=D)).image weight).card ≤ 2 := by
  let N := p*q
  let F := rows.filter fun s => discriminant N z s=D
  let Z := F.image z
  have data {s : Pair} (hs : s∈F) : s∈rows ∧ z s ^ 2-4*(weight s:ℤ)*(N:ℤ)=D :=
    mem_filter.mp hs
  have npos : (0:ℤ)<N := by exact_mod_cast Nat.mul_pos hp.pos hq.pos
  have decode {s : Pair} (hs : s∈F) :
      (((z s ^ 2-D)/(4*(N:ℤ))).toNat)=weight s := by
    have ident : z s ^ 2-D = weight s*(4*(N:ℤ)) := by linarith only [(data hs).2]
    rw [ident,Int.mul_ediv_cancel _ (by positivity : 4*(N:ℤ)≠0),Int.toNat_natCast]
  have sub : F.image weight ⊆ Z.image (fun t => ((t^2-D)/(4*(N:ℤ))).toNat) := by
    intro _ hm
    obtain ⟨s,hs,rfl⟩ := mem_image.mp hm
    exact mem_image.mpr ⟨z s,mem_image_of_mem z hs,decode hs⟩
  change (F.image weight).card≤2
  apply ((card_le_card sub).trans card_image_le).trans
  apply roots_one_parity hp hq hne odd Z D
  · rintro _ ht
    obtain ⟨s,hs,rfl⟩ := mem_image.mp ht
    exact bounds _ (data hs).1
  · rintro _ ht
    obtain ⟨s,hs,rfl⟩ := mem_image.mp ht
    have eq := congrArg (fun d : ℤ => (d:ZMod N)) (data hs).2
    simpa only [Int.cast_sub,Int.cast_mul,Int.cast_pow,Int.cast_natCast,
      ZMod.natCast_self,mul_zero,sub_zero] using eq
  · rintro _ ht
    obtain ⟨s,hs,rfl⟩ := mem_image.mp ht
    obtain ⟨a,eq⟩ := (z s).even_mul_pred_self.two_dvd
    have rep : D=z s+2*(a-2*(weight s:ℤ)*N) := by nlinarith only [(data hs).2,eq]
    omega

theorem two_fold {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q) (odd : Odd (p*q))
    (rows : Finset Pair) (z : Pair → ℤ) (bounds : ∀ s∈rows, 0<z s ∧ z s<(p*q:ℕ)) :
    (rows.image weight).card ≤ 2*(rows.image (discriminant (p*q) z)).card := by
  let discs := rows.image (discriminant (p*q) z)
  let levels (d : ℤ) := (rows.filter (fun s => discriminant (p*q) z s=d)).image weight
  have cover : rows.image weight ⊆ discs.biUnion levels := by
    intro _ hm
    obtain ⟨s,hs,rfl⟩ := mem_image.mp hm
    exact mem_biUnion.mpr ⟨_,mem_image_of_mem _ hs,mem_image_of_mem _ (mem_filter.mpr ⟨hs,rfl⟩)⟩
  exact (card_le_card cover).trans <| (card_biUnion_le_card_mul _ _ _ (fun d _ =>
    two_per_discriminant hp hq hne odd rows z bounds d)).trans_eq (Nat.mul_comm ..)

theorem target {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q) (odd : Odd (p*q))
    (rows : Finset Pair) (z : Pair → ℤ) (many : 2^653 ≤ rows.card)
    (box : ∀ s∈rows, 0<s.1 ∧ s.1≤9*2^327 ∧ 0<s.2 ∧ s.2≤7*2^327)
    (bounds : ∀ s∈rows, 0<z s ∧ z s<(p*q:ℕ)) :
    2^635 < (rows.image (discriminant (p*q) z)).card := by
  have en := QuotientStripRectangularEnergy.subset_energy rows box (show 7*2^327≤(2:ℕ)^330 by decide +kernel)
  have mult := two_fold hp hq hne odd rows z bounds
  by_contra! bad
  have bound := Nat.mul_le_mul_right (9*2^327*(7*2^327)*(1+3*330)) (mult.trans (Nat.mul_le_mul_left 2 bad))
  have left := (Nat.pow_le_pow_left many 2).trans (en.trans bound)
  exact (by decide +kernel : ¬ (2^653:ℕ)^2 ≤ 2*2^635*(9*2^327*(7*2^327)*(1+3*330))) left

end PrimeFactors.QuotientStripOddRootPairs
