import PrimeFactors.SmoothSampleBound
import PrimeFactors.DivisorSecondMoment
import Mathlib.Tactic

namespace PrimeFactors.QuotientStripDiscriminantMultiplicity

open Finset
set_option exponentiation.threshold 4096
set_option maxRecDepth 8000
set_option maxHeartbeats 800000

abbrev Pair := ℕ × ℕ
def weight (s : Pair) := s.1*s.2
def discriminant (N : ℕ) (z : Pair → ℤ) (s : Pair) : ℤ := z s ^ 2-4*(weight s : ℤ)*(N:ℤ)

/-- Fixing a discriminant leaves at most four different products of slope
weights, even when its square roots are nonunits. Labels must stay in a
single complete residue interval for the injection to hold. -/
theorem four_per_discriminant {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (rows : Finset Pair) (z : Pair → ℤ)
    (bounds : ∀ s ∈ rows, 0 ≤ z s ∧ z s < (p*q:ℕ)) (D : ℤ) :
    ((rows.filter (fun s => discriminant (p*q) z s = D)).image weight).card ≤ 4 := by
  classical
  let N := p*q
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  let F := rows.filter fun s => discriminant N z s=D
  let M := F.image weight
  have choose (m : ℕ) : m∈M → ∃ s∈F, weight s=m := fun h => mem_image.mp h
  let pick (m : ℕ) := if h : m∈M then (choose m h).choose else (0,0)
  have rep {m : ℕ} (hm : m∈M) : pick m∈F ∧ weight (pick m)=m := by
    simp only [pick,dif_pos hm]
    exact (choose m hm).choose_spec
  have data {m : ℕ} (hm : m∈M) :
      (0 ≤ z (pick m) ∧ z (pick m) < (N:ℤ)) ∧
      z (pick m)^2-4*(m:ℤ)*(N:ℤ)=D := by
    obtain ⟨f,h⟩ := rep hm
    have mem := mem_filter.mp f
    exact ⟨bounds _ mem.1, by simpa only [discriminant,h] using mem.2⟩
  change M.card ≤ 4
  apply le_trans _ (SmoothSampleBound.crtRootCount ((Nat.coprime_primes hp hq).mpr hne)
    (D:ZMod (p*q)))
  apply card_le_card_of_injOn (fun m => (z (pick m) : ZMod N))
  · intro m hm
    apply mem_filter.mpr ⟨mem_univ _,?_⟩
    have eq := congrArg (fun d : ℤ => (d : ZMod N)) (data hm).2
    simpa only [Int.cast_sub,Int.cast_mul,Int.cast_pow,Int.cast_natCast,
      ZMod.natCast_self,mul_zero,sub_zero] using eq
  · intro m hm v hv eq
    have a := data hm
    have b := data hv
    have same := (ZMod.intCast_eq_intCast_iff' ..).mp eq
    rw [Int.emod_eq_of_lt a.1.1 a.1.2,Int.emod_eq_of_lt b.1.1 b.1.2] at same
    have prod : (m:ℤ)*N=(v:ℤ)*N := by
      have h := a.2.trans b.2.symm
      rw [same] at h
      linarith only [h]
    have np : (0:ℤ)<N := by exact_mod_cast Nat.mul_pos hp.pos hq.pos
    exact_mod_cast mul_right_cancel₀ np.ne' prod

/-- Overall loss of at most a factor of four when passing from distinct
weight products to the discriminants of one selected label per slope. -/
theorem four_fold {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q)
    (rows : Finset Pair) (z : Pair → ℤ)
    (bounds : ∀ s ∈ rows, 0 ≤ z s ∧ z s < (p*q:ℕ)) :
    (rows.image weight).card ≤ 4*(rows.image (discriminant (p*q) z)).card := by
  let discs := rows.image (discriminant (p*q) z)
  let levels (d : ℤ) := (rows.filter (fun s => discriminant (p*q) z s=d)).image weight
  have cover : rows.image weight ⊆ discs.biUnion levels := by
    rintro m hm
    obtain ⟨s,hs,rfl⟩ := mem_image.mp hm
    exact mem_biUnion.mpr ⟨_,mem_image_of_mem _ hs,mem_image_of_mem _ (mem_filter.mpr ⟨hs,rfl⟩)⟩
  exact (card_le_card cover).trans <| (card_biUnion_le_card_mul _ _ _ (fun d _ =>
    four_per_discriminant hp hq hne rows z bounds d)).trans_eq (Nat.mul_comm ..)

/-- Restricted product multiplicity, bounded by the divisor second moment. -/
theorem product_energy (rows : Finset Pair) {X b : ℕ}
    (fit : ∀ s ∈ rows, 0 < weight s ∧ weight s ≤ X) (cap : X ≤ 2^b) :
    rows.card^2 ≤ (rows.image weight).card * (X*(b+3).choose 3) := by
  let M := rows.image weight
  let count (m : ℕ) := (rows.filter fun s => weight s=m).card
  have mass : rows.card=∑ m∈M, count m := card_eq_sum_card_image weight rows
  have fiber {m : ℕ} (hm : m∈M) : count m ≤ m.divisors.card := by
    obtain ⟨s,hs,eq⟩ := mem_image.mp hm
    have mp : m ≠ 0 := (eq ▸ (fit s hs).1).ne'
    have sub : rows.filter (fun t => weight t = m) ⊆ m.divisorsAntidiagonal := by
      intro t ht
      exact Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp ht).2,mp⟩
    change (rows.filter _).card ≤ _
    exact (card_le_card sub).trans_eq (by rw [←Nat.map_div_right_divisors,card_map])
  have range : M ⊆ Icc 1 X := by
    rintro _ hm
    obtain ⟨s,hs,rfl⟩ := mem_image.mp hm
    exact mem_Icc.mpr (fit s hs)
  have moment : ∑ m∈M, count m^2 ≤ X*(b+3).choose 3 := calc
    _ ≤ ∑ m∈M, m.divisors.card^2 := sum_le_sum fun m hm => Nat.pow_le_pow_left (fiber hm) 2
    _ ≤ ∑ m∈Icc 1 X, m.divisors.card^2 := sum_le_sum_of_subset range
    _ ≤ _ := DivisorSecondMoment.binomial b X cap
  have cs := sum_mul_sq_le_sq_mul_sq M (fun _ => (1:ℕ)) count
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at cs
  rw [mass]
  exact cs.trans (Nat.mul_le_mul_left _ moment)

/-- On the specified rectangle, at least 2^653 distinct slopes give more
than 2^618 distinct discriminants of the selected labels. -/
theorem target {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q)
    (rows : Finset Pair) (z : Pair → ℤ) (many : 2^653 ≤ rows.card)
    (box : ∀ s∈rows, 0<s.1 ∧ s.1≤9*2^327 ∧ 0<s.2 ∧ s.2≤7*2^327)
    (bounds : ∀ s∈rows, 0≤z s ∧ z s<(p*q:ℕ)) :
    2^618 < (rows.image (discriminant (p*q) z)).card := by
  let X : ℕ := 63*(2^327)^2
  have fit (s : Pair) (hs : s∈rows) : 0<weight s ∧ weight s≤X := by
    obtain ⟨up,ub,vp,vb⟩ := box _ hs
    exact ⟨Nat.mul_pos up vp,(Nat.mul_le_mul ub vb).trans (by decide +kernel)⟩
  have energy := product_energy rows fit (show X ≤ 2^660 by decide +kernel)
  have mult := four_fold hp hq hne rows z bounds
  by_contra! bad
  have prod := Nat.mul_le_mul_left 4 bad
  have upper := Nat.mul_le_mul_right (X*(660+3).choose 3) (mult.trans prod)
  have left := (Nat.pow_le_pow_left many 2).trans (energy.trans upper)
  exact (by decide +kernel : ¬ (2^653:ℕ)^2 ≤ 4*2^618*(X*(660+3).choose 3)) left

end PrimeFactors.QuotientStripDiscriminantMultiplicity
