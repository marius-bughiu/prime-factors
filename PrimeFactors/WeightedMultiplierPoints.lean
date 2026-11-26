import PrimeFactors.WeightedMultiplierPell
import PrimeFactors.WeightedMultiplierRoots

/-! Count all positive-first-coordinate solutions to one positive square-norm
equation, using the normalized coordinates, their canonical slope, and the
finite count of all possible slopes. -/
namespace PrimeFactors.WeightedMultiplierPoints
open Finset WeightedMultiplierPell WeightedMultiplierRoots

private noncomputable def slopes (s t : ℕ) :=
  (range (s^2)).filter fun a => a^2 ≡ t [MOD s^2]

private def divide (g : ℕ) (z : ℕ×ℕ) : ℤ×ℤ :=
  (((z.1/g:ℕ):ℤ), ((z.2/g:ℕ):ℤ))

private def restore (g : ℕ) (w : ℤ×ℤ) : ℕ×ℕ := (g*w.1.toNat,g*w.2.toNat)

private theorem residue {s : ℕ} (hs : 0<s) (R : ℤ) :
    ∃ a<s^2, (a:ℤ) ≡ R [ZMOD (s:ℤ)^2] := by
  let h := R%(s:ℤ)^2
  have pos : (0:ℤ)<(s:ℤ)^2 := by positivity
  have hn : 0≤h := Int.emod_nonneg _ pos.ne'
  have he : (h.toNat:ℤ)=h := Int.toNat_of_nonneg hn
  refine ⟨h.toNat,?_,?_⟩
  · have bound : (h.toNat:ℤ)<(s:ℤ)^2 := by
      rw [he]; exact Int.emod_lt_of_pos R pos
    exact_mod_cast bound
  · rw [he]
    exact Int.emod_emod ..

/-- Every solution has a label consisting of s dividing C and one tested
natural slope a in [0,s²). Both the normalized coordinates and their inverse
are explicit. -/
private theorem label {z : ℕ×ℕ} {C t K : ℕ} (cp : 0<C) (xp : 0<z.1)
    (norm : z.1^2=t*z.2^2+C^2) (width : z.1<2^K) :
    ∃ s∈C.divisors, ∃ a∈slopes s t,
      let g := C/s
      let w := divide g z
      restore g w=z ∧ w.1^2-(t:ℤ)*w.2^2=(s:ℤ)^2 ∧
      (s:ℤ)^2∣w.1-a*w.2 ∧ 0<w.1 ∧ 0≤w.2 ∧ w.1<2^K := by
  let g := z.1.gcd z.2
  let s := C/g
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ xp
  obtain ⟨gc,R,rr,loc,_⟩ := normalized_class norm xp
  have back : C/s=g := Nat.div_div_self gc cp.ne'
  have sg : s∈C.divisors := Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd gc,cp.ne'⟩
  have spos := Nat.pos_of_mem_divisors sg
  obtain ⟨a,ha,ar⟩ := residue spos R
  have slope : a^2 ≡ t [MOD s^2] := by
    apply Int.natCast_modEq_iff.mp
    push_cast
    exact (ar.pow 2).trans (Int.modEq_iff_dvd.mpr rr).symm
  refine ⟨s,sg,a,mem_filter.mpr ⟨mem_range.mpr ha,slope⟩,?_⟩
  rw [back]
  change restore g (divide g z)=z ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  have dx : g ∣ z.1 := Nat.gcd_dvd_left ..
  have dy : g ∣ z.2 := Nat.gcd_dvd_right ..
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact Prod.ext (Nat.mul_div_cancel' dx) (Nat.mul_div_cancel' dy)
  · have h : ((z.1/g:ℕ):ℤ)^2=(t:ℤ)*((z.2/g:ℕ):ℤ)^2+(s:ℤ)^2 := by
      exact_mod_cast normalize norm gp dx dy
    change ((z.1/g:ℕ):ℤ)^2-(t:ℤ)*((z.2/g:ℕ):ℤ)^2=(s:ℤ)^2
    omega
  · exact Int.modEq_iff_dvd.mp
      ((ar.mul_right (z.2/g:ℕ)).trans (Int.modEq_iff_dvd.mpr loc))
  · change (0:ℤ)<((z.1/g:ℕ):ℤ)
    exact_mod_cast Nat.div_pos (Nat.le_of_dvd xp dx) gp
  · exact Int.natCast_nonneg _
  · change ((z.1/g:ℕ):ℤ)<2^K
    exact_mod_cast (Nat.div_le_self z.1 g).trans_lt width

/-- For each fixed positive C and squarefree t, at most twice the first
coordinate bit bound times τ(C²) distinct natural coordinate pairs occur.
This includes second coordinate zero and radicand one. -/
theorem points {C t K : ℕ} (cp : 0<C) (free : Squarefree t) (S : Finset (ℕ×ℕ))
    (member : ∀ z∈S, 0<z.1 ∧ z.1^2=t*z.2^2+C^2 ∧ z.1<2^K) :
    S.card ≤ 2*K*(C^2).divisors.card := by
  classical
  let cell (s a : ℕ) := (S.image (divide (C/s))).filter fun w =>
    w.1^2-(t:ℤ)*w.2^2=(s:ℤ)^2 ∧ (s:ℤ)^2∣w.1-a*w.2 ∧
      0<w.1 ∧ 0≤w.2 ∧ w.1<2^K
  let original (s a : ℕ) := (cell s a).image (restore (C/s))
  have cover : S ⊆ C.divisors.biUnion (fun s => (slopes s t).biUnion (original s)) := by
    intro z hz
    obtain ⟨pos,norm,width⟩ := member z hz
    obtain ⟨s,hs,a,ha,eq,all⟩ := label cp pos norm width
    exact mem_biUnion.mpr ⟨s,hs,mem_biUnion.mpr ⟨a,ha,
      mem_image.mpr ⟨_,mem_filter.mpr ⟨mem_image_of_mem _ hz,all⟩,eq⟩⟩⟩
  have sized (s a : ℕ) (hs : s∈C.divisors) (ha : a∈slopes s t) : (original s a).card≤K := by
    have spos := Nat.pos_of_mem_divisors hs
    have tp := Nat.pos_of_ne_zero free.ne_zero
    have hr := Int.natCast_modEq_iff.mpr (mem_filter.mp ha).2
    push_cast at hr
    exact card_image_le.trans (class_card (by positivity : (0:ℤ)<(s:ℤ)^2)
      (by exact_mod_cast tp : (0:ℤ)<t) (Int.modEq_iff_dvd.mp hr.symm) _ K
      (fun _ h => (mem_filter.mp h).2))
  calc
    S.card ≤ _ := card_le_card cover
    _ ≤ ∑ s∈C.divisors, ((slopes s t).biUnion (original s)).card := card_biUnion_le
    _ ≤ ∑ s∈C.divisors, 2^s.primeFactors.card*(2*K) := by
      apply sum_le_sum
      intro s hs
      calc
        _ ≤ (slopes s t).card*K := card_biUnion_le_card_mul _ _ K (fun a ha => sized s a hs ha)
        _ ≤ 2^(s.primeFactors.card+1)*K :=
          Nat.mul_le_mul_right _ (slope_count (Nat.pos_of_mem_divisors hs) free)
        _ = _ := by rw [pow_succ,mul_assoc]
    _ = _ := by rw [←sum_mul,divisor_classes,Nat.mul_comm]

end PrimeFactors.WeightedMultiplierPoints
