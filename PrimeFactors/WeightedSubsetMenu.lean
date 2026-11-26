import PrimeFactors.WeightedMultiplierLabels
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Counting complete weighted Fermat menus by the sum of the eight raw ceilings. -/
namespace PrimeFactors.WeightedSubsetMenu
open Finset WeightedMultiplierLabels
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

abbrev Vector := Fin 8 → Fin 2 → ℕ

/-- The full menu has the first two admissible ranks at each weight from one to eight. -/
def vector (n : ℕ) : Vector := fun w i => labelAt n (w.val+1) i.val

def raw (n : ℕ) (w : Fin 8) : ℕ := ceilSqrt (4*(w.val+1)*n)

noncomputable def total (n : ℕ) := ∑ w : Fin 8, raw n w

theorem raw_mono {m n : ℕ} (h : m≤n) (w : Fin 8) : raw m w ≤ raw n w :=
  ceilSqrt_le_iff.mpr ((Nat.mul_le_mul_left _ h).trans (ceilSqrt_le_iff.mp (le_refl _)))

private theorem ordered_equal {m n : ℕ} (order : m≤n) (eq : total m=total n) (w : Fin 8) :
    raw m w = raw n w := by
  by_contra! ne
  have h := sum_lt_sum (fun t (_ : t∈(univ : Finset (Fin 8))) => raw_mono order t)
    ⟨w,mem_univ _,lt_of_le_of_ne (raw_mono order w) ne⟩
  exact (Nat.ne_of_lt h) eq

/-- In each residue class, a single integer determines all eight raw
ceilings, and hence every admissible rank at every menu weight. -/
theorem equal_labels {m n : ℕ} (res : m≡n [MOD 24]) (eq : total m=total n) (w : Fin 8)
    (i : ℕ) : labelAt m (w.val+1) i=labelAt n (w.val+1) i := by
  have ceilings : raw m w=raw n w := by
    rcases le_total m n with h|h
    · exact ordered_equal h eq w
    · exact (ordered_equal h eq.symm w).symm
  have orig := res.add_left (w.val+1)
  have step := (orig.mul_left 2).gcd_eq
  rw [Nat.gcd_comm _ 24,Nat.gcd_comm _ 24] at step
  have div := Nat.gcd_dvd_left 24 (2*(w.val+1+n))
  have same := orig.of_dvd div
  unfold raw at ceilings
  simp only [labelAt,step,ceilings]
  rw [show (w.val+1+m) % Nat.gcd 24 (2*(w.val+1+n)) = _ from same]

noncomputable def code (n : ℕ) := (n%24,total n)

/-- A collision of the short codes preserves the entire sixteen-label vector. -/
theorem equal_vector {m n : ℕ} (h : code m=code n) : vector m=vector n := by
  funext w i
  exact equal_labels (congrArg Prod.fst h) (congrArg Prod.snd h) w i

private theorem count_from_codes (S : Finset ℕ) (C : Finset (ℕ×ℕ))
    (covers : ∀ n∈S, code n∈C) : (S.image vector).card≤C.card := by
  classical
  let decode (key : ℕ×ℕ) : Vector := if h : ∃ n∈S, code n=key then vector h.choose else 0
  have sub : S.image vector ⊆ C.image decode := by
    intro a ha
    obtain ⟨n,hn,rfl⟩ := mem_image.mp ha
    have valid : ∃ m∈S, code m=code n := ⟨n,hn,rfl⟩
    refine mem_image.mpr ⟨code n,covers n hn,?_⟩
    dsimp only [decode]
    rw [dif_pos valid]
    exact equal_vector valid.choose_spec.2
  exact (card_le_card sub).trans card_image_le

private noncomputable def lower : Fin 8 → ℕ := ![724,1024,1254,1448,1619,1773,1915,2048]
private noncomputable def upper : Fin 8 → ℕ := ![1024,1449,1774,2048,2290,2509,2710,2897]

private theorem weights : ∀ w : Fin 8,
    (lower w)^2≤8*(w.val+1)*256^2 ∧ 16*(w.val+1)*256^2≤(upper w)^2 := by decide +kernel

private theorem endpoints :
    (∑ w : Fin 8, lower w)=11805 ∧ (∑ w : Fin 8, upper w)=16701 := by
  simp [Fin.sum_univ_succ,lower,upper]

private abbrev Q : ℕ := 2^1015
private abbrev X : ℕ := 2^1023

private theorem scale : X=256*Q := by decide +kernel

private theorem raw_high {n : ℕ} (h : n ≤ 4*X^2) (w : Fin 8) : raw n w ≤ upper w*Q := by
  apply ceilSqrt_le_iff.mpr
  have wbound := (weights w).2
  calc
    4*(w.val+1)*n ≤ 4*(w.val+1)*(4*X^2) := Nat.mul_le_mul_left _ h
    _ = (16*(w.val+1)*256^2)*Q^2 := by rw [scale]; ring
    _ ≤ (upper w)^2*Q^2 := Nat.mul_le_mul_right _ wbound
    _ = _ := (mul_pow ..).symm

private theorem raw_low {n : ℕ} (h : 2*X^2≤n) (w : Fin 8) : lower w*Q≤raw n w := by
  apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
  have wbound := (weights w).1
  calc
    (lower w*Q)^2 = (lower w)^2*Q^2 := mul_pow ..
    _ ≤ (8*(w.val+1)*256^2)*Q^2 := Nat.mul_le_mul_right _ wbound
    _ = 4*(w.val+1)*(2*X^2) := by rw [scale]; ring
    _ ≤ 4*(w.val+1)*n := Nat.mul_le_mul_left _ h
    _ ≤ (raw n w)^2 := ceilSqrt_le_iff.mp (le_refl _)

private theorem total_high {n : ℕ} (h : n≤4*X^2) : total n≤16701*Q := by
  calc
    total n≤∑ w : Fin 8, upper w*Q := sum_le_sum (fun i _ => raw_high h i)
    _ = (∑ w : Fin 8, upper w)*Q := (sum_mul ..).symm
    _ = 16701*Q := congrArg (·*Q) endpoints.2

private theorem total_low {n : ℕ} (h : 2*X^2≤n) : 11805*Q≤total n := by
  calc
    11805*Q=(∑ w : Fin 8, lower w)*Q := congrArg (·*Q) endpoints.1.symm
    _ = ∑ w : Fin 8, lower w*Q := sum_mul ..
    _ ≤ total n := sum_le_sum (fun i _ => raw_low h i)

/-- Across all positive inputs below 4X² (even including zero), the full menu
takes fewer than 1,566X values. This bound uses all 24 residue classes. -/
theorem all_menus (S : Finset ℕ) (inputs : ∀ n∈S, n≤4*(2^1023)^2) :
    (S.image vector).card < 1566*2^1023 := by
  let codes := range 24 ×ˢ range (16701*Q+1)
  have h := count_from_codes S codes (fun n hn => mem_product.mpr
    ⟨mem_range.mpr (Nat.mod_lt n (by decide)),mem_range.mpr (Nat.lt_succ_of_le (total_high (inputs n hn)))⟩)
  apply h.trans_lt
  dsimp only [codes]
  rw [card_product,card_range,card_range]
  decide +kernel

private noncomputable def units := (range 24).filter (·.Coprime 24)

/-- Product width and coprimality to 24 put the budget at 153X+8.
No distribution assumption or factor labels enter this count. -/
theorem target_menus (S : Finset ℕ)
    (inputs : ∀ n∈S, 2*(2^1023)^2≤n ∧ n≤4*(2^1023)^2 ∧ n.Coprime 24) :
    (S.image vector).card≤153*2^1023+8 := by
  let codes := units ×ˢ Icc (11805*Q) (16701*Q)
  have h := count_from_codes S codes (fun n hn => by
    obtain ⟨lo,hi,cop⟩ := inputs n hn
    exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (by decide)),
      (Nat.mod_modEq n 24).gcd_eq.trans cop⟩, mem_Icc.mpr ⟨total_low lo,total_high hi⟩⟩)
  apply h.trans
  dsimp only [codes]
  rw [card_product,Nat.card_Icc,show units.card=8 by decide +kernel]
  decide +kernel

attribute [local irreducible] MixedPrefixSample.primes MixedPrefixSample.ordered MixedPrefixSample.eligible

/-- The same budget for the actual eligible semiprimes, each represented by
its unique increasingly ordered prime pair. -/
theorem eligible_menus :
    (MixedPrefixSample.eligible.image (fun z => vector (z.1*z.2))).card≤153*2^1023+8 := by
  classical
  let S := MixedPrefixSample.eligible.image (fun z => z.1*z.2)
  rw [show MixedPrefixSample.eligible.image (fun z => vector (z.1*z.2))=S.image vector by
    simp only [S,image_image,Function.comp_def]]
  apply target_menus
  intro n hn
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hn
  rw [MixedPrefixSample.eligible,MixedPrefixSample.sample,mem_filter] at hz
  obtain ⟨hp,hq,_,lo,_⟩ := (MixedPrefixSample.mem_ordered (E:=fun _ => True) (z:=z)).mp hz.1
  rw [MixedPrefixSample.primes,mem_filter,mem_Ico] at hp hq
  have lx : 24<MixedPrefixSample.X := by decide +kernel
  have upper := Nat.mul_le_mul hp.1.2.le hq.1.2.le
  have cop (p : ℕ) (pr : p.Prime) (big : MixedPrefixSample.X≤p) :=
    pr.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide : 0<24) (lx.trans_le big))
  exact ⟨lo,upper.trans_eq (by decide +kernel),Nat.coprime_mul_iff_left.mpr
    ⟨cop _ hp.2 hp.1.1,cop _ hq.2 hq.1.1⟩⟩

end PrimeFactors.WeightedSubsetMenu
