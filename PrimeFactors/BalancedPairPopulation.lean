import PrimeFactors.WeightedCrowdingEstimates
import Mathlib.Data.Nat.Size

/-! Lower bound on the number of *distinct products* with the specified
factor and product bit lengths, from Dusart's explicit pair of inequalities. -/
namespace PrimeFactors.BalancedPairPopulation
open Finset Real WeightedCrowdingEstimates
set_option maxRecDepth 4096
set_option exponentiation.threshold 4096
attribute [local irreducible] Finset.Ico Finset.Ioc Nat.primeCounting

/-- Sorted distinct factors, both of width 1024 and with product of width 2048. -/
noncomputable def pairs : Finset (ℕ×ℕ) := by
  classical
  let pool := (Ico (2^1023) (2^1024)).filter Nat.Prime
  exact (pool ×ˢ pool).filter fun z => z.1<z.2 ∧ 2^2047≤z.1*z.2

private theorem width (p k : ℕ) : p.size=k+1 ↔ 2^k≤p ∧ p<2^(k+1) := by
  rw [←Nat.lt_size,←Nat.size_le]
  omega

theorem mem_pairs {p q : ℕ} :
    (p,q)∈pairs ↔ p.Prime ∧ q.Prime ∧ p<q ∧ p.size=1024 ∧ q.size=1024 ∧ (p*q).size=2048 := by
  classical
  simp only [pairs,mem_filter,mem_product,mem_Ico]
  rw [show p.size=1024 ↔ _ from width p 1023,show q.size=1024 ↔ _ from width q 1023,
    show (p*q).size=2048 ↔ _ from width _ 2047]
  constructor
  · rintro ⟨⟨⟨hp,pp⟩,⟨hq,qp⟩⟩,less,cut⟩
    exact ⟨pp,qp,less,hp,hq,cut,(Nat.mul_lt_mul_of_lt_of_le hp.2 hq.2.le (by omega)).trans_le
      (by decide +kernel : (2^1024)*(2^1024)≤2^2048)⟩
  · rintro ⟨pp,qp,less,hp,hq,cut,_⟩
    exact ⟨⟨⟨hp,pp⟩,⟨hq,qp⟩⟩,less,cut⟩

/-- The finite set of products, each occurring once. -/
noncomputable def products := pairs.image fun z => z.1*z.2

attribute [local irreducible] pairs

private theorem recover {p q a b : ℕ} (pp : p.Prime) (ap : a.Prime) (bp : b.Prime)
    (lt : p<q) (ab : a<b) (eq : p*q=a*b) : (p,q)=(a,b) := by
  have dvd : p∣a*b := eq ▸ dvd_mul_right p q
  rcases pp.dvd_mul.mp dvd with left | right
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq pp ap).mp left
    exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_left pp.pos eq)
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq pp bp).mp right
    rw [Nat.mul_comm a p] at eq
    have := Nat.eq_of_mul_eq_mul_left pp.pos eq
    omega

private theorem recover_image (S : Finset (ℕ×ℕ)) (T : Finset ℕ)
    (image_eq : T=S.image (fun z => z.1*z.2))
    (shape : ∀ v∈S, v.1.Prime ∧ v.2.Prime ∧ v.1<v.2) : T.card=S.card := by
  rw [image_eq]
  exact card_image_of_injOn (fun v hv w hw e =>
    recover (shape v hv).1 (shape w hw).1 (shape w hw).2.1
      (shape v hv).2.2 (shape w hw).2.2 e)

theorem card_products : products.card=pairs.card := by
  apply recover_image pairs products rfl
  intro v hv
  exact ⟨(mem_pairs.mp hv).1,(mem_pairs.mp hv).2.1,(mem_pairs.mp hv).2.2.1⟩

private abbrev Y : ℕ := 2^1017
private def band (a b : ℕ) := (Ioc (a*Y) (b*Y)).filter Nat.Prime
private abbrev lower (a b : ℕ) := ((707*b-710*a)*Y)/501970

private theorem estimates (dusart : Dusart) {n : ℕ} (lo : 2^1023≤n) (hi : n≤2^1024) :
    707*n.primeCounting≤n ∧ n≤710*n.primeCounting := by
  have pos : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have small := log_le_log (by positivity : (0:ℝ)<2^1023) (by exact_mod_cast lo : (2:ℝ)^1023≤n)
  have large := log_le_log pos (by exact_mod_cast hi : (n:ℝ)≤2^1024)
  rw [log_pow] at small large
  norm_num only [Nat.cast_ofNat] at small large
  have l : (707:ℝ)≤log n-11/10 := by linarith only [small,log_two_gt_d9]
  have r : log n-1≤(710:ℝ) := by linarith only [large,log_two_lt_d9]
  obtain ⟨left,right⟩ := dusart n ((by decide +kernel : 60184<2^1023).trans_le lo)
  have u := (le_div_iff₀ (by linarith only [l])).mp right
  have v := (div_le_iff₀ (by linarith only [l])).mp left
  constructor
  · exact_mod_cast (mul_le_mul_of_nonneg_right l (Nat.cast_nonneg n.primeCounting)).trans
      ((mul_comm _ _).trans_le u)
  · have right := v.trans (mul_le_mul_of_nonneg_left r (Nat.cast_nonneg n.primeCounting))
    rw [mul_comm (n.primeCounting:ℝ)] at right
    exact_mod_cast right

private theorem band_lower (dusart : Dusart) {a b : ℕ} (lo : 64≤a) (ord : a≤b) (hi : b≤128)
    (test : 501970*lower a b+710*(a*Y) ≤ 707*(b*Y)) : lower a b≤(band a b).card := by
  have ab := Nat.mul_le_mul_right Y ord
  have ax : 2^1023≤a*Y := calc
    _ = 64*Y := by decide +kernel
    _ ≤ _ := Nat.mul_le_mul_right Y lo
  have bx : b*Y≤2^1024 := (Nat.mul_le_mul_right Y hi).trans (by decide +kernel)
  have left := (estimates dusart ax (ab.trans bx)).1
  have right := (estimates dusart (ax.trans ab) bx).2
  have diff := count_eq _ _ ab
  change (a*Y).primeCounting+(band a b).card=(b*Y).primeCounting at diff
  omega

private def sorted (P : Finset ℕ) := P.offDiag.filter fun z => z.1<z.2

private theorem sorted_lower (P : Finset ℕ) : P.card.choose 2 ≤ (sorted P).card := by
  let H := sorted P
  have incl : P.offDiag ⊆ H ∪ H.image Prod.swap := by
    rintro ⟨p,q⟩ h
    obtain ⟨hp,hq,ne⟩ := mem_offDiag.mp h
    obtain lt|gt := lt_or_gt_of_ne ne
    · exact mem_union_left _ (mem_filter.mpr ⟨h,lt⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨(q,p),mem_filter.mpr
        ⟨mem_offDiag.mpr ⟨hq,hp,ne.symm⟩,gt⟩,rfl⟩)
  have cnt : P.offDiag.card ≤ 2*H.card := (card_le_card incl).trans
    ((card_union_le ..).trans (by simpa only [two_mul] using Nat.add_le_add_left (card_image_le (s:=H) (f:=Prod.swap)) H.card))
  rw [Nat.choose_two_right]
  apply Nat.div_le_of_le_mul'
  simpa [offDiag_card,Nat.mul_sub] using cnt

private theorem into_pairs {a b c d p q : ℕ} (hp : p∈band a b) (hq : q∈band c d) (ord : p<q)
    (al : 64≤a) (cl : 64≤c) (bh : b≤128) (dh : d≤128) (margin : 8192≤a*c) : (p,q)∈pairs := by
  have bounds {z i j : ℕ} (mem : z∈band i j) (low : 64 ≤ i) (high : j≤128) :
      z∈(Ico (2^1023) (2^1024)).filter Nat.Prime := by
    obtain ⟨zmem,prime⟩ := mem_filter.mp mem
    obtain ⟨zl,zu⟩ := mem_Ioc.mp zmem
    have zlo : 2^1023≤z := (Nat.mul_le_mul_right Y low).trans zl.le
    have zhi : z≤2^1024 := zu.trans (Nat.mul_le_mul_right Y high)
    have ne : z≠2^1024 := fun e => (Nat.Prime.not_prime_pow (by decide : 2≤1024)) (e ▸ prime)
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨zlo,lt_of_le_of_ne zhi ne⟩,prime⟩
  unfold pairs
  refine mem_filter.mpr ⟨mem_product.mpr ⟨bounds hp al bh,bounds hq cl dh⟩,ord,?_⟩
  calc
    2^2047 = 8192*Y^2 := by decide +kernel
    _ ≤ (a*c)*Y^2 := Nat.mul_le_mul_right _ margin
    _ = (a*Y)*(c*Y) := by ring
    _ ≤ p*q := Nat.mul_le_mul (mem_Ioc.mp (mem_filter.mp hp).1).1.le
      (mem_Ioc.mp (mem_filter.mp hq).1).1.le

/-- Dusart's unconditional inequalities (6.6) are the only analytic premise. -/
theorem population (dusart : Dusart) : 2^2025 ≤ pairs.card := by
  let A := sorted (band 91 128)
  let B := band 80 91 ×ˢ band 103 128
  let C := band 72 80 ×ˢ band 114 128
  have bands {a b n : ℕ} (h : n∈band a b) : a*Y<n ∧ n≤b*Y := mem_Ioc.mp (mem_filter.mp h).1
  have inA {p q : ℕ} (h : (p,q)∈A) : p∈band 91 128 ∧ q∈band 91 128 ∧ p<q := by
    obtain ⟨off,lt⟩ := mem_filter.mp h
    exact ⟨(mem_offDiag.mp off).1,(mem_offDiag.mp off).2.1,lt⟩
  have disAB : Disjoint A B := by
    apply disjoint_left.mpr
    rintro ⟨p,q⟩ ha hb
    exact (not_lt_of_ge (bands (mem_product.mp hb).1).2) (bands (inA ha).1).1
  have disC : Disjoint (A∪B) C := by
    apply disjoint_left.mpr
    rintro ⟨p,q⟩ hab hc
    have top := (bands (mem_product.mp hc).1).2
    rcases mem_union.mp hab with ha|hb
    · exact (not_lt_of_ge (top.trans (by decide +kernel : 80*Y≤91*Y))) (bands (inA ha).1).1
    · exact (not_lt_of_ge top) (bands (mem_product.mp hb).1).1
  have cover : (A∪B)∪C ⊆ pairs := by
    rintro ⟨p,q⟩ hit
    rcases mem_union.mp hit with earlier|hc
    · rcases mem_union.mp earlier with ha|hb
      · obtain ⟨hp,hq,lt⟩ := inA ha
        exact into_pairs hp hq lt (by decide) (by decide) (by decide) (by decide) (by decide)
      · obtain ⟨hp,hq⟩ := mem_product.mp hb
        have ord := (bands hp).2.trans_lt ((by decide +kernel : 91*Y≤103*Y).trans_lt (bands hq).1)
        exact into_pairs hp hq ord (by decide) (by decide) (by decide) (by decide) (by decide)
    · obtain ⟨hp,hq⟩ := mem_product.mp hc
      have ord := (bands hp).2.trans_lt ((by decide +kernel : 80*Y≤114*Y).trans_lt (bands hq).1)
      exact into_pairs hp hq ord (by decide) (by decide) (by decide) (by decide) (by decide)
  have all := card_le_card cover
  rw [card_union_of_disjoint disC,card_union_of_disjoint disAB] at all
  change (sorted (band 91 128)).card + _ + _ ≤ _ at all
  simp only [B,C,card_product] at all
  have cell {a b : ℕ} (l : 64≤a) (m : a≤b) (h : b≤128)
      (v : 501970*lower a b+710*(a*Y) ≤ 707*(b*Y)) := band_lower dusart l m h v
  have hA := (Nat.choose_le_choose 2 (cell (a:=91) (b:=128) (by decide) (by decide) (by decide) (by decide +kernel))).trans (sorted_lower _)
  have hB := Nat.mul_le_mul (cell (a:=80) (b:=91) (by decide) (by decide) (by decide) (by decide +kernel))
    (cell (a:=103) (b:=128) (by decide) (by decide) (by decide) (by decide +kernel))
  have hC := Nat.mul_le_mul (cell (a:=72) (b:=80) (by decide) (by decide) (by decide) (by decide +kernel))
    (cell (a:=114) (b:=128) (by decide) (by decide) (by decide) (by decide +kernel))
  exact (show 2^2025 ≤ (lower 91 128).choose 2 + lower 80 91*lower 103 128 + lower 72 80*lower 114 128 by
    rw [Nat.choose_two_right]; decide +kernel).trans ((Nat.add_le_add (Nat.add_le_add hA hB) hC).trans all)

theorem population_products (dusart : Dusart) : 2^2025 ≤ products.card :=
  by rw [card_products]; exact population dusart

end PrimeFactors.BalancedPairPopulation
