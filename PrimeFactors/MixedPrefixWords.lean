import PrimeFactors.LowBitsCarryMenu
import PrimeFactors.MixedPrefixSlab
import PrimeFactors.MixedPrefixBand

/-! Passing from the two observed words of the product to points in an affine
lattice. The first and second coordinates are the factor quotients. -/

namespace PrimeFactors.MixedPrefixWords

open Finset

set_option exponentiation.threshold 8192

def D : ℕ := 2^704
def B : ℕ := 2^319
def Q : ℕ := 2^1023
def L : ℕ := 2^212

private theorem constants : 0<D ∧ 0<L ∧ B*D=Q ∧ B∣D ∧ D^2=2^1408 ∧ 2*Q=2^1024 ∧
    2^107*L=B ∧ (2*B*D)^2=2^2048 := by decide +kernel

private def coords (z : ℕ×ℕ) : ℤ×ℤ := ((z.1/D : ℕ),(z.2/D : ℕ))
private def slab (z : ℕ×ℕ) := (z.1/D-B)/L
private def residue (u : ℤ) := (u%(D:ℤ)).toNat

private theorem eq_residue {p : ℕ} {u : ℤ} (h : (p:ℤ)≡u [ZMOD D]) : p%D=residue u := by
  simpa only [residue,←Int.natCast_mod,Int.toNat_natCast] using congrArg Int.toNat h.eq

structure Point (step H c : ℕ) (t : ℤ×ℤ) (z : ℕ×ℕ) : Prop where
  pmin : Q≤z.1
  pmax : z.1<2*Q
  qmin : Q≤z.2
  qmax : z.2<2*Q
  oddP : Odd z.1
  oddQ : Odd z.2
  head : z.1*z.2/step=H
  tail : z.1*z.2%Q=c
  fst_res : (z.1:ℤ)≡t.1 [ZMOD D]
  snd_res : (z.2:ℤ)≡t.2 [ZMOD D]

private theorem partner {p q v : ℕ} (po : Odd p) (ql : Q≤q) (qh : q<2*Q)
    (vl : Q≤v) (vh : v<2*Q) (h : p*q≡p*v [MOD Q]) : q=v := by
  have rel := Nat.ModEq.cancel_left_of_coprime (po.coprime_two_left.pow_left 1023) h
  have rel' : (q-Q) ≡ (v-Q) [MOD Q] := Nat.ModEq.add_right_cancel' Q (by simpa [Nat.sub_add_cancel ql,Nat.sub_add_cancel vl] using rel)
  have := rel'.eq_of_lt_of_lt (by omega) (by omega); omega

private theorem quotient_unique {u x y : ℕ} (a : x%D=u) (b : y%D=u) (eq : x/D=y/D) : x=y := by
  rw [←Nat.mod_add_div x D,←Nat.mod_add_div y D,a,b,eq]

private theorem injective_fst {step H c : ℕ} {t : ℤ×ℤ} {x y : ℕ×ℕ}
    (hx : Point step H c t x) (hy : Point step H c t y) (eq : (coords x).1=(coords y).1) : x=y := by
  have p := quotient_unique (eq_residue hx.fst_res) (eq_residue hy.fst_res) (by dsimp only [coords] at eq; exact_mod_cast eq)
  exact Prod.ext p (partner hx.oddP hx.qmin hx.qmax hy.qmin hy.qmax (by have h := hx.tail.trans hy.tail.symm; rwa [←p] at h))

private theorem injective_snd {step H c : ℕ} {t : ℤ×ℤ} {x y : ℕ×ℕ}
    (hx : Point step H c t x) (hy : Point step H c t y) (eq : (coords x).2=(coords y).2) : x=y := by
  have q := quotient_unique (eq_residue hx.snd_res) (eq_residue hy.snd_res) (by dsimp only [coords] at eq; exact_mod_cast eq)
  refine Prod.ext (partner hx.oddQ hx.pmin hx.pmax hy.pmin hy.pmax ?_) q
  have ee := hx.tail.trans hy.tail.symm
  rw [←q] at ee
  simpa only [mul_comm] using ee

private theorem linear {d m p q x y : ℤ} (dn : d≠0) (md : m∣d)
    (fiber : d*m ∣ (p+d*x)*(q+d*y)-p*q) : m∣p*y+q*x := by
  have big : m∣p*y+q*x+d*(x*y) := (mul_dvd_mul_iff_left dn).mp (by
    convert fiber using 1; ring)
  exact (dvd_add_left (md.trans (dvd_mul_right ..))).mp big

private theorem congruence {step H c : ℕ} {t : ℤ×ℤ} {x y : ℕ×ℕ}
    (hx : Point step H c t x) (hy : Point step H c t y) :
    (B:ℤ)∣(x.1:ℤ)*((coords y).2-(coords x).2)+(x.2:ℤ)*((coords y).1-(coords x).1) := by
  have diff (p q : ℕ) (z : ℤ) (hp : (p:ℤ)≡z [ZMOD D]) (hq : (q:ℤ)≡z [ZMOD D]) :
      (q:ℤ)=p+(D:ℤ)*((q/D:ℕ)-(p/D:ℕ):ℤ) := by
    have h₁ := Nat.mod_add_div p D; have h₂ := Nat.mod_add_div q D
    rw [eq_residue hp] at h₁; rw [eq_residue hq] at h₂
    have heq : (q:ℤ)+D*(p/D:ℕ)=p+D*(q/D:ℕ) := by exact_mod_cast (show q+D*(p/D)=p+D*(q/D) by omega)
    linarith only [heq]
  have h := Nat.modEq_iff_dvd.mp (show x.1*x.2≡y.1*y.2 [MOD Q] from hx.tail.trans hy.tail.symm)
  push_cast at h
  have eq : (D:ℤ)*B=Q := by exact_mod_cast (constants.2.2.1 ▸ mul_comm D B)
  apply linear (d:=(D:ℤ)) (by exact_mod_cast constants.1.ne') (Int.natCast_dvd_natCast.mpr constants.2.2.2.1)
  dsimp only [coords]; rw [eq,←diff _ _ t.1 hx.fst_res hy.fst_res,←diff _ _ t.2 hx.snd_res hy.snd_res]
  exact h

/-- The low word makes each triangle determinant a multiple of the quotient
block count. This uses oddness of the first factor to cancel it modulo B. -/
private theorem determinant {step H c : ℕ} {t : ℤ×ℤ} {x y z : ℕ×ℕ}
    (hx : Point step H c t x) (hy : Point step H c t y) (hz : Point step H c t z) :
    (B:ℤ) ∣ ((coords y).1-(coords x).1)*((coords z).2-(coords x).2)-
      ((coords z).1-(coords x).1)*((coords y).2-(coords x).2) := by
  have cop : IsCoprime (B:ℤ) (x.1:ℤ) := Int.isCoprime_iff_nat_coprime.mpr (by simpa [B] using hx.oddP.coprime_two_left.pow_left 319)
  apply cop.dvd_of_dvd_mul_left
  obtain ⟨u,hu⟩ := congruence hx hy
  obtain ⟨v,hv⟩ := congruence hx hz
  refine ⟨((coords y).1-(coords x).1)*v-((coords z).1-(coords x).1)*u,?_⟩
  linear_combination ((coords y).1-(coords x).1)*hv - ((coords z).1-(coords x).1)*hu

private theorem quotient_bounds {step H c : ℕ} {t : ℤ×ℤ} {z : ℕ×ℕ} (hz : Point step H c t z) :
    B≤z.1/D ∧ z.1/D<2*B := by
  rw [Nat.le_div_iff_mul_le constants.1,Nat.div_lt_iff_lt_mul constants.1,constants.2.2.1,Nat.mul_assoc,constants.2.2.1]
  exact ⟨hz.pmin,hz.pmax⟩

private theorem bins {step H c : ℕ} {t : ℤ×ℤ} {z : ℕ×ℕ} (hz : Point step H c t z) :
    slab z<2^107 ∧ B+slab z*L≤z.1/D ∧ z.1/D≤B+slab z*L+L := by
  obtain ⟨lo,hi⟩ := quotient_bounds hz
  have hl := constants.2.1
  have num : 2^107*L=B := by decide +kernel
  let i := z.1/D-B
  have xl := Nat.div_mul_le_self i L
  have xu := Nat.lt_mul_div_succ i hl
  rw [Nat.mul_add,Nat.mul_comm L (i/L),Nat.mul_one] at xu
  dsimp only [slab]; change i/L<2^107 ∧ _; dsimp only [i] at *
  refine ⟨(Nat.div_lt_iff_lt_mul hl).mpr (num ▸ (by omega)),by omega,by omega⟩

/-- For fixed leading and trailing words and one fixed pair of factor residues,
all 2^107 quotient slabs together have at most 2^108 candidate pairs. -/
theorem word_card {step H c : ℕ} {t : ℤ×ℤ} (V : Finset (ℕ×ℕ)) (sp : 0<step) (narrow : 2*step≤D^2)
    (fixed : ∀ z∈V, Point step H c t z) : V.card≤2^108 := by
  have into : ∀ z∈V, slab z∈range (2^107) := fun z hz => mem_range.mpr (bins (fixed z hz)).1
  have local_bound (m : ℕ) : (V.filter (fun z => slab z=m)).card≤2 := by
    let slice := V.filter (fun z => slab z=m)
    by_cases empty : slice=∅
    · change slice.card≤2; rw [empty,card_empty]; decide
    obtain ⟨z₀,in₀⟩ := nonempty_iff_ne_empty.mpr empty
    have get {z : ℕ×ℕ} (hz : z∈slice) := fixed z (mem_filter.mp hz).1
    have large : H*step≤4*B^2*D^2 := calc
      _ ≤ z₀.1*z₀.2 := (get in₀).head ▸ Nat.div_mul_le_self _ _
      _ ≤ (2*Q)*(2*Q) := Nat.mul_le_mul (get in₀).pmax.le (get in₀).qmax.le
      _ = _ := by rw [←constants.2.2.1]; ring
    let r := residue t.1
    let s := residue t.2
    let ρ : ℚ := (r:ℚ)/D
    let σ : ℚ := (s:ℚ)/D
    let T : ℚ := (H*step:ℕ)/(D:ℚ)^2
    let U : ℚ := (step:ℚ)/(D:ℚ)^2
    let x₀ : ℚ := (B+m*L:ℕ)+ρ
    have inj : Set.InjOn coords (slice : Set (ℕ×ℕ)) := fun _ hx _ hy heq =>
      injective_fst (get hx) (get hy) (congrArg Prod.fst heq)
    have fd : ∀ z∈slice, ∀ y∈slice, (coords z).1=(coords y).1 → z=y :=
      fun _ hx _ hy => injective_fst (get hx) (get hy)
    have sd : ∀ z∈slice, ∀ y∈slice, (coords z).2=(coords y).2 → z=y :=
      fun _ hx _ hy => injective_snd (get hx) (get hy)
    change slice.card≤2
    rw [←card_image_of_injOn inj]
    apply MixedPrefixSlab.card_le_two_chord _ ρ σ T U x₀
    · rw [show (2:ℚ)^319=(B:ℚ) by simp only [B,Nat.cast_pow,Nat.cast_ofNat]]
      dsimp only [x₀,ρ]; push_cast; exact le_add_of_le_of_nonneg (le_add_of_nonneg_right (by positivity)) (by positivity)
    · dsimp [T]; positivity
    · simpa only [B,Nat.cast_pow,Nat.cast_ofNat] using MixedPrefixBand.top constants.1 large
    · exact MixedPrefixBand.width constants.1 narrow
    · intro P hP
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hP
      have hp := Nat.div_add_mod z.1 D
      have hq := Nat.div_add_mod z.2 D
      rw [eq_residue (get hz).fst_res] at hp
      rw [eq_residue (get hz).snd_res] at hq
      obtain ⟨_,lo,hi⟩ := bins (get hz)
      rw [(mem_filter.mp hz).2] at lo hi
      simpa only [coords,Int.cast_natCast,ρ,σ,T,U,x₀,r,s,L,Nat.cast_pow,Nat.cast_ofNat] using
        MixedPrefixBand.bounds constants.1 sp hp.symm hq.symm lo hi (get hz).head
    · intro P hP S hS eq
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hP
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hS
      exact congrArg coords (fd z hz y hy eq)
    · intro P hP S hS eq
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hP
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hS
      exact congrArg coords (sd z hz y hy eq)
    · intro P hP S hS R hR
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hP
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hS
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hR
      simpa only [MixedPrefixSlab.det,B,Nat.cast_pow,Nat.cast_ofNat] using determinant (get hx) (get hy) (get hz)
  have bound := card_le_mul_card_image_of_maps_to into 2 fun m _ => local_bound m
  simpa only [card_range] using bound

end PrimeFactors.MixedPrefixWords
