import PrimeFactors.ChebyshevPrimeSample
import PrimeFactors.FactorSum
import PrimeFactors.Fermat

/-! Frequency of a product becoming an integer square after adding an offset.
The offsets can be any fixed nonnegative integers. The same menu is used for
every product in the balanced 2048-bit prime-pair sample. -/
namespace PrimeFactors.SmallNormSquarePopulation

open Finset MixedPrefixSample
set_option exponentiation.threshold 8192
set_option maxRecDepth 8192

private def halfWidth : ℕ := 75*2^1015

private theorem square_eq {u : ℕ} (h : IsSquare u) : u.sqrt^2=u := by
  obtain ⟨x,rfl⟩ := h
  rw [Nat.sqrt_eq,pow_two]

/-- A fixed offset translates the product interval. Its square roots occupy
less than 75/256 of the original factor-width ceiling at every offset. -/
theorem root_window {N d : ℕ} (lo : 2^2047≤N) (hi : N<2^2048) (sq : IsSquare (N+d)) :
    let b := ceilSqrt (2^2047+d)
    b≤(N+d).sqrt ∧ (N+d).sqrt<b+75*2^1016 := by
  let b := ceilSqrt (2^2047+d)
  let H := 75*2^1016
  let A := 181*2^1016
  have floors : A^2≤2^2047 := by decide +kernel
  have span : 2^2047≤2*A*H+H^2 := by decide +kernel
  have b2 : 2^2047+d≤b^2 := ceilSqrt_le_iff.mp le_rfl
  have ab : A≤b := (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
    (floors.trans ((Nat.le_add_right ..).trans b2))
  have multiply := Nat.mul_le_mul_right H ab
  have eq := square_eq sq
  change b≤(N+d).sqrt ∧ (N+d).sqrt<b+H
  refine ⟨ceilSqrt_le_iff.mpr (by rw [eq]; omega),?_⟩
  apply lt_of_not_ge
  intro large
  have square := Nat.pow_le_pow_left large 2
  have limit : N<2*2^2047 := by simpa only [show (2:ℕ)^2048=2*2^2047 by decide +kernel] using hi
  nlinarith only [limit,square,b2,eq,span,multiply]

attribute [local irreducible] ordered sample primes eligible

private theorem pair_data {E : ℕ → Prop} {z : ℕ×ℕ} (h : z∈sample E) :
    z.1.Prime ∧ z.2.Prime ∧ z.1<z.2 ∧ Odd (z.1*z.2) ∧
    2^2047≤z.1*z.2 ∧ z.1*z.2<2^2048 ∧ E (z.1*z.2) := by
  rw [sample,mem_filter] at h
  obtain ⟨p,q,_,lo,event⟩ := (mem_ordered (E:=E) (z:=z)).mp h.1
  simp only [primes,mem_filter,mem_Ico] at p q
  have large : 2<X := by decide +kernel
  have pl := p.1.1
  have ql := q.1.1
  have upper := Nat.mul_lt_mul_of_lt_of_le p.1.2 q.1.2.le (show 0<2*X by omega)
  refine ⟨p.2,q.2,h.2,(p.2.odd_of_ne_two (by omega)).mul (q.2.odd_of_ne_two (by omega)),
    ?_,?_,event⟩
  · simpa only [show 2*X^2=2^2047 by decide +kernel] using lo
  · simpa only [show 2*X*(2*X)=2^2048 by decide +kernel] using upper

private theorem rootParity {N d : ℕ} (odd : Odd N) (sq : IsSquare (N+d)) :
    (N+d).sqrt%2 = (1+d%2)%2 := by
  have power (x : ℕ) : x^2%2=x%2 := by
    rw [Nat.pow_mod]
    rcases Nat.mod_two_eq_zero_or_one x with h|h <;> rw [h]
  rw [←power,square_eq sq,Nat.add_mod,Nat.odd_iff.mp odd]

private theorem parity_count {α : Type*} (S : Finset α) (root : α → ℕ) (b w parity : ℕ)
    (box : ∀ x∈S, b≤root x ∧ root x<b+2*w ∧ root x%2=parity)
    (inj : ∀ x∈S, ∀ y∈S, root x=root y → x=y) : S.card ≤ w := by
  let index (x : α) := (root x-b)/2
  calc
    _ ≤ (range w).card := by
      apply card_le_card_of_injOn index
      · intro x hx
        obtain ⟨_,size,_⟩ := box x hx
        apply mem_range.mpr
        dsimp only [index]
        omega
      · intro x hx y hy eq
        have wx := box x hx
        have wy := box y hy
        change (root x-b)/2=(root y-b)/2 at eq
        exact inj x hx y hy (by omega)
    _ = _ := card_range _

private theorem doubleWidth : 75*2^1016=2*halfWidth := by decide +kernel

private def root (d : ℕ) (z : ℕ×ℕ) := (z.1*z.2+d).sqrt

private theorem index_window {d : ℕ} {z : ℕ×ℕ} (hz : z∈sample (fun N => IsSquare (N+d))) :
    ceilSqrt (2^2047+d)≤root d z ∧ root d z<ceilSqrt (2^2047+d)+2*halfWidth ∧
    root d z%2=(1+d%2)%2 := by
  obtain ⟨_,_,_,odd,lo,hi,sq⟩ := pair_data (E:=fun N => IsSquare (N+d)) (z:=z) hz
  have w := root_window lo hi sq
  rw [doubleWidth] at w
  exact ⟨w.1,w.2,rootParity odd sq⟩

private theorem equal_pairs {d : ℕ} {x y : ℕ×ℕ} (xp : x.1.Prime)
    (yp : y.1.Prime) (yq : y.2.Prime) (xlt : x.1<x.2) (ylt : y.1<y.2)
    (xs : IsSquare (x.1*x.2+d)) (ys : IsSquare (y.1*y.2+d)) (same : root d x=root d y) :
    x=y := by
  have sq : x.1*x.2+d=y.1*y.2+d :=
    (square_eq xs).symm.trans ((congrArg (fun r : ℕ => r^2) same).trans (square_eq ys))
  obtain ⟨p,q⟩ := ordered_semiprime_pair_unique yp yq ylt.le xlt.le xp.one_lt (Nat.add_right_cancel sq)
  exact Prod.ext p q

private theorem root_inj (d : ℕ) : ∀ x∈sample (fun N => IsSquare (N+d)),
    ∀ y∈sample (fun N => IsSquare (N+d)), root d x=root d y → x=y := by
  intro x hx y hy same
  have px := pair_data (E:=fun N => IsSquare (N+d)) (z:=x) hx
  have py := pair_data (E:=fun N => IsSquare (N+d)) (z:=y) hy
  exact equal_pairs px.1 py.1 py.2.1 px.2.2.1 py.2.2.1 px.2.2.2.2.2.2 py.2.2.2.2.2.2 same

/-- One fixed offset has at most 75·2^1015 successes. Distinct pairs giving
the same square root would have the same product and the same sorted factors. -/
theorem one_count (d : ℕ) : (sample (fun N => IsSquare (N+d))).card ≤ 75*2^1015 :=
  parity_count _ (root d) _ halfWidth _ (fun _ h => index_window h) (root_inj d)

/-- A menu may reuse roots across offsets. Summing the single-offset counts
is a rigorous upper bound including such overlaps. -/
theorem menu_count (offsets : Finset ℕ) :
    (sample (fun N => ∃ d∈offsets, IsSquare (N+d))).card ≤ offsets.card*(75*2^1015) := by
  classical
  have sub : sample (fun N => ∃ d∈offsets, IsSquare (N+d)) ⊆
      offsets.biUnion (fun d => sample (fun N => IsSquare (N+d))) := by
    intro z hz
    simp only [sample,mem_filter,mem_ordered] at hz
    obtain ⟨⟨p,q,ne,size,d,hd,sq⟩,lt⟩ := hz
    exact mem_biUnion.mpr ⟨d,hd,by simp only [sample,mem_filter,mem_ordered]; exact ⟨⟨p,q,ne,size,sq⟩,lt⟩⟩
  exact (card_le_card sub).trans (card_biUnion_le_card_mul _ _ _ (fun d _ => one_count d))

theorem one_frequency (d : ℕ) :
    2^1000*(sample (fun N => IsSquare (N+d))).card < eligible.card := by
  have cnt := Nat.mul_le_mul_left (21000000*2^1000) (one_count d)
  have num : 21000000*2^1000*(75*2^1015) ≤ 2^2046 := by decide +kernel
  apply Nat.lt_of_mul_lt_mul_left (a:=21000000)
  simpa only [Nat.mul_assoc] using (cnt.trans num).trans_lt ChebyshevPrimeSample.eligible_count

theorem menu_frequency (offsets : Finset ℕ) (cap : offsets.card≤2^40) :
    2^960*(sample (fun N => ∃ d∈offsets, IsSquare (N+d))).card < eligible.card := by
  have cnt := (menu_count offsets).trans (Nat.mul_le_mul_right _ cap)
  have scaled := Nat.mul_le_mul_left (21000000*2^960) cnt
  have num : 21000000*2^960*(2^40*(75*2^1015))≤2^2046 := by decide +kernel
  apply Nat.lt_of_mul_lt_mul_left (a:=21000000)
  simpa only [Nat.mul_assoc] using (scaled.trans num).trans_lt ChebyshevPrimeSample.eligible_count

/-- Distinct sorted primes in this sample give a nonsquare product. In
particular adding the zero offset cannot succeed. -/
theorem nonsquare {E : ℕ → Prop} {z : ℕ×ℕ} (inside : z∈sample E) : ¬IsSquare (z.1*z.2) := by
  obtain ⟨p,q,lt,_,lo,_⟩ := pair_data inside
  rintro ⟨r,eq⟩
  have rp : 1<r := by
    by_contra! small
    have sq := Nat.mul_le_mul small small
    have bound : 1 < (2:ℕ)^2047 := by decide +kernel
    omega
  obtain ⟨left,right⟩ := ordered_semiprime_pair_unique p q lt.le le_rfl rp eq.symm
  omega

/-- The first 2^40 midpoints, including the ceiling square root at index
zero. The coefficient ranges over all naturals through 2^64. -/
def shortSearch (N : ℕ) : Prop :=
  ∃ i h u : ℕ, i<2^40 ∧ h≤2^64 ∧ (ceilSqrt N+i)^2=N+h*u^2

private theorem excess_bound {N i d : ℕ} (pos : 0<N) (hi : N<2^2048)
    (index : i<2^40) (eq : (ceilSqrt N+i)^2=N+d) : d<2^1066 := by
  let r := ceilSqrt N
  have maxRoot : r≤2^1024 := ceilSqrt_le_iff.mpr
    (hi.le.trans_eq (by decide +kernel : 2^2048=(2^1024)^2))
  have rp : 0<r := by
    by_contra! h
    have : N≤0^2 := ceilSqrt_le_iff.mp h
    omega
  have prev : (r-1)^2<N := by
    apply lt_of_not_ge
    intro le
    have : r≤r-1 := ceilSqrt_le_iff.mpr le
    omega
  have back := Nat.sub_add_cancel (show 1≤r by omega)
  have sq := congrArg (fun a : ℕ => a^2) back
  have near : r^2 ≤ N+2*r := by nlinarith only [prev,sq,back]
  have cross := Nat.mul_le_mul maxRoot index.le
  have rest := Nat.pow_le_pow_left index.le 2
  have cap : 2*2^1024 + 2*(2^1024*2^40) + (2^40)^2 < (2:ℕ)^1066 := by decide +kernel
  change (r+i)^2=N+d at eq
  nlinarith only [near,cross,rest,cap,eq,maxRoot]

/-- A fixed coefficient and square-part menu also contains the offset zero. -/
private noncomputable def coefficientMenu (H U : ℕ) : Finset ℕ :=
  ((Icc 1 H) ×ˢ (range U)).image (fun z : ℕ×ℕ => z.1*z.2^2)

private noncomputable def excessMenu : Finset ℕ := coefficientMenu (2^64) (2^533)

attribute [local irreducible] coefficientMenu

private theorem excessMenu_size : excessMenu.card≤2^597 := by
  have cap : 2^64*2^533= (2:ℕ)^597 := by decide +kernel
  unfold excessMenu coefficientMenu
  apply card_image_le.trans
  rw [card_product,card_range,Nat.card_Icc]
  simpa only [Nat.add_sub_cancel] using cap.le

attribute [local irreducible] excessMenu

private theorem menu_mem {H U h u : ℕ} (hp : 0<h) (hc : h≤H) (ub : u<U) :
    h*u^2 ∈ coefficientMenu H U := by
  unfold coefficientMenu
  exact mem_image.mpr ⟨(h,u),mem_product.mpr ⟨mem_Icc.mpr ⟨hp,hc⟩,mem_range.mpr ub⟩,rfl⟩

private theorem short_subset : sample shortSearch ⊆
    sample (fun N => ∃ d∈excessMenu, IsSquare (N+d)) := by
  intro z hz
  have inside := hz
  simp only [sample,mem_filter,mem_ordered] at hz ⊢
  obtain ⟨⟨p,q,ne,size,hit⟩,lt⟩ := hz
  obtain ⟨i,h,u,ic,hc,eq⟩ := hit
  have sq : IsSquare (z.1*z.2+h*u^2) := ⟨ceilSqrt (z.1*z.2)+i,by rw [←eq,pow_two]⟩
  have positive : 0<h*u^2 := by
    by_contra! zero
    have zz : h*u^2=0 := by omega
    rw [zz,Nat.add_zero] at sq
    exact nonsquare inside sq
  have hp : 0<h := Nat.pos_of_mul_pos_right positive
  obtain ⟨_,_,_,_,lo,hi,_⟩ := pair_data inside
  have excess := excess_bound (by omega : 0<z.1*z.2) hi ic eq
  have ub : u<2^533 := by
    apply (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp
    have small : u^2≤h*u^2 := Nat.le_mul_of_pos_left _ hp
    exact (small.trans_lt excess).trans_eq (by decide +kernel)
  refine ⟨⟨p,q,ne,size,h*u^2,?_,sq⟩,lt⟩
  unfold excessMenu
  exact menu_mem (H:=2^64) (U:=2^533) (h:=h) (u:=u) hp hc ub

/-- Even free recognition of every allowed square multiple throughout the
first 2^40 midpoints succeeds on fewer than one in 2^403 eligible products. -/
theorem short_frequency : 2^403*(sample shortSearch).card < eligible.card := by
  have cnt := (card_le_card short_subset).trans ((menu_count excessMenu).trans
    (Nat.mul_le_mul_right _ excessMenu_size))
  have scaled := Nat.mul_le_mul_left (21000000*2^403) cnt
  have num : 21000000*2^403*(2^597*(75*2^1015))≤2^2046 := by decide +kernel
  apply Nat.lt_of_mul_lt_mul_left (a:=21000000)
  simpa only [Nat.mul_assoc] using (scaled.trans num).trans_lt ChebyshevPrimeSample.eligible_count

end PrimeFactors.SmallNormSquarePopulation
