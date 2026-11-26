import PrimeFactors.ChebyshevPrimeSample
import PrimeFactors.FactorSum
import PrimeFactors.SmoothSampleBound
import Mathlib.Tactic

/-! Count the products admitting even a single smooth rational row at a shifted
integer cube root. The denominator counts each eligible prime pair once. -/

namespace PrimeFactors.CubicSmoothRows
open Finset
open scoped BigOperators
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

/-- Public search event. `cut` is a strict smoothness cutoff. Either sign of
the row is permitted. Constant rows are excluded by `0 < b`. -/
def Hit (K A B cut n : ℕ) : Prop :=
  ∃ r : ℕ, r^3 ≤ n ∧ n < (r+1)^3 ∧ ∃ k a : ℤ, |k| ≤ (K:ℤ) ∧ |a| ≤ (A:ℤ) ∧
    ∃ b : ℕ, 0 < b ∧ b ≤ B ∧ (a + (b:ℤ)*((r:ℤ)+k)).natAbs ∈ Nat.smoothNumbers cut

def width (R : ℕ) := 3*R^2+3*R+1

/-- Fix the combined intercept `h=a+b*k`, slope, and positive smooth value.
They determine the floor cube root. Only the integers in one cube cell remain. -/
theorem fiber (P : Finset ℕ) (h : ℤ) {b : ℕ} (bp : 0 < b) (v R : ℕ)
    (hits : ∀ n ∈ P, ∃ r ≤ R, r^3≤n ∧ n<(r+1)^3 ∧ (v:ℤ)=h+(b:ℤ)*r) :
    P.card ≤ width R := by
  classical
  rcases P.eq_empty_or_nonempty with empty | ⟨n₀, member⟩
  · simp [empty]
  obtain ⟨r, bound, _, _, row⟩ := hits n₀ member
  have cover : P ⊆ Ico (r^3) ((r+1)^3) := by
    intro n hn
    obtain ⟨r', _, l, u, row'⟩ := hits n hn
    have nonzero : (b:ℤ) ≠ 0 := by exact_mod_cast bp.ne'
    have same : r = r' := by
      exact_mod_cast mul_left_cancel₀ nonzero (add_left_cancel (row.symm.trans row'))
    exact mem_Ico.mpr (same ▸ ⟨l, u⟩)
  have expand : (r+1)^3 = r^3+width r := by unfold width; ring
  calc
    P.card ≤ (Ico (r^3) ((r+1)^3)).card := card_le_card cover
    _ = width r := by rw [Nat.card_Ico, expand]; omega
    _ ≤ width R := by unfold width; gcongr

/-- Arbitrary finite coefficient and value menus, including product-dependent
choices from either menu. Each admitted positive row fixes one cube cell. -/
theorem menu_count (P : Finset ℕ) (labels : Finset (ℤ × ℕ)) (values : Finset ℕ)
    (R : ℕ) (positive : ∀ l ∈ labels, 0 < l.2)
    (hits : ∀ n ∈ P, ∃ l ∈ labels, ∃ v ∈ values, ∃ r ≤ R,
      r^3≤n ∧ n<(r+1)^3 ∧ (v:ℤ)=l.1+(l.2:ℤ)*r) :
    P.card ≤ labels.card * (values.card * width R) := by
  classical
  let cell (l : ℤ×ℕ) (v : ℕ) := P.filter (fun n => ∃ r ≤ R,
      r^3≤n ∧ n<(r+1)^3 ∧ (v:ℤ)=l.1+(l.2:ℤ)*r)
  have cover : P ⊆ labels.biUnion (fun l => values.biUnion (cell l)) := by
    intro n hn
    obtain ⟨l,hl,v,hv,hr⟩ := hits n hn
    exact mem_biUnion.mpr ⟨l,hl,mem_biUnion.mpr ⟨v,hv,mem_filter.mpr ⟨hn,hr⟩⟩⟩
  refine (card_le_card cover).trans (card_biUnion_le_card_mul _ _ _ fun l hl => ?_)
  exact card_biUnion_le_card_mul _ _ _ fun v _ =>
    fiber (cell l v) l.1 (positive l hl) v R (fun n hn => (mem_filter.mp hn).2)

/-- Eight times a rational majorant for the local Euler factor at exponent
1/16. Each entry is checked by integer sixteenth powers. -/
def numerator (p : ℕ) : ℕ :=
  if p≤2 then 189 else if p≤3 then 121 else if p≤5 then 84 else if p≤7 then 70
  else if p≤11 then 58 else if p≤13 then 55 else if p≤17 then 50 else if p≤19 then 48
  else if p≤23 then 45 else if p≤29 then 43 else if p≤31 then 42 else if p≤37 then 40
  else if p≤43 then 39 else if p≤47 then 38 else if p≤53 then 37 else if p≤61 then 36
  else if p≤73 then 35 else if p≤83 then 34 else if p≤97 then 33 else if p≤113 then 32 else 31

private theorem euler_local {p u : ℕ} (large : 8 < u) (order : u^16 ≤ p*(u-8)^16) :
    (1 - (p:ℝ)^(-(16:ℝ)⁻¹))⁻¹ ≤ (u:ℝ)/8 := by
  have ul : (8:ℝ) < u := by exact_mod_cast large
  have den : (0:ℝ) < u-8 := by linarith
  have test : (u:ℝ)^16 ≤ p*((u:ℝ)-8)^16 := by
    have h : (u:ℝ)^16 ≤ p*((u-8:ℕ):ℝ)^16 := by exact_mod_cast order
    simpa only [Nat.cast_sub large.le, Nat.cast_ofNat] using h
  let x : ℝ := (p:ℝ)^((16:ℝ)⁻¹)
  have power : x^16=(p:ℝ) := Real.rpow_inv_natCast_pow (by positivity) (by decide : 16≠0)
  have pos : 0≤x := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have bound : (u:ℝ) ≤ x*(u-8) := by
    apply le_of_pow_le_pow_left₀ (by decide : 16≠0) (mul_nonneg pos den.le)
    rwa [mul_pow,power]
  have xp : 1 < x := by
    apply lt_of_not_ge
    intro bad
    linarith only [bound, mul_le_mul_of_nonneg_right bad den.le]
  rw [Real.rpow_neg (Nat.cast_nonneg p)]
  change (1-x⁻¹)⁻¹ ≤ _
  have x0 : 0<x := by linarith
  have gap : 0 < 1-x⁻¹ := by
    rw [inv_eq_one_div, sub_pos, div_lt_one x0]
    exact xp
  rw [inv_eq_one_div, div_le_iff₀ gap, inv_eq_one_div]
  rw [show (u:ℝ)/8*(1-1/x)=u*(x-1)/(8*x) by field_simp]
  rw [le_div_iff₀ (by positivity)]
  nlinarith only [bound]

/-- Finite Euler-product estimate for all positive 127-smooth integers up to
2^(16j). It does not enumerate any of these integers. -/
theorem smooth_weighted (j : ℕ) : 8^31 * (Nat.smoothNumbersUpTo (2^(j*16)) 128).card ≤
    2^j * (∏ p ∈ (128:ℕ).primesBelow, numerator p) := by
  let primes := (128:ℕ).primesBelow
  have localTable : ∀ p ∈ primes, 8 < numerator p ∧
      numerator p ^ 16 ≤ p*(numerator p-8)^16 := by decide +kernel
  have count : primes.card=31 := by decide +kernel
  have le := SmoothSampleBound.rankinBound (2^(j*16)) 127 ((16:ℝ)⁻¹) (by positivity)
  have euler : (∏ p ∈ primes, (1-(p:ℝ)^(-(16:ℝ)⁻¹))⁻¹) ≤
        ∏ p ∈ primes, ((numerator p:ℝ)/8) := by
    apply prod_le_prod
    · intro p hp
      have pp : (1:ℝ)<p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt
      have less := Real.rpow_lt_one_of_one_lt_of_neg pp (by norm_num : -(16:ℝ)⁻¹ < 0)
      exact inv_nonneg.mpr (sub_nonneg.mpr less.le)
    · exact fun p hp => euler_local (localTable p hp).1 (localTable p hp).2
  have powPart : (((2^(j*16):ℕ):ℝ)^((16:ℝ)⁻¹))=(2:ℝ)^j := by
    rw [Nat.cast_pow, Nat.cast_ofNat, pow_mul]
    exact Real.pow_rpow_inv_natCast (by positivity) (by decide : 16≠0)
  rw [powPart] at le
  have final := le.trans (mul_le_mul_of_nonneg_left euler (by positivity : (0:ℝ)≤2^j))
  rw [prod_div_distrib,prod_const,count] at final
  rw [← mul_div_assoc,le_div_iff₀ (by positivity)] at final
  exact_mod_cast (by simpa only [mul_comm (8^31:ℝ)] using final :
    (8:ℝ)^31 * (Nat.smoothNumbersUpTo (2^(j*16)) 128).card ≤
      2^j * ∏ p ∈ primes, (numerator p:ℝ))

attribute [local irreducible] Nat.smoothNumbersUpTo

theorem smooth_count : 8^31 * (Nat.smoothNumbersUpTo (2^688) 128).card ≤
    2^43 * (∏ p ∈ (128:ℕ).primesBelow, numerator p) := by
  have h := smooth_weighted 43
  rw [show 43*16=688 by decide] at h
  exact h

/-- The explicit integer floor of the finite Euler-product upper bound. -/
theorem smooth_size : (Nat.smoothNumbersUpTo (2^688) 128).card ≤
    462527822261304141796036693645202636 := by
  by_contra! large
  have small : 2^43 * (∏ p ∈ (128:ℕ).primesBelow, numerator p) <
      8^31 * (462527822261304141796036693645202636+1) := by decide +kernel
  exact (not_lt_of_ge (Nat.mul_le_mul_left _ large)) (smooth_count.trans_lt small)

/-- Raising the smoothness height by sixteen bits costs a factor of two
in this upper bound. The integer majorant is rounded up only once. -/
theorem smooth_size_scaled (extra : ℕ) :
    (Nat.smoothNumbersUpTo (2^(688+16*extra)) 128).card ≤
      2^extra*462527822261304141796036693645202637 := by
  have weight := smooth_weighted (43+extra)
  rw [show (43+extra)*16=688+16*extra by omega, pow_add 2 43 extra] at weight
  have fixed : 2^43*(∏ p ∈ (128:ℕ).primesBelow, numerator p) ≤
      8^31*462527822261304141796036693645202637 := by decide +kernel
  apply Nat.le_of_mul_le_mul_left (c:=8^31) _ (by decide)
  calc
    _ ≤ _ := weight
    _ = 2^extra*(2^43*(∏ p ∈ (128:ℕ).primesBelow, numerator p)) := by ring
    _ ≤ 2^extra*(8^31*462527822261304141796036693645202637) := Nat.mul_le_mul_left _ fixed
    _ = 8^31*(2^extra*462527822261304141796036693645202637) := by ring

/-- Public upper bound on the integer cube root, with enough slack to bound the
whole row by 2^688. Both endpoint comparisons are integer calculations. -/
def rootCap : ℕ := 51*2^677

private def labels : Finset (ℤ×ℕ) := Icc (-288:ℤ) 288 ×ˢ Icc (1:ℕ) 32

private theorem mem_labels (l : ℤ×ℕ) : l ∈ labels ↔
    (-288≤l.1 ∧ l.1≤288) ∧ (1≤l.2 ∧ l.2≤32) := by
  simp only [labels,mem_product,mem_Icc]

attribute [local irreducible] labels

private theorem labels_card : labels.card = 18464 := by
  rw [labels, card_product, Int.card_Icc, Nat.card_Icc]
  decide

/-- Decode a successful signed row into one fixed coefficient pair and one
smooth value. In this size range the row is strictly positive. -/
private theorem decode {n : ℕ} (lower : 2^2047≤n) (upper : n<2^2048)
    (hit : Hit 4 160 32 128 n) :
    ∃ l ∈ labels, ∃ v ∈ Nat.smoothNumbersUpTo (2^688) 128, ∃ r ≤ rootCap,
      r^3≤n ∧ n<(r+1)^3 ∧ (v:ℤ)=l.1+(l.2:ℤ)*r := by
  obtain ⟨r,lo,hi,k,a,hk,ha,b,bp,bs,smooth⟩ := hit
  have rb : r ≤ rootCap := by
    by_contra! large
    have endpt : 2^2048 ≤ rootCap^3 := by decide +kernel
    exact (not_lt_of_ge (endpt.trans ((Nat.pow_le_pow_left large.le 3).trans lo))) upper
  have rp : 288 < r := by
    by_contra! small
    have fromBelow := lower.trans_lt (hi.trans_le (Nat.pow_le_pow_left (Nat.succ_le_succ small) 3))
    exact (by decide +kernel : ¬(2^2047:ℕ)<289^3) fromBelow
  let h : ℤ := a+(b:ℤ)*k
  have hb : 0≤(b:ℤ) := by positivity
  have hs : (b:ℤ)≤32 := by exact_mod_cast bs
  have hspan : |h| ≤ 288 := calc
    |h| ≤ |a|+|(b:ℤ)*k| := abs_add_le ..
    _ = |a| + (b:ℤ)*|k| := by rw [abs_mul,abs_of_nonneg hb]
    _ ≤ 160+32*4 := add_le_add ha (mul_le_mul hs hk (abs_nonneg _) (by decide))
    _ = 288 := by norm_num
  have bound := abs_le.mp hspan
  have br : (r:ℤ) ≤ (b:ℤ)*r := by
    simpa using mul_le_mul_of_nonneg_right (show (1:ℤ)≤b by exact_mod_cast bp)
      (show 0≤(r:ℤ) by positivity)
  have pos : 0 ≤ h+b*(r:ℤ) := by
    have hbig : (288:ℤ)<r := by exact_mod_cast rp
    linarith only [bound.1,br,hbig]
  have val : ((a+(b:ℤ)*((r:ℤ)+k)).natAbs:ℤ)=h+b*(r:ℤ) := by
    rw [Int.natCast_natAbs, show a+(b:ℤ)*((r:ℤ)+k)=h+b*(r:ℤ) by dsimp [h]; ring,
      abs_of_nonneg pos]
  have limit : (a+(b:ℤ)*((r:ℤ)+k)).natAbs≤2^688 := by
    have top : (288:ℤ)+32*(rootCap:ℤ) ≤ (2:ℤ)^688 := by
      exact_mod_cast (by decide +kernel : 288+32*rootCap≤2^688)
    have raw := (add_le_add bound.2 (mul_le_mul hs (show (r:ℤ)≤rootCap by exact_mod_cast rb)
      (by positivity) (by decide))).trans top
    exact_mod_cast (val.le.trans raw)
  exact ⟨(h,b),(mem_labels _).mpr ⟨bound,bp,bs⟩,_,
    Nat.mem_smoothNumbersUpTo.mpr ⟨limit,smooth⟩,r,rb,lo,hi,val⟩

attribute [local irreducible] MixedPrefixSample.ordered MixedPrefixSample.primes
  MixedPrefixSample.eligible MixedPrefixSample.sample

private abbrev product (z : ℕ×ℕ) := z.1*z.2

private theorem sample_facts {E : ℕ → Prop} {z : ℕ×ℕ}
    (hz : z ∈ MixedPrefixSample.sample E) : z.1.Prime ∧ z.2.Prime ∧ z.1<z.2 ∧
      2^2047≤product z ∧ product z<2^2048 ∧ E (product z) := by
  rw [MixedPrefixSample.sample,mem_filter] at hz
  obtain ⟨mem,ord⟩ := hz
  obtain ⟨hp,hq,_,lo,hit⟩ := MixedPrefixSample.mem_ordered.mp mem
  rw [MixedPrefixSample.primes, mem_filter, mem_Ico] at hp hq
  have up := Nat.mul_lt_mul_of_lt_of_le hp.1.2 hq.1.2.le (hq.2.pos.trans hq.1.2)
  have base : 2*MixedPrefixSample.X^2=2^2047 := by decide +kernel
  have ceiling : (2*MixedPrefixSample.X)*(2*MixedPrefixSample.X)=2^2048 := by decide +kernel
  rw [base] at lo
  rw [ceiling] at up
  exact ⟨hp.2,hq.2,ord,lo,up,hit⟩

private theorem same_product (S : Finset (ℕ×ℕ))
    (members : ∀ z ∈ S, z.1.Prime ∧ z.2.Prime ∧ z.1<z.2) :
    Set.InjOn product (S : Set (ℕ×ℕ)) := by
  intro x hx y hy eq
  obtain ⟨xp,_,xy⟩ := members x hx
  obtain ⟨yp,yq,yy⟩ := members y hy
  obtain ⟨hp,hq⟩ := ordered_semiprime_pair_unique yp yq yy.le xy.le xp.one_lt eq
  exact Prod.ext hp hq

private theorem product_card (E : ℕ → Prop) :
    ((MixedPrefixSample.sample E).image product).card=(MixedPrefixSample.sample E).card :=
  card_image_of_injOn (same_product _ (fun z hz => by
    obtain ⟨p,q,lt,_⟩ := sample_facts (E:=E) (z:=z) hz
    exact ⟨p,q,lt⟩))

/-- Uniform bound on eligible pairs of distinct 1,024-bit primes whose product
has 2,048 bits. The union includes all shifts and rows, even if chosen after
seeing the entire product. -/
theorem coverage :
    2^522 * (MixedPrefixSample.sample (Hit 4 160 32 128)).card <
      MixedPrefixSample.eligible.card := by
  classical
  let P := (MixedPrefixSample.sample (Hit 4 160 32 128)).image product
  have count := menu_count P labels (Nat.smoothNumbersUpTo (2^688) 128) rootCap
    (fun l hl => ((mem_labels l).mp hl).2.1) (by
      intro n hn
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hn
      obtain ⟨_,_,_,lo,hi,hit⟩ := sample_facts hz
      exact decode lo hi hit)
  have same : P.card=(MixedPrefixSample.sample (Hit 4 160 32 128)).card := product_card _
  rw [same,labels_card] at count
  apply Nat.lt_of_mul_lt_mul_left (a:=21000000)
  apply lt_of_le_of_lt _ ChebyshevPrimeSample.eligible_count
  refine (Nat.mul_le_mul_left 21000000 (Nat.mul_le_mul_left (2^522) (count.trans
    (Nat.mul_le_mul_left 18464 (Nat.mul_le_mul_right _ smooth_size))))).trans ?_
  decide +kernel

/-- For a primitive row, `r ∣ H+b³*n` singles out one residue modulo `r`.
In an octave beginning at `L`, the quotient of the offset by `r` therefore
identifies the input uniquely. The estimate uses a half-open interval. -/
theorem residue_fiber (P : Finset ℕ) {r b L T C : ℕ} (tp : 0<T) (lower : T≤r)
    (cop : r.Coprime b) (H : ℤ) (hits : ∀ n∈P, L≤n ∧ n<L+T*C ∧
      (r:ℤ) ∣ H+(b:ℤ)^3*n) : P.card ≤ C := by
  classical
  have into (n : ℕ) (hn : n∈P) : (n-L)/r ∈ range C := by
    apply mem_range.mpr
    rw [Nat.div_lt_iff_lt_mul (tp.trans_le lower)]
    obtain ⟨lo,h,_⟩ := hits n hn
    calc
      n-L < T*C := by omega
      _ ≤ C*r := by simpa only [mul_comm C] using Nat.mul_le_mul_right C lower
  have inj : Set.InjOn (fun n : ℕ => (n-L)/r) (P : Set ℕ) := by
    intro x hx y hy q
    change (x-L)/r=(y-L)/r at q
    obtain ⟨lx,_,dx⟩ := hits x hx
    obtain ⟨ly,_,dy⟩ := hits y hy
    have equiv : b^3*x ≡ b^3*y [MOD r] := by
      apply Nat.modEq_iff_dvd.mpr
      push_cast
      simpa only [add_sub_add_left_eq_sub] using dvd_sub dy dx
    have cancel : x ≡ y [MOD r] := Nat.ModEq.cancel_left_of_coprime (cop.pow_right 3) equiv
    have shifted : x-L ≡ y-L [MOD r] := by
      apply Nat.modEq_iff_dvd.mpr
      simpa only [Nat.cast_sub lx, Nat.cast_sub ly, sub_sub_sub_cancel_right] using cancel.dvd
    have reconstruction : x-L = y-L := calc
      _ = (x-L)%r + r*((x-L)/r) := (Nat.mod_add_div ..).symm
      _ = (y-L)%r + r*((y-L)/r) := by rw [show (x-L)%r=(y-L)%r from shifted,q]
      _ = _ := Nat.mod_add_div ..
    omega
  simpa only [card_range] using card_le_card_of_injOn _ into inj

/-- A finite set of permissible signed norms from positive magnitudes. -/
noncomputable def signedValues (V : Finset ℕ) : Finset ℤ :=
  V.image (fun v : ℕ => (v:ℤ)) ∪ V.image (fun v : ℕ => -(v:ℤ))

private theorem signed_mem {H : ℤ} {V : Finset ℕ} (h : H.natAbs ∈ V) :
    H ∈ signedValues V := by
  rw [signedValues, mem_union]
  by_cases pos : 0≤H
  · exact Or.inl (mem_image.mpr ⟨H.natAbs,h,by rw [Int.natCast_natAbs,abs_of_nonneg pos]⟩)
  · exact Or.inr (mem_image.mpr ⟨H.natAbs,h,by rw [Int.natCast_natAbs,abs_of_neg (lt_of_not_ge pos),neg_neg]⟩)

theorem signed_count (V : Finset ℕ) : (signedValues V).card ≤ 2*V.card := by
  apply (card_union_le ..).trans
  exact (Nat.add_le_add card_image_le card_image_le).trans_eq (two_mul V.card).symm

/-- Simultaneously count an arbitrary public menu of rational values, norm
magnitudes and slopes, without requiring the base or polynomial to be fixed
across inputs. Coprimality and the indicated congruence are the entire
algebraic hypothesis. -/
theorem residue_menu (P : Finset ℕ) (rows norms slopes : Finset ℕ) (L T C : ℕ)
    (tp : 0<T) (rangeN : ∀ n∈P, L≤n ∧ n<L+T*C)
    (hits : ∀ n∈P, ∃ r∈rows, ∃ b∈slopes, ∃ H : ℤ, H.natAbs∈norms ∧
      T≤r ∧ r.Coprime b ∧ (r:ℤ) ∣ H+(b:ℤ)^3*n) :
    P.card ≤ slopes.card*(rows.card*(2*norms.card))*C := by
  classical
  let menu := slopes ×ˢ (rows ×ˢ signedValues norms)
  let cell (w : ℕ×ℕ×ℤ) := P.filter (fun n : ℕ => T≤w.2.1 ∧ w.2.1.Coprime w.1 ∧
      (w.2.1:ℤ) ∣ w.2.2+(w.1:ℤ)^3*n)
  have cover : P ⊆ menu.biUnion cell := by
    intro n hn
    obtain ⟨r,hr,b,hb,H,hv,lo,cp,d⟩ := hits n hn
    exact mem_biUnion.mpr ⟨(b,r,H),mem_product.mpr ⟨hb,mem_product.mpr ⟨hr,signed_mem hv⟩⟩,
      mem_filter.mpr ⟨hn,lo,cp,d⟩⟩
  have per (w : ℕ×ℕ×ℤ) : (cell w).card ≤ C := by
    rcases (cell w).eq_empty_or_nonempty with empty | ⟨n,hn⟩
    · simp [empty]
    obtain ⟨_,lr,cp,_⟩ := mem_filter.mp hn
    apply residue_fiber (cell w) tp lr cp w.2.2
    intro x hx
    obtain ⟨mem,_,_,d⟩ := mem_filter.mp hx
    exact ⟨(rangeN x mem).1,(rangeN x mem).2,d⟩
  have total := (card_le_card cover).trans (card_biUnion_le_card_mul _ _ _ (fun w _ => per w))
  rw [show menu.card=slopes.card*(rows.card*(signedValues norms).card) by simp [menu]] at total
  exact total.trans (Nat.mul_le_mul_right C (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
    (signed_count norms))))

/-- Both magnitudes are positive and 127-smooth. The rational magnitude is
between 2^681 and 2^688, and the signed norm has magnitude at most
2^(688+16*extra). Slope and sign may depend on the input. -/
def Adaptive (B extra n : ℕ) : Prop :=
  ∃ r ∈ Nat.smoothNumbersUpTo (2^688) 128, ∃ b ∈ Icc 1 B, ∃ H : ℤ,
    H.natAbs ∈ Nat.smoothNumbersUpTo (2^(688+16*extra)) 128 ∧ 2^681≤r ∧
    r.Coprime b ∧ (r:ℤ) ∣ H+(b:ℤ)^3*n

/-- Even if 2^w slopes are available and the polynomial and base are selected
freely from the public product, the two smooth values must obey the congruence.
Every sixteen additional norm-height bits cost one population bit in this bound. -/
theorem adaptive_coverage {w extra saving : ℕ} (budget : saving+w+extra ≤ 417) :
    2^saving*(MixedPrefixSample.sample (Adaptive (2^w) extra)).card <
      MixedPrefixSample.eligible.card := by
  classical
  let S := MixedPrefixSample.sample (Adaptive (2^w) extra)
  let P := S.image product
  let V := Nat.smoothNumbersUpTo (2^688) 128
  let norms := Nat.smoothNumbersUpTo (2^(688+16*extra)) 128
  have endpt : 2^2047+2^681*2^1366=(2:ℕ)^2048 := by decide +kernel
  have all := residue_menu P V norms (Icc 1 (2^w)) (2^2047) (2^681) (2^1366)
    (by positivity) (fun n hn => by
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hn
      obtain ⟨_,_,_,lo,hi,_⟩ := sample_facts hz
      exact ⟨lo,endpt ▸ hi⟩) (fun n hn => by
        obtain ⟨z,hz,rfl⟩ := mem_image.mp hn
        exact (sample_facts hz).2.2.2.2.2)
  have same : P.card=S.card := product_card _
  rw [same,Nat.card_Icc,Nat.add_sub_cancel] at all
  let M := 462527822261304141796036693645202637
  have bound : S.card ≤ (2^w*2^extra) * (M*(2*M)*2^1366) := by
    refine all.trans ?_
    calc
      _ ≤ 2^w*(M*(2*(2^extra*M)))*2^1366 := by
        gcongr
        · exact smooth_size.trans (by decide)
        · exact smooth_size_scaled extra
      _ = _ := by ring
  have price : (2:ℕ)^saving*(2^w*2^extra) ≤ 2^417 := by
    rw [←mul_assoc,←pow_add,←pow_add]
    exact Nat.pow_le_pow_right (by decide) budget
  change 2^saving*S.card < _
  apply Nat.lt_of_mul_lt_mul_left (a:=21000000)
  apply lt_of_le_of_lt _ ChebyshevPrimeSample.eligible_count
  calc
    21000000*(2^saving*S.card) ≤ 21000000*(2^saving*((2^w*2^extra)*(M*(2*M)*2^1366))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ bound)
    _ = 21000000*((2^saving*(2^w*2^extra))*(M*(2*M)*2^1366)) := by ring
    _ ≤ 21000000*(2^417*(M*(2*M)*2^1366)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ price)
    _ ≤ 2^2046 := by decide +kernel

/-- Includes the 704-bit norm-height benchmark and all 32 positive slopes. -/
theorem adaptive_704 : 2^411*(MixedPrefixSample.sample (Adaptive 32 1)).card <
    MixedPrefixSample.eligible.card := by
  have h := adaptive_coverage (w:=5) (extra:=1) (saving:=411) (by decide)
  rw [show (2:ℕ)^5=32 by decide] at h
  exact h

/-- The same 32 slopes with norm height at most 2^2048. -/
theorem adaptive_2048 : 2^327*(MixedPrefixSample.sample (Adaptive 32 85)).card <
    MixedPrefixSample.eligible.card := by
  have h := adaptive_coverage (w:=5) (extra:=85) (saving:=327) (by decide)
  rw [show (2:ℕ)^5=32 by decide] at h
  exact h

end PrimeFactors.CubicSmoothRows
