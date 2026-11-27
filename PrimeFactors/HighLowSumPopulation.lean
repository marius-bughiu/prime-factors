import PrimeFactors.ActualWindowAdvice
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! # Factor-sum lists chosen from the high and low bits of a product

For a semiprime with two distinct 1,024-bit factors, count the pairs covered by a
list of proposed sums. The list may depend on the high 1,024 product bits, the low
512 bits, and (in the final theorem) the five fields defining the public interval.
The integer inequalities use the unconditional prime count in ChebyshevPrimeSample.
-/

namespace PrimeFactors.HighLowSumPopulation
open Finset MixedPrefixSample

set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

private theorem other_factor {x y : ℤ} {k v : ℕ} (low : ¬(2:ℤ)^(v+1) ∣ x)
    (prod : (2:ℤ)^k ∣ x*y) : (2:ℤ)^(k-v) ∣ y := by
  by_cases hx : x=0
  · exact False.elim (low (hx ▸ dvd_zero _))
  by_cases hy : y=0
  · simp [hy]
  change ¬((2:ℕ):ℤ)^(v+1) ∣ x at low
  change ((2:ℕ):ℤ)^k ∣ x*y at prod
  change ((2:ℕ):ℤ)^(k-v) ∣ y
  rw [padicValInt_dvd_iff] at low prod ⊢
  rw [padicValInt.mul hx hy] at prod
  have hxy := mul_ne_zero hx hy
  omega

/-- The proposed factor a agrees with p or q modulo the indicated power of two.
Truncated subtraction includes the case v ≥ k. -/
theorem two_roots {p q a b g : ℤ} {k v : ℕ}
    (gap : q-p=(2:ℤ)^v*g) (odd : Odd g) (sum : p+q=a+b)
    (prod : p*q ≡ a*b [ZMOD (2:ℤ)^k]) :
    a ≡ p [ZMOD (2:ℤ)^(k-v)] ∨ a ≡ q [ZMOD (2:ℤ)^(k-v)] := by
  have exact_gap : ¬(2:ℤ)^(v+1) ∣ q-p := by
    rintro ⟨j,h⟩
    rw [gap,pow_succ,mul_assoc] at h
    have nz : (2:ℤ)^v≠0 := by positivity
    have eq := mul_left_cancel₀ nz h
    obtain ⟨i,hi⟩ := odd
    omega
  have factors : (2:ℤ)^k ∣ (a-p)*(q-a) := by
    rw [show (a-p)*(q-a)=a*b-p*q by nlinarith only [congrArg (a*·) sum]]
    exact Int.modEq_iff_dvd.mp prod
  by_cases left : (2:ℤ)^(v+1) ∣ a-p
  · have right : ¬(2:ℤ)^(v+1) ∣ q-a := by
      intro d
      exact exact_gap (show (2:ℤ)^(v+1) ∣ q-p by convert dvd_add left d using 1; ring)
    have swapped : (2:ℤ)^k ∣ (q-a)*(a-p) := by rwa [mul_comm (q-a)]
    exact Or.inl (Int.modEq_iff_dvd.mpr (other_factor right swapped)).symm
  · exact Or.inr (Int.modEq_iff_dvd.mpr (other_factor left factors))

/-- With enough precision the two classes exactly characterize the product test. -/
theorem roots_iff {p q a b g : ℤ} {k v : ℕ} (enough : 2*v≤k)
    (gap : q-p=(2:ℤ)^v*g) (odd : Odd g) (sum : p+q=a+b) :
    p*q ≡ a*b [ZMOD (2:ℤ)^k] ↔
    a ≡ p [ZMOD (2:ℤ)^(k-v)] ∨ a ≡ q [ZMOD (2:ℤ)^(k-v)] := by
  refine ⟨two_roots gap odd sum,?_⟩
  have divides : (2:ℤ)^v ∣ q-p := ⟨g,gap⟩
  have nested : (2:ℤ)^v ∣ 2^(k-v) := pow_dvd_pow _ (by omega)
  have whole : (2:ℤ)^k=(2:ℤ)^(k-v)*2^v := by rw [←pow_add]; congr 1; omega
  intro roots
  apply Int.modEq_iff_dvd.mpr
  rw [show a*b-p*q=(a-p)*(q-a) by nlinarith only [congrArg (a*·) sum],whole]
  rcases roots with left|right
  · have near := Int.modEq_iff_dvd.mp left.symm
    have far : (2:ℤ)^v ∣ q-a := by
      convert dvd_sub divides (nested.trans near) using 1; ring
    exact mul_dvd_mul near far
  · have near := Int.modEq_iff_dvd.mp right
    have far : (2:ℤ)^v ∣ a-p := by
      convert dvd_sub divides (nested.trans near) using 1; ring
    rw [mul_comm (a-p)]
    exact mul_dvd_mul near far

/-- Distinct equal-width prime pairs, identical sum and product suffix. Recovering
a root modulo 32 would be too strong, but the promised precision of 16 works. -/
theorem sharp_example :
    Nat.Prime 73 ∧ Nat.Prime 83 ∧ Nat.Prime 67 ∧ Nat.Prime 89 ∧
    73+83=67+89 ∧ (83:ℤ)-73=2*5 ∧ Odd (5:ℤ) ∧
    (73:ℤ)*83 ≡ 67*89 [ZMOD 32] ∧ (67:ℤ) ≡ 83 [ZMOD 16] ∧
    ¬((67:ℤ) ≡ 73 [ZMOD 32] ∨ (67:ℤ) ≡ 83 [ZMOD 32]) := by
  decide +kernel

private theorem root_classes {p q a b g k v : ℕ} (order : p≤q)
    (gap : q-p=2^v*g) (odd : Odd g) (sum : p+q=a+b)
    (prod : p*q%2^k=a*b%2^k) :
    a%2^(k-v)=p%2^(k-v) ∨ a%2^(k-v)=q%2^(k-v) := by
  have gapZ : (q:ℤ)-p=2^v*(g:ℤ) := by
    rw [←Int.natCast_sub order]
    exact_mod_cast gap
  have pro := Int.natCast_modEq_iff.mpr (show p*q ≡ a*b [MOD 2^k] from prod)
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at pro
  have result := two_roots gapZ (by exact_mod_cast odd)
    (show (p:ℤ)+q=a+b by exact_mod_cast sum) pro
  have unwrap {x y : ℕ} (h : (x:ℤ) ≡ y [ZMOD (2:ℤ)^(k-v)]) :
      x%2^(k-v)=y%2^(k-v) :=
    Int.natCast_modEq_iff.mp (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using h)
  exact result.imp unwrap unwrap

private theorem close_count {B D G : ℕ} (S : Finset (ℕ×ℕ))
    (data : ∀ z∈S, z.1<B ∧ z.1≤z.2 ∧ G∣z.2-z.1 ∧ (z.2-z.1)/G<D) : S.card≤B*D := by
  let key (z : ℕ×ℕ) := (z.1,(z.2-z.1)/G)
  calc S.card ≤ ((range B) ×ˢ (range D)).card := by
         apply card_le_card_of_injOn key
         · intro z hz
           obtain ⟨a,_,_,g⟩ := data z hz
           exact mem_product.mpr ⟨mem_range.mpr a,mem_range.mpr g⟩
         · intro a ha b hb eq
           have e := congrArg Prod.fst eq
           have f := congrArg Prod.snd eq
           change a.1=b.1 at e
           change (a.2-a.1)/G=(b.2-b.1)/G at f
           obtain ⟨_,asc,ga,_⟩ := data a ha
           obtain ⟨_,bsc,gb,_⟩ := data b hb
           have val := congrArg (· * G) f
           simp only [Nat.div_mul_cancel ga, Nat.div_mul_cancel gb] at val
           exact Prod.ext e (by omega)
       _ = _ := by rw [card_product,card_range,card_range]

private theorem two_per_fiber {B D U : ℕ} (bp : 0<B) (lim : B≤U*D)
    (S : Finset (ℕ×ℕ)) (h s : ℕ)
    (data : ∀ z∈S, z.1*z.2/B=h ∧ z.1+z.2=s ∧ z.1+D≤z.2)
    (roots : ∀ a∈S,∀ z∈S, z.1%U=a.1%U ∨ z.1%U=a.2%U) : S.card≤2 := by
  by_cases emp : S.Nonempty
  · obtain ⟨a,ha⟩ := emp
    let f (z : ℕ×ℕ) := z.1%U
    calc S.card ≤ ({a.1%U,a.2%U}:Finset ℕ).card := by
           apply card_le_card_of_injOn f
           · intro z hz
             simpa only [f,mem_insert,mem_singleton] using roots a ha z hz
           · intro x hx y hy eq
             obtain ⟨wx,sx,gx⟩ := data x hx
             obtain ⟨wy,sy,gy⟩ := data y hy
             exact ActualWindowAdvice.far_unique bp lim gx gy (wx.trans wy.symm) (sx.trans sy.symm) eq
         _ ≤ 2 := card_le_two
  · rw [not_nonempty_iff_eq_empty.mp emp,card_empty]; decide

private theorem per_layer {B R J G U D : ℕ} (bp : 0<B) (rp : 0<R) (lim : B≤U*(G*D))
    (S : Finset (ℕ×ℕ)) (menu : ℕ×ℕ → Finset ℕ) (cap : ∀ x, (menu x).card≤J)
    (data : ∀ z∈S, z.1<B ∧ z.1≤z.2 ∧ G∣z.2-z.1 ∧ z.1*z.2/B<B ∧
      z.1+z.2∈menu (z.1*z.2/B,z.1*z.2%R))
    (roots : ∀ a∈S,∀ z∈S, a.1+a.2=z.1+z.2 → a.1*a.2%R=z.1*z.2%R →
      z.1%U=a.1%U ∨ z.1%U=a.2%U) :
    S.card≤B*D+2*(B*R*J) := by
  let close := fun z : ℕ×ℕ => (z.2-z.1)/G<D
  have near := close_count (S.filter close) (B:=B) (D:=D) (by
    intro z hz
    obtain ⟨inside,gap⟩ := mem_filter.mp hz
    obtain ⟨p,o,m,_⟩ := data z inside
    exact ⟨p,o,m,gap⟩)
  let rest := S.filter fun z => ¬close z
  let key (z : ℕ×ℕ) : Σ _ : ℕ×ℕ, ℕ := ⟨(z.1*z.2/B,z.1*z.2%R),z.1+z.2⟩
  let box := ((range B) ×ˢ (range R)).sigma menu
  have into : Set.MapsTo key rest box := by
    intro z hz
    have inside := (mem_filter.mp hz).1
    obtain ⟨_,_,_,lo,found⟩ := data z inside
    exact mem_sigma.mpr ⟨mem_product.mpr ⟨mem_range.mpr lo,mem_range.mpr (Nat.mod_lt _ rp)⟩,found⟩
  have capBox : box.card≤B*R*J := by
    calc box.card = _ := card_sigma ..
         _ ≤ ∑ _x∈(range B) ×ˢ (range R), J := sum_le_sum (fun h _ => cap h)
         _ = _ := by simp
  have fiber (w : Σ _ : ℕ×ℕ, ℕ) : (rest.filter (fun z => key z=w)).card≤2 := by
    let T := rest.filter (fun z => key z=w)
    have info (z) (hz : z∈T) : z∈S ∧ z.1*z.2/B=w.1.1 ∧ z.1*z.2%R=w.1.2 ∧
        z.1+z.2=w.2 ∧ z.1+(G*D)≤z.2 := by
      obtain ⟨far,eq⟩ := mem_filter.mp hz
      obtain ⟨base,gap⟩ := mem_filter.mp far
      obtain ⟨_,order,div,_,_⟩ := data z base
      have bigger := Nat.mul_le_mul_left G (Nat.le_of_not_gt gap)
      rw [Nat.mul_div_cancel' div] at bigger
      exact ⟨base,congrArg (fun v : Σ _ : ℕ×ℕ, ℕ => v.1.1) eq,
        congrArg (fun v : Σ _ : ℕ×ℕ, ℕ => v.1.2) eq,
        congrArg (fun v : Σ _ : ℕ×ℕ, ℕ => v.2) eq,by omega⟩
    apply two_per_fiber bp lim T w.1.1 w.2
    · intro z hz
      obtain ⟨_,word,_,s,g⟩ := info z hz
      exact ⟨word,s,g⟩
    · intro a ha z hz
      obtain ⟨ai,_,ar,asum,_⟩ := info a ha
      obtain ⟨zi,_,zr,zsum,_⟩ := info z hz
      exact roots a ai z zi (asum.trans zsum.symm) (ar.trans zr.symm)
  have far := (card_le_mul_card_image_of_maps_to into 2 (fun z _ => fiber z)).trans
    (Nat.mul_le_mul_left 2 capBox)
  have sum := Nat.add_le_add near far
  rw [←filter_card_add_filter_neg_card_eq_card (s:=S) close]
  exact sum

/-- One finite menu per high product word and low product suffix. No primality
assumption is needed in the layer count. Strict ordering excludes the zero gap. -/
theorem layers {B b k D J : ℕ} (bp : 0<B) (lim : B≤2^k*D)
    (S : Finset (ℕ×ℕ)) (menu : ℕ×ℕ → Finset ℕ) (cap : ∀ w, (menu w).card≤J)
    (data : ∀ z∈S, z.1<B ∧ z.1<z.2 ∧ z.2-z.1<2^b ∧ z.1*z.2/B<B ∧
      z.1+z.2∈menu (z.1*z.2/B,z.1*z.2%2^k)) :
    S.card≤b*(B*D+2*(B*2^k*J)) := by
  classical
  let T (v : ℕ) := S.filter fun z => ∃ j : ℕ, Odd j ∧ z.2-z.1=2^v*j
  have cover : S ⊆ (range b).biUnion T := by
    intro z hz
    obtain ⟨_,ord,gap,_,_⟩ := data z hz
    obtain ⟨v,j,odd,eq⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : z.2-z.1≠0)
    have low := Nat.le_of_dvd (by omega : 0<z.2-z.1) (show 2^v∣z.2-z.1 from ⟨j,eq⟩)
    have inside := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp (low.trans_lt gap)
    exact mem_biUnion.mpr ⟨v,mem_range.mpr inside,mem_filter.mpr ⟨hz,j,odd,eq⟩⟩
  apply (card_le_card cover).trans
  apply (card_biUnion_le_card_mul (range b) T (B*D+2*(B*2^k*J)) ?_).trans
  · simp
  intro v _
  have height : 2^k≤2^(k-v)*2^v := by
    rw [←pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  apply per_layer (R:=2^k) (U:=2^(k-v)) (G:=2^v) bp (by positivity)
    (by simpa only [Nat.mul_assoc] using lim.trans (Nat.mul_le_mul_right D height))
    (T v) menu cap
  · intro z hz
    obtain ⟨hz,j,_,eq⟩ := mem_filter.mp hz
    obtain ⟨base,ord,_,word,hit⟩ := data z hz
    exact ⟨base,ord.le,⟨j,eq⟩,word,hit⟩
  · intro a ha z _ sum prod
    obtain ⟨inside,j,odd,eq⟩ := mem_filter.mp ha
    exact root_classes (data _ inside).2.1.le eq odd sum prod

attribute [local irreducible] ordered sample primes eligible

private theorem eligible_shape {z : ℕ×ℕ} (inside : z∈eligible) :
    z.1<2^1024 ∧ z.2<2^1024 ∧ z.1<z.2 ∧ 2*X^2≤z.1*z.2 ∧ z.1*z.2<(2^1024)^2 := by
  rw [eligible,sample,mem_filter] at inside
  obtain ⟨p,q,_,lo,_⟩ := (mem_ordered (z:=z) (E:=fun _ => True)).mp inside.1
  simp only [primes,mem_filter,mem_Ico] at p q
  have pl : z.1<2^1024 := p.1.2
  have ql : z.2<2^1024 := q.1.2
  have hi := Nat.mul_lt_mul_of_lt_of_le pl ql.le (by decide +kernel : 0<2^1024)
  exact ⟨pl,ql,inside.2,lo,by simpa only [pow_two] using hi⟩

/-- A menu accessing only the high product word and k low bits. -/
noncomputable def wordHits (k : ℕ) (menu : ℕ×ℕ → Finset ℕ) : Finset (ℕ×ℕ) :=
  eligible.filter fun z => z.1+z.2∈menu (z.1*z.2/2^1024,z.1*z.2%2^k)

/-- Count qualifying pairs covered by any bounded high-word and low-suffix list. -/
theorem word_count {k D J : ℕ} (menu : ℕ×ℕ → Finset ℕ) (cap : ∀ w, (menu w).card≤J)
    (lim : 2^1024≤2^k*D) :
    (wordHits k menu).card≤1024*(2^1024*D+2*(2^1024*2^k*J)) := by
  apply layers (by decide +kernel) lim _ menu cap
  intro z hz
  obtain ⟨inside,hit⟩ := mem_filter.mp (show z∈eligible.filter _ from hz)
  obtain ⟨pl,ql,ord,_,hi⟩ := eligible_shape inside
  exact ⟨pl,ord,by omega,(Nat.div_lt_iff_lt_mul (by decide +kernel)).mpr (by simpa only [pow_two] using hi),hit⟩

private theorem priced {J e : ℕ} (menu : ℕ×ℕ → Finset ℕ) (cap : ∀ w, (menu w).card≤J)
    (cost : 21000000*2^e*(1024*(2^1024*2^512+2*(2^1024*2^512*J)))≤2^2046) :
    2^e*(wordHits 512 menu).card<eligible.card := by
  have bound := word_count (k:=512) (D:=2^512) menu cap (by decide +kernel)
  have req := (Nat.mul_le_mul_left (21000000*2^e) bound).trans cost
  apply Nat.lt_of_mul_lt_mul_left (a:=21000000)
  simpa only [Nat.mul_assoc] using req.trans_lt ChebyshevPrimeSample.eligible_count

/-- The frequency of a correct sum among all eligible pairs is below 2^{-434}. -/
theorem full_size (menu : ℕ×ℕ → Finset ℕ) (cap : ∀ w, (menu w).card≤2^40) :
    2^434*(wordHits 512 menu).card<eligible.card := priced menu cap (by decide +kernel)

/-- The selector reads the actual interval data and the product suffix. -/
noncomputable def intervalHits (k : ℕ) (menu : ActualWindowAdvice.View → ℕ → Finset ℕ) :
    Finset (ℕ×ℕ) :=
  eligible.filter fun z => z.1+z.2∈menu (ActualWindowAdvice.view X (z.1*z.2)) (z.1*z.2%2^k)

/-- Among sorted, distinct prime pairs of the target widths, the five interval
fields and the low 512 product bits allow fewer than one success in 2^426
for any rule proposing at most 2^40 exact sums per reading. -/
theorem full_size_with_view (menu : ActualWindowAdvice.View → ℕ → Finset ℕ)
    (cap : ∀ v r, (menu v r).card≤2^40) :
    2^426*(intervalHits 512 menu).card<eligible.card := by
  classical
  let views (h : ℕ) := (ActualWindowAdvice.view_cover X h).choose
  let pooled (w : ℕ×ℕ) := (views w.1).biUnion fun v => menu v w.2
  have bound (w : ℕ×ℕ) : (pooled w).card≤288*2^40 := by
    exact (card_biUnion_le_card_mul (views w.1) (fun v => menu v w.2) (2^40)
      (fun v _ => cap v w.2)).trans
      (Nat.mul_le_mul_right _ (ActualWindowAdvice.view_cover X w.1).choose_spec.1)
  apply lt_of_le_of_lt _ (priced (e:=426) pooled bound (by decide +kernel))
  apply Nat.mul_le_mul_left
  apply card_le_card
  intro z hz
  obtain ⟨inside,found⟩ := mem_filter.mp (show z∈eligible.filter _ from hz)
  obtain ⟨_,_,_,lo,hi⟩ := eligible_shape inside
  apply mem_filter.mpr
  refine ⟨inside,mem_biUnion.mpr ⟨ActualWindowAdvice.view X (z.1*z.2),?_,found⟩⟩
  exact (ActualWindowAdvice.view_cover X (z.1*z.2/2^1024)).choose_spec.2 _ (by decide +kernel) lo hi rfl

/-- Two products of 10-bit primes have all five interval fields and their five
low bits in common. Their correct sums are different. -/
theorem small_window_collision :
    Nat.Prime 563 ∧ Nat.Prime 971 ∧ Nat.Prime 619 ∧ Nat.Prime 883 ∧
    563*971=546673 ∧ 619*883=546577 ∧ 563+971=1534 ∧ 619+883=1502 ∧
    ActualWindowAdvice.view 512 546673=ActualWindowAdvice.view 512 546577 ∧
    546673%32=17 ∧ 546577%32=17 := by
  have root {n : ℕ} (above : 739^2<n) (below : n≤740^2) : ceilSqrt n=740 := by
    have hi := ceilSqrt_le_iff.mpr below
    have lo : ¬ceilSqrt n≤739 := fun h => Nat.not_le_of_gt above (ceilSqrt_le_iff.mp h)
    omega
  have same : ActualWindowAdvice.view 512 546673=ActualWindowAdvice.view 512 546577 := by
    unfold ActualWindowAdvice.view
    rw [root (n:=546673) (by decide) (by decide),root (n:=546577) (by decide) (by decide)]
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    by decide,by decide,by decide,by decide,same,by decide,by decide⟩

end PrimeFactors.HighLowSumPopulation
