import PrimeFactors.ReduceQuarticDenominator

/-! Disjoint factor-ratio intervals for the three primitive quartic
denominators, and necessary tests on the public product alone. -/
namespace PrimeFactors.QuarticDenominatorBands

open MixedPrefixSample (eligible)
open RecognizingQuarticProducts (factors)
open ComplementaryQuarticProducts (choices)
open private PrimeFactors.QuarticPrimePopulation.eligible_bounds from PrimeFactors.QuarticPrimePopulation
set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
attribute [local irreducible] eligible

def Band (p q t : ℕ) : Prop :=
  (t=1 ∧ 256*q≤257*p) ∨ (t=725 ∧ 9*p<5*q) ∨ (t=1517 ∧ 3*p<2*q ∧ 8*q<13*p)

def Gates (n t : ℕ) : Prop :=
  t=1 ∨ (t=725 ∧ 9*n<5*2^2048) ∨ (t=1517 ∧ 3*n<2*2^2048)

def PrimitiveHit (n t : ℕ) : Prop :=
  0<t ∧ t≤2048 ∧ ∃ a b : ℕ, 0<a ∧ 0<b ∧ a.Coprime b ∧
    t^4*n=a^4+4*b^4 ∧ (t^4*n<(a+1)^4 ∨ t^4*n<4*(b+1)^4)

theorem band_unique {p q t s : ℕ} (a : Band p q t) (b : Band p q s) : t=s := by
  unfold Band at a b
  omega

theorem close_factors {n a b d : ℕ} (large : 2^2047≤n) (small : n<2^2048)
    (dp : 0<d) (fit : d≤2048) (point : d^4*n=a^4+4*b^4)
    (gap : d^4*n<(a+1)^4 ∨ d^4*n<4*(b+1)^4) : 256*(factors a b).2≤257*(factors a b).1 := by
  have box := QuarticStripDenominators.coordinate_bounds large small dp fit point
  have sep : 513*(2*a*b)≤a^2+2*b^2 := by
    rcases gap with low|high
    · obtain ⟨big,tiny⟩ := box.1 low
      have h := Nat.mul_le_mul_right a (show 1026*b≤a by omega)
      nlinarith only [h,Nat.zero_le (b^2)]
    · obtain ⟨tiny,big⟩ := box.2 high
      have h := Nat.mul_le_mul_right b (show 513*a≤b by omega)
      nlinarith only [h,Nat.zero_le (a^2)]
  have diff := Nat.sub_add_cancel (show 2*a*b≤a^2+2*b^2 by omega)
  dsimp [factors]
  omega

private abbrev Arms (u v : ℕ) : Prop :=
  (u=1 ∧ v=1) ∨ (u=25 ∧ v=29) ∨ (u=29 ∧ v=25) ∨ (u=37 ∧ v=41) ∨ (u=41 ∧ v=37)

set_option synthInstance.maxSize 1000 in
private theorem table : ∀ t ∈ [1,725,1517], ∀ u : Fin 100, 0<u.val → t%u.val=0 →
    u.val^4≤12*(t/u.val)^4 → (t/u.val)^4≤12*u.val^4 → Arms u.val (t/u.val) := by
  unfold Arms
  decide +kernel

private theorem arms {u v t : ℕ} (tp : 0<t) (menu : t=1 ∨ t=725 ∨ t=1517)
    (split : t=u*v) (uv : u^4≤12*v^4) (vu : v^4≤12*u^4) : Arms u v := by
  have fit : t≤2048 := by omega
  have bound : u<100 := by
    by_contra! big
    have small : v≤20 := by
      by_contra! high
      have := Nat.mul_le_mul big (show 21≤v by omega)
      omega
    have := Nat.pow_le_pow_left big 4
    have := Nat.pow_le_pow_left small 4
    omega
  have up : 0<u := Nat.pos_of_mul_pos_right (split ▸ tp)
  have div : t/u=v := by rw [split,Nat.mul_div_cancel_left _ up]
  have h := table t (by simpa using menu) ⟨u,bound⟩ up
    (Nat.mod_eq_zero_of_dvd (split ▸ dvd_mul_right u v))
  dsimp at h
  rw [div] at h
  exact h uv vu

/-- The quartic factors are within 257/256 of each other. Once their exact
denominator parts are removed, the possible prime ratios lie in disjoint bands. -/
theorem primitive_band {p q t : ℕ} (mem : (p,q)∈eligible) (hit : PrimitiveHit (p*q) t) :
    Band p q t := by
  obtain ⟨tp,fit,a,b,_,bp,cop,point,gap⟩ := hit
  obtain ⟨pl,ord,qu,pp,qp,_⟩ := SumGridPopulation.eligible_data.mp mem
  have bounds := PrimeFactors.QuarticPrimePopulation.eligible_bounds mem
  have pg : 2<p := (by decide +kernel : 2<FullRangeResidueEstimates.X).trans_le pl
  have po := pp.odd_of_ne_two pg.ne'
  have qo := qp.odd_of_ne_two (pg.trans ord).ne'
  have balanced : q≤2*p := qu.le.trans (Nat.mul_le_mul_left 2 pl)
  have menu := QuarticStripDenominators.primitive_menu pp qp po qo ord.le balanced
    bounds.1 bounds.2.1 tp fit bp cop point gap
  have limit := Nat.pow_le_pow_left fit 4
  have size : 6*t^4≤p*q := (show 6*t^4≤2^2047 by omega).trans bounds.1
  obtain ⟨u,v,split,_,either,uv,vu⟩ := QuarticDenominatorSplit.partition pp qp po qo ord.le balanced
    bp cop point size
  have pair := arms tp menu split uv vu
  have close := close_factors bounds.1 bounds.2.1 tp fit point gap
  have order : (factors a b).1≤(factors a b).2 := by dsimp [factors]; omega
  subst t
  rcases pair with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
    rcases either with ⟨left,right⟩|⟨left,right⟩ <;> rw [left,right] at close order <;>
    norm_num [Band] at close order ⊢ <;> omega

theorem primitive_unique {p q t s : ℕ} (mem : (p,q)∈eligible)
    (a : PrimitiveHit (p*q) t) (b : PrimitiveHit (p*q) s) : t=s :=
  band_unique (primitive_band mem a) (primitive_band mem b)

private theorem to_product {p q k l : ℕ} (positive : 0<q) (width : q^2<2^2048)
    (lp : 0<l) (ratio : k*p<l*q) : k*(p*q)<l*2^2048 := calc
  _ = (k*p)*q := by ring
  _ < (l*q)*q := Nat.mul_lt_mul_of_pos_right ratio positive
  _ = l*q^2 := by ring
  _ < _ := Nat.mul_lt_mul_of_pos_left width lp

theorem gates_of_band {p q t : ℕ} (mem : (p,q)∈eligible) (b : Band p q t) : Gates (p*q) t := by
  obtain ⟨_,_,qtop,_,qp,_⟩ := SumGridPopulation.eligible_data.mp mem
  have width : q^2<2^2048 := (Nat.pow_lt_pow_left qtop (by decide : 2≠0)).trans_eq (by decide +kernel)
  rcases b with ⟨one,_⟩|⟨small,r⟩|⟨large,r,_⟩
  · exact Or.inl one
  · exact Or.inr (Or.inl ⟨small,to_product qp.pos width (by decide) r⟩)
  · exact Or.inr (Or.inr ⟨large,to_product qp.pos width (by decide) r⟩)

/-- A successful unreduced reading has a successful primitive divisor that
satisfies both the factor-ratio band and the public product test. -/
theorem raw_hit {p q d : ℕ} (mem : (p,q)∈eligible) (dp : 0<d) (fit : d≤2048)
    (hit : (choices (d^4*(p*q))).Nonempty) :
    ∃ t : ℕ, t∣d ∧ Band p q t ∧ Gates (p*q) t ∧ (choices (t^4*(p*q))).Nonempty := by
  obtain ⟨_,ord,_,pp,qp,_⟩ := SumGridPopulation.eligible_data.mp mem
  have sf := (Nat.squarefree_mul ((Nat.coprime_primes pp qp).mpr ord.ne)).mpr ⟨pp.squarefree,qp.squarefree⟩
  obtain ⟨t,dvd,tp,small,x,y,xp,yp,cop,form,gap⟩ := ReduceQuarticDenominator.primitive_choice dp sf hit
  have b := primitive_band mem ⟨tp,small.trans fit,x,y,xp,yp,cop,form,gap⟩
  exact ⟨t,dvd,b,gates_of_band mem b,factors x y,
    ComplementaryQuarticProducts.mem_choices.mpr ⟨x,y,xp,yp,form,gap,rfl⟩⟩

end PrimeFactors.QuarticDenominatorBands
