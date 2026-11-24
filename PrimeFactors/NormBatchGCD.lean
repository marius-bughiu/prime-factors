import PrimeFactors.CanonicalNorm
import Mathlib.Algebra.BigOperators.Associated

namespace PrimeFactors.NormBatchGCD

/-- The magnitude of the signed norm at a positive grid point. -/
def leaf (b : ℤ) (u v : ℕ) : ℕ := ((u : ℤ)^2-b*(v : ℤ)^2).natAbs

/-- The public square grid includes each ordered pair once. -/
noncomputable def gridProduct (b : ℤ) (H : ℕ) : ℕ :=
  ∏ v ∈ Finset.Icc 1 H, ∏ u ∈ Finset.Icc 1 H, leaf b u v

private theorem dvd_leaf_iff {s u v : ℕ} {b : ℤ} :
    s ∣ leaf b u v ↔ (u : ZMod s)^2-(b : ZMod s)*(v : ZMod s)^2 = 0 := by
  rw [leaf, ← Int.natCast_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rfl

/-- A nonzero square root modulo p puts a multiple of p in the grid. -/
theorem split_dvd_grid {p H : ℕ} [Fact p.Prime] {b z : ℤ}
    (pos : 0 < H) (short : H < p) (wide : p < (H+1)^2)
    (nonzero : (z : ZMod p) ≠ 0) (root : (z : ZMod p)^2 = b) :
    p ∣ gridProduct b H := by
  obtain ⟨v,t,vpos,vmax,tn,tmax,hit⟩ :=
    NormOrbit.local_box (-b) z pos short wide (isUnit_iff_ne_zero.mpr nonzero)
      (by simpa using root)
  have usq : (t.natAbs : ℤ)^2=t^2 := by rw [Int.natCast_natAbs,sq_abs]
  have ucast : (t.natAbs : ZMod p)^2=(t : ZMod p)^2 := by
    simpa only [Int.cast_pow, Int.cast_natCast] using congrArg (fun w : ℤ => (w : ZMod p)) usq
  have upos : 0 < t.natAbs := Nat.pos_of_ne_zero (by simpa using tn)
  have umax : t.natAbs ≤ H := by exact_mod_cast (show (t.natAbs : ℤ) ≤ H by simpa using tmax)
  have hp := (Fact.out : p.Prime).prime
  apply (hp.dvd_finset_prod_iff _).mpr
  refine ⟨v,Finset.mem_Icc.mpr ⟨vpos,vmax⟩,(hp.dvd_finset_prod_iff _).mpr ?_⟩
  refine ⟨t.natAbs,Finset.mem_Icc.mpr ⟨upos,umax⟩,dvd_leaf_iff.mpr ?_⟩
  rw [ucast]
  simpa [sub_eq_add_neg] using hit

/-- A nonsquare modulo q excludes q from the entire grid when H < q. -/
theorem inert_not_dvd_grid {q H : ℕ} [Fact q.Prime] {b : ℤ}
    (short : H < q) (inert : ¬ IsSquare (b : ZMod q)) :
    ¬ q ∣ gridProduct b H := by
  have hq := (Fact.out : q.Prime).prime
  intro divides
  obtain ⟨v,vm,row⟩ := (hq.dvd_finset_prod_iff _).mp divides
  obtain ⟨u,_,point⟩ := (hq.dvd_finset_prod_iff _).mp row
  have bounds := Finset.mem_Icc.mp vm
  have vunit : (v : ZMod q) ≠ 0 := by
    intro h
    exact (Nat.not_dvd_of_pos_of_lt bounds.1 (bounds.2.trans_lt short))
      ((ZMod.natCast_zmod_eq_zero_iff_dvd v q).mp h)
  exact NormOrbit.inert_leaf _ _ _ vunit inert (dvd_leaf_iff.mp point)

/-- A product divisible by p and coprime to the prime q yields p directly. -/
theorem one_batch {p q P : ℕ} (hq : q.Prime) (hit : p ∣ P) (miss : ¬ q ∣ P) :
    Nat.gcd P (p*q) = p := by
  rw [Nat.gcd_comm, Nat.mul_comm p q]
  exact Nat.gcd_mul_of_coprime_of_dvd (hq.coprime_iff_not_dvd.mpr miss) hit

/-- Retaining positive values through the square root of the product excludes
the larger prime from every leaf, independently of the formula for the values. -/
theorem threshold_gcd {ι : Type*} (s : Finset ι) (V : ι → ℕ) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (lt : p < q)
    (range : ∀ i ∈ s, 0 < V i ∧ V i ≤ Nat.sqrt (p*q))
    (hit : ∃ i ∈ s, p ∣ V i) : Nat.gcd (∏ i ∈ s, V i) (p*q) = p := by
  apply one_batch hq ((hp.prime.dvd_finset_prod_iff V).mpr hit)
  intro h
  obtain ⟨i,mem,dvd⟩ := (hq.prime.dvd_finset_prod_iff V).mp h
  have below := Nat.sqrt_lt.mpr (Nat.mul_lt_mul_of_pos_right lt hq.pos)
  exact (Nat.not_dvd_of_pos_of_lt (range i mem).1 ((range i mem).2.trans_lt below)) dvd

/-- The gcd of the full public batch is exactly the split prime. -/
theorem grid_gcd {p q H : ℕ} [Fact p.Prime] [Fact q.Prime] {b z : ℤ}
    (pos : 0 < H) (pshort : H < p) (qshort : H < q) (wide : p < (H+1)^2)
    (nonzero : (z : ZMod p) ≠ 0) (root : (z : ZMod p)^2 = b)
    (inert : ¬ IsSquare (b : ZMod q)) :
    Nat.gcd (gridProduct b H) (p*q) = p := by
  exact one_batch (Fact.out : q.Prime) (split_dvd_grid pos pshort wide nonzero root)
    (inert_not_dvd_grid qshort inert)

/-- For the indefinite form the positive value is 2*a²-t². The other two
forms contribute the positive values t²+a² and t²+2*a². -/
def bandValue (w : ℤ × ℤ × ℤ) : ℤ :=
  if w.1 = 2 then 2*w.2.2^2-w.2.1^2 else w.2.1^2-w.1*w.2.2^2

/-- Public triples (discriminant, numerator, denominator) in the annulus.
All three forms require an odd numerator. Only -2 uses odd denominators. -/
noncomputable def bandCells (N L : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  let coordinates := Finset.Icc (1 : ℤ) (N.sqrt.sqrt : ℤ)
  (({-1, -2, 2} : Finset ℤ) ×ˢ (coordinates ×ˢ coordinates)).filter fun w =>
    w.2.1 % 2 = 1 ∧ w.2.2 % 2 = (if w.1 = -2 then 1 else 0) ∧
      0 < bandValue w ∧ (L : ℤ) ≤ bandValue w ∧ bandValue w ≤ (N.sqrt : ℤ)

/-- The positive in-band product, counting a value once per retained triple. -/
noncomputable def bandProduct (N L : ℕ) : ℕ :=
  ∏ w ∈ bandCells N L, (bandValue w).toNat

/-- An indefinite norm from the short prime representation has t < a. -/
noncomputable def canonicalBandCells (N L : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (bandCells N L).filter fun w => w.1 = 2 → w.2.1 < w.2.2

noncomputable def canonicalBandProduct (N L : ℕ) : ℕ :=
  ∏ w ∈ canonicalBandCells N L, (bandValue w).toNat

/-- Every odd smaller prime occurs even after tightening the indefinite form. -/
theorem canonical_hit {p q L : ℕ} [Fact p.Prime]
    (odd : p ≠ 2) (lt : p < q) (lower : L ≤ p) :
    ∃ w ∈ canonicalBandCells (p*q) L, bandValue w = p := by
  have ppos := (Fact.out : p.Prime).pos
  have pmax : p ≤ (p*q).sqrt := Nat.le_sqrt.mpr (Nat.mul_le_mul_left p lt.le)
  obtain ⟨t,a,tp,ap,ts,asq,parity,cases⟩ := ShortNormBox.prime_representation odd
  have coord {u : ℤ} (pos : 0 < u) (small : u^2 < p) :
      u ∈ Finset.Icc (1 : ℤ) ((p*q).sqrt.sqrt : ℤ) := by
    have natSmall : u.toNat^2 < p := by
      exact_mod_cast (show (u.toNat : ℤ)^2 < (p : ℤ) by
        rwa [Int.toNat_of_nonneg pos.le])
    have high := Nat.le_sqrt'.mpr (natSmall.le.trans pmax)
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  obtain ⟨d,fd,aden,order,repr⟩ : ∃ d : ℤ, d ∈ ({-1,-2,2} : Finset ℤ) ∧
      a%2 = (if d = -2 then 1 else 0) ∧ (d = 2 → t < a) ∧ bandValue (d,t,a) = p := by
    rcases cases with ⟨ae,rep⟩ | ⟨ao,rep⟩ | ⟨ae,rep⟩
    · refine ⟨-1, by decide, by simpa using ae, by norm_num, ?_⟩
      simpa [bandValue] using rep.symm
    · refine ⟨-2, by decide, by simpa using ao, by norm_num, ?_⟩
      simpa [bandValue] using rep.symm
    · refine ⟨2, by decide, by simpa using ae, fun _ => ?_, by simpa [bandValue] using rep.symm⟩
      apply lt_of_not_ge
      intro bad
      have hsq := pow_le_pow_left₀ ap.le bad 2
      linarith
  refine ⟨(d,t,a), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩,order⟩, repr⟩
  · exact Finset.mem_product.mpr ⟨fd, Finset.mem_product.mpr ⟨coord tp ts, coord ap asq⟩⟩
  · exact ⟨parity, aden, by rw [repr]; exact_mod_cast ppos,
              by rw [repr]; exact_mod_cast lower, by rw [repr]; exact_mod_cast pmax⟩

private theorem band_bounds {N L : ℕ} {w : ℤ × ℤ × ℤ} (hw : w ∈ bandCells N L) :
    0 < (bandValue w).toNat ∧ (bandValue w).toNat ≤ N.sqrt := by
  obtain ⟨_,_,pos,_,high⟩ := (Finset.mem_filter.mp hw).2
  omega

/-- Every odd smaller prime occurs in the public annulus. The inputs to
the product itself are just N and any lower bound L on its smaller prime. -/
theorem smaller_prime_gcd {p q L : ℕ} [Fact p.Prime] [Fact q.Prime]
    (odd : p ≠ 2) (lt : p < q) (lower : L ≤ p) :
    Nat.gcd (bandProduct (p*q) L) (p*q) = p := by
  apply threshold_gcd (bandCells (p*q) L) _ Fact.out Fact.out lt (fun _ => band_bounds)
  obtain ⟨w, hw, eq⟩ := canonical_hit odd lt lower
  exact ⟨w, (Finset.mem_filter.mp hw).1, by simp [eq]⟩

theorem canonical_gcd {p q L : ℕ} [Fact p.Prime] [Fact q.Prime]
    (odd : p ≠ 2) (lt : p < q) (lower : L ≤ p) :
    Nat.gcd (canonicalBandProduct (p*q) L) (p*q) = p := by
  apply threshold_gcd (canonicalBandCells (p*q) L) _ Fact.out Fact.out lt
    (fun _ hw => band_bounds (Finset.mem_filter.mp hw).1)
  obtain ⟨w, hw, eq⟩ := canonical_hit odd lt lower
  exact ⟨w, hw, by simp [eq]⟩

/-- These are the signed leaf factors obtained by evaluating X−t² at d*a². -/
noncomputable def polynomialProduct (N L : ℕ) : ℤ :=
  ∏ w ∈ bandCells N L, (w.1*w.2.2^2-w.2.1^2)

private def magnitude : ℤ →* ℕ where
  toFun := Int.natAbs
  map_one' := rfl
  map_mul' := Int.natAbs_mul

/-- Taking the absolute value of the signed evaluation product produces
exactly the positive band product, including when the two signs are mixed. -/
theorem polynomialProduct_natAbs (N L : ℕ) :
    (polynomialProduct N L).natAbs = bandProduct N L := by
  unfold polynomialProduct bandProduct
  rw [show (∏ w ∈ bandCells N L, (w.1*w.2.2^2-w.2.1^2)).natAbs =
    ∏ w ∈ bandCells N L, (w.1*w.2.2^2-w.2.1^2).natAbs from map_prod magnitude _ _]
  apply Finset.prod_congr rfl
  intro w hw
  obtain ⟨_,_,pos,_,_⟩ := (Finset.mem_filter.mp hw).2
  have absEq : (w.1*w.2.2^2-w.2.1^2).natAbs = (bandValue w).natAbs := by
    by_cases d : w.1 = 2
    · simp [bandValue,d]
    · simp only [bandValue, if_neg d]
      rw [← Int.natAbs_neg (w.2.1^2-w.1*w.2.2^2),neg_sub]
  rw [absEq]
  exact_mod_cast (show ((bandValue w).natAbs : ℤ) = ((bandValue w).toNat : ℤ) by
    rw [Int.natCast_natAbs,abs_of_nonneg pos.le,Int.toNat_of_nonneg pos.le])

/-- The gcd obtained with signed polynomial evaluations is the same prime. -/
theorem polynomial_gcd {p q L : ℕ} [Fact p.Prime] [Fact q.Prime]
    (odd : p ≠ 2) (lt : p < q) (lower : L ≤ p) :
    Int.gcd (polynomialProduct (p*q) L) ((p*q : ℕ) : ℤ) = p := by
  simpa only [Int.gcd, Int.natAbs_natCast, polynomialProduct_natAbs] using
    (smaller_prime_gcd odd lt lower)

/-- The lower bound 3 supplies a formula with the product alone as input. -/
theorem product_only_gcd {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (odd : p ≠ 2) (lt : p < q) :
    Nat.gcd (bandProduct (p*q) 3) (p*q) = p := by
  have := (Fact.out : p.Prime).two_le
  exact smaller_prime_gcd odd lt (by omega)

/-- For q ≤ 2p the public lower cutoff is ceil(sqrt(ceil(N/2))), or 3
if larger. This matches the balanced search's integer square-root rounding. -/
theorem balanced_gcd {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (odd : p ≠ 2) (lt : p < q) (balanced : q ≤ 2*p) :
    Nat.gcd (bandProduct (p*q) (max 3 (((p*q-1)/2).sqrt+1))) (p*q) = p := by
  have pp : p.Prime := Fact.out
  have low := pp.two_le
  have pos : 0 < p*q := Nat.mul_pos pp.pos (Fact.out : q.Prime).pos
  have less : p*q-1 < p^2*2 := calc
    p*q-1 < p*q := by omega
    _ ≤ p*(2*p) := Nat.mul_le_mul_left p balanced
    _ = p^2*2 := by ring
  have cut := Nat.sqrt_lt'.mpr ((Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr less)
  exact smaller_prime_gcd odd lt (max_le (by omega) (by omega))

private theorem once_in_product {ι : Type*} (S : Finset ι) (V : ι → ℕ) {p : ℕ}
    (pp : p.Prime) {w : ι} (mem : w ∈ S) (value : V w = p)
    (unique : ∀ i ∈ S, p ∣ V i → i = w) :
    p ∣ (∏ i ∈ S, V i) ∧ ¬ p^2 ∣ (∏ i ∈ S, V i) := by
  classical
  have tail : ¬p ∣ ∏ i ∈ S.erase w, V i := by
    intro h
    obtain ⟨i,inside,hit⟩ := (pp.prime.dvd_finset_prod_iff V).mp h
    obtain ⟨ne,ins⟩ := Finset.mem_erase.mp inside
    exact ne (unique i ins hit)
  have decomp := (Finset.mul_prod_erase S V mem).symm
  rw [value] at decomp
  rw [decomp,pow_two]
  exact ⟨dvd_mul_right p _, fun h => tail ((Nat.mul_dvd_mul_iff_left pp.pos).mp h)⟩

private theorem divisible_value {p q L : ℕ} [Fact p.Prime] [Fact q.Prime]
    (lt : p < q) (balanced : q ≤ 2*p) {w : ℤ × ℤ × ℤ}
    (inside : w ∈ canonicalBandCells (p*q) L) (hit : p ∣ (bandValue w).toNat) :
    bandValue w = p := by
  have bounds := band_bounds (Finset.mem_filter.mp inside).1
  have below := Nat.sqrt_lt.mpr (Nat.mul_lt_mul_of_pos_right lt (Fact.out : q.Prime).pos)
  have small : (bandValue w).toNat < p*2 := by omega
  obtain ⟨m,hm⟩ := hit
  have pos := (Fact.out : p.Prime).pos
  have double : m < 2 := (Nat.mul_lt_mul_left pos).mp (hm ▸ small)
  have nz : m ≠ 0 := by intro zero; rw [zero,mul_zero] at hm; omega
  have one : m = 1 := by omega
  rw [one,mul_one] at hm
  omega

private theorem canonical_of_mem {N L : ℕ} {w : ℤ × ℤ × ℤ}
    (member : w ∈ canonicalBandCells N L) :
    CanonicalNorm.IsCanonical (bandValue w) w.1 w.2.1 w.2.2 := by
  obtain ⟨d,t,a⟩ := w
  obtain ⟨base,order⟩ := Finset.mem_filter.mp member
  obtain ⟨box,par,den,_,_,_⟩ := Finset.mem_filter.mp base
  obtain ⟨forms,coords⟩ := Finset.mem_product.mp box
  obtain ⟨tm,am⟩ := Finset.mem_product.mp coords
  have tp : 1 ≤ t := (Finset.mem_Icc.mp tm).1
  have ap : 1 ≤ a := (Finset.mem_Icc.mp am).1
  change a%2 = (if d = -2 then 1 else 0) at den
  change d = 2 → t < a at order
  have fd : d = -1 ∨ d = -2 ∨ d = 2 := by simpa using forms
  refine ⟨(by omega : 0 < t), (by omega : 0 < a), par, ?_⟩
  rcases fd with rfl | rfl | rfl
  · exact Or.inl ⟨rfl, by simpa using den, by simp [bandValue]⟩
  · exact Or.inr (Or.inl ⟨rfl, by simpa using den, by simp [bandValue]⟩)
  · exact Or.inr (Or.inr ⟨rfl, by simpa using den, order rfl, by simp [bandValue]⟩)

/-- In a balanced product, exactly one retained triple carries the smaller prime. -/
theorem unique_divisible_cell {p q L : ℕ} [Fact p.Prime] [Fact q.Prime]
    (odd : p ≠ 2) (lt : p < q) (balanced : q ≤ 2*p) (lower : L ≤ p) :
    ∃! w, w ∈ canonicalBandCells (p*q) L ∧ p ∣ (bandValue w).toNat := by
  obtain ⟨w, wm, eq⟩ := canonical_hit odd lt lower
  refine ⟨w, ⟨wm, by simp [eq]⟩, ?_⟩
  intro u hu
  have urep := canonical_of_mem hu.1
  have wrep := canonical_of_mem wm
  rw [divisible_value lt balanced hu.1 hu.2] at urep
  rw [eq] at wrep
  obtain ⟨d,t,a⟩ := CanonicalNorm.unique odd urep wrep
  exact Prod.ext d (Prod.ext t a)

/-- For p < q ≤ 2p the exact power of the smaller prime in the public
canonical product is one. Testing the square distinguishes this multiplicity. -/
theorem canonical_multiplicity_one {p q L : ℕ} [Fact p.Prime] [Fact q.Prime]
    (odd : p ≠ 2) (lt : p < q) (balanced : q ≤ 2*p) (lower : L ≤ p) :
    p ∣ canonicalBandProduct (p*q) L ∧ ¬p^2 ∣ canonicalBandProduct (p*q) L := by
  obtain ⟨w, ⟨wm, hit⟩, unique⟩ := unique_divisible_cell odd lt balanced lower
  apply once_in_product (canonicalBandCells (p*q) L) (fun x => (bandValue x).toNat)
    Fact.out wm
  · simp [divisible_value lt balanced wm hit]
  · exact fun i hi h => unique i ⟨hi,h⟩

end PrimeFactors.NormBatchGCD
