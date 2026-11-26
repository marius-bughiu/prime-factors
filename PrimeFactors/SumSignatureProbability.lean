import PrimeFactors.JointPeriod
import Mathlib.Algebra.BigOperators.Intervals

/-! Uniform independent tuples of units. A false signature in the balanced
sum interval requires a short period at each hidden prime simultaneously. -/

namespace PrimeFactors.SumSignatureProbability
open Finset

/-- Bounds for the diameter of the ordinary, product-defined balanced interval. -/
theorem diameter {p q s t : ℕ} (large : 64≤p) (pq : p≤q) (bal : q≤2*p)
    (lo : 4*(p*q)≤s^2) (hi : 2*t^2≤9*(p*q)) (ord : s≤t) :
    5*(t-s)<p-1 ∧ 8*(t-s)<q-1 := by
  have pos : 0<p*q := Nat.mul_pos (by omega) (by omega)
  have close : 49*t≤52*s := Nat.mul_self_le_mul_self_iff.mp (by nlinarith only [lo,hi,pos])
  have endp : t≤3*p := Nat.mul_self_le_mul_self_iff.mp (by
    nlinarith only [hi,Nat.mul_le_mul_left p bal])
  have endq : 8*t≤17*q := Nat.mul_self_le_mul_self_iff.mp (by
    nlinarith only [hi,Nat.mul_le_mul_right q pq])
  omega

/-- Base tuples admitting any positive repeat of at most W. -/
noncomputable def short (G : Type*) [Fintype G] [Group G] (k W : ℕ) : Finset (Fin k→G) := by
  classical
  exact univ.filter fun x => ∃ e ∈ Icc 1 W, ∀ i, x i ^ e=1

@[simp] theorem mem_short {G : Type*} [Fintype G] [Group G] {k W : ℕ} {x : Fin k→G} :
    x∈short G k W ↔ ∃ e ∈ Icc 1 W, ∀ i, x i ^ e=1 := by
  classical
  simp [short]

/-- The number of exceptional base tuples as a fraction of all tuples is at
most the finite reciprocal-power tail. No distribution of the factors enters. -/
theorem cyclic_bound {G : Type*} [Fintype G] [Group G] [IsCyclic G] {W a k : ℕ}
    (bound : a*W<Fintype.card G) :
    ((short G k W).card : ℚ) ≤ (Fintype.card G:ℚ)^k *
      ∑ d ∈ Ioc a (Fintype.card G), 1/(d:ℚ)^k := by
  classical
  let h := Fintype.card G
  have hp : 0<h := Fintype.card_pos
  let roots (d : ℕ) := univ.filter fun g : G => g^(h/d)=1
  let tuples (d : ℕ) := Fintype.piFinset (fun _ : Fin k => roots d)
  have subset : short G k W ⊆ (Ioc a h).biUnion tuples := by
    intro x hx
    obtain ⟨e,he,ex⟩ := mem_short.mp hx
    obtain ⟨ep,ew⟩ := mem_Icc.mp he
    let g := e.gcd h
    have gd : g∣h := Nat.gcd_dvd_right ..
    have gp : 0<g := Nat.gcd_pos_of_pos_left h ep
    have gw : g≤W := (Nat.gcd_le_left h ep).trans ew
    have big : a<h/g := by
      apply lt_of_not_ge
      intro small
      have mul := Nat.mul_le_mul small gw
      rw [Nat.div_mul_cancel gd] at mul
      omega
    apply mem_biUnion.mpr
    refine ⟨h/g,mem_Ioc.mpr ⟨big,Nat.div_le_self ..⟩,Fintype.mem_piFinset.mpr ?_⟩
    intro i
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rw [Nat.div_div_self gd hp.ne']
    exact pow_gcd_card_eq_one_iff.mp (ex i)
  have price {d : ℕ} (hd : d∈Ioc a h) :
      ((tuples d).card : ℚ) ≤ (h:ℚ)^k * (1/(d:ℚ)^k) := by
    obtain ⟨ad,dh⟩ := mem_Ioc.mp hd
    have dp : 0<d := by omega
    have count : (roots d).card ≤ h/d := IsCyclic.card_pow_eq_one_le (Nat.div_pos dh dp)
    change ((Fintype.piFinset (fun _ : Fin k => roots d)).card : ℚ) ≤ _
    rw [Fintype.card_piFinset_const, Nat.cast_pow]
    have dpos : 0<(d:ℚ) := by exact_mod_cast dp
    have ratio : ((roots d).card:ℚ) ≤ (h:ℚ)/d := (le_div_iff₀ dpos).mpr (by
      exact_mod_cast (Nat.mul_le_mul_right d count).trans (Nat.div_mul_le_self h d))
    simpa only [div_pow,mul_one_div] using pow_le_pow_left₀ (by positivity) ratio k
  have count := (card_le_card subset).trans card_biUnion_le
  calc
    _ ≤ ∑ d ∈ Ioc a h, ((tuples d).card:ℚ) := by exact_mod_cast count
    _ ≤ _ := by rw [mul_sum]; exact sum_le_sum (fun _ => price)

private theorem telescope {f F : ℕ → ℚ} (a : ℕ)
    (step : ∀ i, a ≤ i → f (i+1) ≤ F i-F (i+1)) (pos : ∀ i, a ≤ i → 0 < F i) :
    ∀ n, (∑ d ∈ Ioc a n, f d) < F a := by
  intro n
  by_cases small : n<a
  · have none : Ioc a n=∅ := Ioc_eq_empty (by omega)
    simpa [none] using pos a le_rfl
  have result (e : ℕ) : (∑ d ∈ Ioc a (a+e), f d) ≤ F a-F (a+e) := by
    induction e with
    | zero => simp
    | succ e ih =>
      rw [Nat.add_succ,sum_Ioc_succ_top (by omega)]
      linarith only [ih,step (a+e) (by omega)]
  obtain ⟨e,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt small)
  linarith only [result e,pos (a+e) (by omega)]

theorem tail_two {a : ℕ} (ap : 0<a) (n : ℕ) :
    (∑ d ∈ Ioc a n, 1/(d:ℚ)^2) < 1/(a:ℚ) := by
  apply telescope (F:=fun i => 1/(i:ℚ)) a _ _ n
  · intro i hi
    have ip : 0<(i:ℚ) := by exact_mod_cast ap.trans_le hi
    push_cast
    change 1/((i:ℚ)+1)^2 ≤ 1/i-1/((i:ℚ)+1)
    rw [div_sub_div _ _ ip.ne' (by positivity : (i:ℚ)+1≠0)]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [ip]
  · intro i hi
    exact one_div_pos.mpr (by exact_mod_cast ap.trans_le hi)

theorem tail_three {a : ℕ} (ap : 0<a) (n : ℕ) :
    (∑ d ∈ Ioc a n, 1/(d:ℚ)^3) < 1/(2*(a:ℚ)^2) := by
  apply telescope (F:=fun i => 1/(2*(i:ℚ)^2)) a _ _ n
  · intro i hi
    have ip : 0<(i:ℚ) := by exact_mod_cast ap.trans_le hi
    push_cast
    change 1/((i:ℚ)+1)^3 ≤ 1/(2*(i:ℚ)^2)-1/(2*((i:ℚ)+1)^2)
    rw [div_sub_div _ _ (by positivity : 2*(i:ℚ)^2≠0)
      (by positivity : 2*((i:ℚ)+1)^2≠0)]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [ip,sq_nonneg (i:ℚ),pow_nonneg ip.le 3]
  · intro i hi
    have ip : 0<(i:ℚ) := by exact_mod_cast ap.trans_le hi
    change 0 < 1/(2*(i:ℚ)^2)
    exact one_div_pos.mpr (mul_pos (by norm_num) (pow_pos ip _))

/-- CRT gives independent tuples on the two prime factors. A repeat over the
product must repeat at both projections, possibly allowing extra local tuples. -/
theorem product_count {G A B : Type*} [Fintype G] [Group G] [Fintype A] [Group A]
    [Fintype B] [Group B] (crt : G ≃* A × B) (k W : ℕ) :
    (short G k W).card≤(short A k W).card*(short B k W).card := by
  classical
  let split (x : Fin k→G) : (Fin k→A) × (Fin k→B) :=
    ⟨fun i => (crt (x i)).1, fun i => (crt (x i)).2⟩
  rw [←card_product]
  apply card_le_card_of_injOn split
  · intro x hx
    obtain ⟨e,he,good⟩ := mem_short.mp hx
    apply mem_product.mpr
    constructor
    · apply mem_short.mpr
      refine ⟨e,he,fun i => ?_⟩
      simpa [split] using congrArg (fun y : G => (crt y).1) (good i)
    · apply mem_short.mpr
      refine ⟨e,he,fun i => ?_⟩
      simpa [split] using congrArg (fun y : G => (crt y).2) (good i)
  · intro x _ y _ eq
    funext i
    apply crt.injective
    exact Prod.ext (congrArg (fun z : (Fin k→A) × (Fin k→B) => z.1 i) eq)
      (congrArg (fun z : (Fin k→A) × (Fin k→B) => z.2 i) eq)

private theorem target {p q W k rate : ℕ} [NeZero (p*q)] (hp : p.Prime) (hq : q.Prime) (ne : p≠q)
    (wp : 5*W<p-1) (wq : 8*W<q-1)
    (tails : (∑ d ∈ Ioc 5 (p-1), 1/(d:ℚ)^k) *
      (∑ d ∈ Ioc 8 (q-1), 1/(d:ℚ)^k) < 1/(rate:ℚ)) (rp : 0<rate) :
    rate*(short (ZMod (p*q))ˣ k W).card < ((p-1)*(q-1))^k := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  let crt := (Units.mapEquiv (ZMod.chineseRemainder ((Nat.coprime_primes hp hq).mpr ne)).toMulEquiv).trans MulEquiv.prodUnits
  have c := product_count crt k W
  have pcard := (Nat.prime_iff_card_units p).mp hp
  have qcard := (Nat.prime_iff_card_units q).mp hq
  have bp := cyclic_bound (G:=(ZMod p)ˣ) (k:=k) (a:=5) (W:=W) (by rwa [pcard])
  have bq := cyclic_bound (G:=(ZMod q)ˣ) (k:=k) (a:=8) (W:=W) (by rwa [qcard])
  rw [pcard] at bp
  rw [qcard] at bq
  have joint := mul_le_mul bp bq (by positivity) (le_trans (by positivity) bp)
  have cp : 0 < (↑(p-1):ℚ) := by exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
  have cq : 0 < (↑(q-1):ℚ) := by exact_mod_cast Nat.sub_pos_of_lt hq.one_lt
  have times := mul_lt_mul_of_pos_left tails (mul_pos (pow_pos cp k) (pow_pos cq k))
  rw [mul_one_div,lt_div_iff₀ (by exact_mod_cast rp)] at times
  have cast : ((short (ZMod (p*q))ˣ k W).card : ℚ) ≤
      (short (ZMod p)ˣ k W).card*(short (ZMod q)ˣ k W).card := by exact_mod_cast c
  have bound := mul_le_mul_of_nonneg_right (cast.trans joint) (show 0≤(rate:ℚ) by positivity)
  rw [mul_pow]
  exact_mod_cast (show (rate:ℚ)*(short (ZMod (p*q))ˣ k W).card <
    (↑(p-1):ℚ)^k*(↑(q-1):ℚ)^k by linarith only [bound,times])

/-- Fewer than one in forty ordered pairs of independent uniform units can
have a repeated signature anywhere across the whole balanced sum interval. -/
theorem two_bases {p q L U : ℕ} [NeZero (p*q)] (hp : p.Prime) (hq : q.Prime) (pq : p<q)
    (bal : q≤2*p) (large : 64≤p) (lo : 4*(p*q)≤L^2) (hi : 2*U^2≤9*(p*q)) (ord : L≤U) :
    40*(short (ZMod (p*q))ˣ 2 (U-L)).card < ((p-1)*(q-1))^2 := by
  have ⟨wp,wq⟩ := diameter large pq.le bal lo hi ord
  apply target hp hq pq.ne wp wq _ (by decide)
  have b := mul_lt_mul_of_nonneg_of_pos (tail_two (a:=5) (by decide) (p-1))
    (tail_two (a:=8) (by decide) (q-1)).le (sum_nonneg (fun d _ => one_div_nonneg.mpr (pow_nonneg (Nat.cast_nonneg d) _))) (by norm_num)
  norm_num at b ⊢
  exact b

/-- The same proof with three independently sampled units. -/
theorem three_bases {p q L U : ℕ} [NeZero (p*q)] (hp : p.Prime) (hq : q.Prime) (pq : p<q)
    (bal : q≤2*p) (large : 64≤p) (lo : 4*(p*q)≤L^2) (hi : 2*U^2≤9*(p*q)) (ord : L≤U) :
    6400*(short (ZMod (p*q))ˣ 3 (U-L)).card < ((p-1)*(q-1))^3 := by
  have ⟨wp,wq⟩ := diameter large pq.le bal lo hi ord
  apply target hp hq pq.ne wp wq _ (by decide)
  have b := mul_lt_mul_of_nonneg_of_pos (tail_three (a:=5) (by decide) (p-1))
    (tail_three (a:=8) (by decide) (q-1)).le (sum_nonneg (fun d _ => one_div_nonneg.mpr (pow_nonneg (Nat.cast_nonneg d) _))) (by norm_num)
  norm_num at b ⊢
  exact b

/-- Outside the counted exceptional set, matching the target powers identifies
the factor sum throughout the supplied interval. -/
theorem identify {p q L U s k : ℕ} [NeZero (p*q)] (hp : p.Prime) (hq : q.Prime)
    (ne : p≠q) (x : Fin k → (ZMod (p*q))ˣ) (regular : x∉short _ k (U-L))
    (candidate : s∈Icc L U) (trueSum : p+q∈Icc L U) :
    (∀ i, x i^s=x i^(p*q+1)) ↔ s=p+q := by
  constructor
  · intro matchAt
    have agree (i) := (matchAt i).trans (unit_pow_factorSum hp hq ne (x i)).symm
    have cannot {a b : ℕ} (lt : a<b) (low : L≤a) (hi : b≤U)
        (same : ∀ i, x i^a=x i^b) : False := by
      apply regular
      apply mem_short.mpr
      refine ⟨b-a,mem_Icc.mpr ⟨by omega,by omega⟩,fun i => ?_⟩
      have eqn : x i^a=x i^a*x i^(b-a) := by rw [←pow_add,Nat.add_sub_of_le lt.le,same i]
      exact (mul_eq_left.mp eqn.symm)
    obtain ⟨ls,us⟩ := mem_Icc.mp candidate
    obtain ⟨lt,ut⟩ := mem_Icc.mp trueSum
    rcases lt_trichotomy s (p+q) with h|equal|h
    · exact (cannot h ls ut agree).elim
    · exact equal
    · exact (cannot h lt us (fun i => (agree i).symm)).elim
  · rintro rfl i
    exact unit_pow_factorSum hp hq ne (x i)

end PrimeFactors.SumSignatureProbability
