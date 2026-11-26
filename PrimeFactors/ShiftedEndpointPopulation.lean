import PrimeFactors.PredictedTraceCarries
import PrimeFactors.OffsetSquareSplit
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! A successful dyadic carry probe forces one of the actual primes close to
a multiple of its radix, even when its square came from unintended anchors. -/

namespace PrimeFactors.ShiftedEndpointPopulation
open Finset

set_option exponentiation.threshold 10000
set_option maxRecDepth 8192

/-- A proper gcd of one root forces the two primes into opposite roots.
No hypothesis on how the coefficient was chosen is required. -/
theorem allocation {p q c x y : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (prod : x*y=c*(p*q)) (nontrivial : 1<(p*q).gcd x) (proper : (p*q).gcd x<p*q) :
    ∃ a b : ℕ, c=a*b ∧ x+y=b*p+a*q := by
  have pc := (Nat.coprime_primes pp qp).mpr ne
  have px : p∣x*y := prod ▸ dvd_mul_of_dvd_right (dvd_mul_right p q) c
  have qx : q∣x*y := prod ▸ dvd_mul_of_dvd_right (dvd_mul_left q p) c
  have allocate (u v : ℕ) (pu : p∣u) (qv : q∣v) (ev : u*v=c*(p*q)) :
      ∃ a b : ℕ, c=a*b ∧ u+v=b*p+a*q := by
    obtain ⟨b,rfl⟩ := pu
    obtain ⟨a,rfl⟩ := qv
    refine ⟨a,b,Nat.eq_of_mul_eq_mul_left (Nat.mul_pos pp.pos qp.pos) ?_,by ring⟩
    calc
      _ = c*(p*q) := by ring
      _ = (p*b)*(q*a) := ev.symm
      _ = _ := by ring
  by_cases hp : p∣x
  · have nq : ¬q∣x := fun h => proper.ne (Nat.gcd_eq_left (pc.mul_dvd_of_dvd_of_dvd hp h))
    exact allocate x y hp ((qp.dvd_mul.mp qx).resolve_left nq) prod
  · have hq : q∣x := by
      by_contra hn
      have cop := (Nat.coprime_mul_iff_left.mpr ⟨pp.coprime_iff_not_dvd.mpr hp,qp.coprime_iff_not_dvd.mpr hn⟩)
      exact nontrivial.ne' cop.gcd_eq_one
    simpa only [Nat.add_comm y x] using
      allocate y x ((pp.dvd_mul.mp px).resolve_left hp) hq (by rwa [Nat.mul_comm y x])

/-- The trace prediction implies that the product of the two distances
is bounded by the low-carry budget, independently of the high carry. -/
theorem residual {p q D a b : ℕ} {L k : ℤ} (dp : 0<D)
    (rounded : 2*|(p:ℤ)*q-D*L|≤D)
    (trace : (b:ℤ)*p+a*q=(a:ℤ)*b*D+L-k) (budget : |k|≤4) :
    2*(|(p:ℤ)-a*D| * |(q:ℤ)-b*D|)≤9*D := by
  have eq : ((p:ℤ)-a*D)*((q:ℤ)-b*D)=(p*q-D*L)+D*k := by
    linear_combination -(D:ℤ)*trace
  rw [←abs_mul,eq]
  have cap := abs_add_le ((p:ℤ)*q-D*L) ((D:ℤ)*k)
  rw [abs_mul,abs_of_nonneg (by exact_mod_cast dp.le : 0≤(D:ℤ))] at cap
  have h := mul_le_mul_of_nonneg_left budget (show 0≤(D:ℤ) by positivity)
  linarith only [rounded,cap,h]

/-- Radius padded to an integer dyadic bound for counting. -/
def radius (e : ℕ) : ℕ := 3*2^((e+1)/2)

private theorem near_of_residual {p q a b e : ℕ}
    (h : 2*(|(p:ℤ)-a*(2:ℤ)^e| * |(q:ℤ)-b*(2:ℤ)^e|)≤9*(2:ℤ)^e) :
    |(p:ℤ)-a*2^e|≤(radius e:ℕ) ∨ |(q:ℤ)-b*2^e|≤(radius e:ℕ) := by
  have ep : e≤(e+1)/2+(e+1)/2 := by omega
  have pw := pow_le_pow_right₀ (show (1:ℤ)≤2 by decide) ep
  rw [pow_add] at pw
  by_contra! bad
  have v := mul_lt_mul_of_pos_left bad.2 (show 0<(radius e:ℤ) by
    unfold radius; positivity)
  have u := mul_lt_mul_of_pos_right bad.1 (show 0 < |(q:ℤ)-b*2^e| by
    have : (0:ℤ)≤(radius e:ℤ) := by positivity
    linarith only [bad.2,this])
  have t := v.trans u
  unfold radius at t
  push_cast at t
  nlinarith only [pw,t,h,sq_nonneg ((2:ℤ)^((e+1)/2))]

/-- The actual upper-root gcd supplies genuine anchor coefficients for every
proper output. Their weighted trace and product equal the public predictions. -/
theorem probe_allocation {p q D f : ℕ} {h k : ℤ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (hit : PredictedTraceCarries.probe (p*q) D h k=some f) :
    ∃ a b : ℕ, PredictedTraceCarries.coefficient (p*q) D h=(a:ℤ)*b ∧
      PredictedTraceCarries.label (p*q) D h k=(b:ℤ)*p+a*q := by
  let c := PredictedTraceCarries.coefficient (p*q) D h
  let t := PredictedTraceCarries.label (p*q) D h k
  let r := (t.toNat^2-4*c.toNat*(p*q)).sqrt
  let x := (t.toNat+r)/2
  let y := (t.toNat-r)/2
  have guards : 0<c ∧ 0<t ∧ r^2+4*c.toNat*(p*q)=t.toNat^2 ∧ (t.toNat+r)%2=0 ∧
      1<(p*q).gcd x ∧ (p*q).gcd x<p*q := by
    unfold PredictedTraceCarries.probe at hit
    dsimp only at hit
    split at hit
    next hg => exact hg
    next => contradiction
  have ⟨cs,ts,sq,_,g₁,g₂⟩ := guards
  obtain ⟨sum,prod⟩ := OffsetSquareSplit.root_identities (k:=1) (N:=c.toNat*(p*q))
    (S:=t.toNat) (d:=r) (by simp only [one_pow,mul_one]; linarith only [sq])
  change x+y=t.toNat at sum
  simp only [one_pow,Nat.mul_one] at prod
  change x*y=c.toNat*(p*q) at prod
  obtain ⟨a,b,ab,tr⟩ := allocation pp qp ne prod g₁ g₂
  have cz : c=(a:ℤ)*b := by rw [←Int.toNat_of_nonneg cs.le,ab,Nat.cast_mul]
  have tz : t=(b:ℤ)*p+a*q := by rw [←Int.toNat_of_nonneg ts.le,←sum,tr]; push_cast; rfl
  exact ⟨a,b,cz,tz⟩

/-- Every successful probe yields a simultaneous bound on the two genuine
prime displacements, even when the high carry was chosen arbitrarily. -/
theorem product_of_probe {p q D f : ℕ} {h k : ℤ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (d : 0<D) (small : |k|≤4) (hit : PredictedTraceCarries.probe (p*q) D h k=some f) :
    ∃ a b : ℕ, 2*(|(p:ℤ)-a*D| * |(q:ℤ)-b*D|)≤9*D := by
  obtain ⟨a,b,cz,tz⟩ := probe_allocation pp qp ne hit
  have trace : (b:ℤ)*p+a*q=(a:ℤ)*b*D+PredictedTraceCarries.nearest ((p:ℤ)*q) D-k := by
    rw [←tz,←cz]
    simp only [PredictedTraceCarries.label,Nat.cast_mul]
  exact ⟨a,b,residual d (PredictedTraceCarries.nearest_error (n:=(p:ℤ)*q) (by exact_mod_cast d)) trace small⟩

/-- The actual probe, including an accidental square, forces a near factor.
There is no bound on the high carry or coprimality restriction on its coefficient. -/
theorem near_of_probe {p q e f : ℕ} {h k : ℤ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (small : |k|≤4) (hit : PredictedTraceCarries.probe (p*q) (2^e) h k=some f) :
    (∃ a : ℕ, |(p:ℤ)-a*(2:ℤ)^e|≤(radius e:ℕ)) ∨ (∃ b : ℕ, |(q:ℤ)-b*(2:ℤ)^e|≤(radius e:ℕ)) := by
  obtain ⟨a,b,rz⟩ := product_of_probe pp qp ne (by positivity) small hit
  push_cast at rz
  exact (near_of_residual rz).imp (fun z => ⟨a,z⟩) (fun z => ⟨b,z⟩)

/-- Numbers in range of one positive radix multiple. The right endpoint
2^1024 is allowed as a multiple, even though no target prime equals it. -/
private def band (e : ℕ) : Finset ℕ :=
  (Icc 1 (2^(1024-e))).biUnion fun a =>
    Icc (a*2^e-radius e) (a*2^e+radius e)

private theorem mem_band {p a e : ℕ} (lo : 513≤e) (hi : e≤1024)
    (small : p<2^1024) (large : 2^1023≤p) (near : |(p:ℤ)-a*(2:ℤ)^e|≤(radius e:ℕ)) :
    p∈band e := by
  have d : 0<(2:ℕ)^e := by positivity
  have r : radius e < 2^e := by
    have step : (e+1)/2+2 ≤ e := by omega
    calc
      _ < 2^((e+1)/2+2) := by rw [pow_add]; unfold radius; have := Nat.pow_pos (n:=((e+1)/2)) (by decide : 0<2); omega
      _ ≤ _ := Nat.pow_le_pow_right (by decide) step
  have rt : radius e<2^1023 := by
    have a' : (e+1)/2≤512 := by omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by decide) a'))
      (by decide +kernel : 3*2^512 < (2:ℕ)^1023)
  have ⟨h₁,h₂⟩ := abs_le.mp near
  have l : a*2^e≤p+radius e := by exact_mod_cast (show (a:ℤ)*2^e≤p+(radius e:ℕ) by linarith only [h₁])
  have u : p≤a*2^e+radius e := by exact_mod_cast (show (p:ℤ)≤a*2^e+(radius e:ℕ) by linarith only [h₂])
  have pos : 1≤a := by by_contra! h; rw [show a=0 by omega,zero_mul,zero_add] at u; omega
  have cap : a≤2^(1024-e) := by
    by_contra! bad
    have bound := Nat.mul_le_mul_right (2^e) (Nat.succ_le_of_lt bad)
    rw [Nat.succ_mul,←pow_add,Nat.sub_add_cancel hi] at bound
    omega
  exact mem_biUnion.mpr ⟨a,mem_Icc.mpr ⟨pos,cap⟩,mem_Icc.mpr ⟨by omega,u⟩⟩

private theorem band_count (e : ℕ) :
    (band e).card≤2^(1024-e)*(2*radius e+1) := by
  calc
    _ ≤ _ := card_biUnion_le
    _ ≤ ∑ _a ∈ Icc 1 (2^(1024-e)), (2*radius e+1) := by
      apply sum_le_sum
      intro a _
      rw [Nat.card_Icc]; omega
    _ = _ := by simp [Nat.card_Icc]

/-- Public overestimate of the primes which could participate on either side. -/
private def reachable := (range 512).biUnion fun i => band (i+513)

noncomputable def cost : ℕ := ∑ i ∈ range 512, 2^(1024-(i+513))*(2*radius (i+513)+1)

attribute [local irreducible] band

private theorem mem_reachable {e z : ℕ} (lo : 513≤e) (hi : e≤1024) (mem : z∈band e) : z∈reachable := by
  unfold reachable
  apply mem_biUnion.mpr
  refine ⟨e-513,mem_range.mpr (by omega),?_⟩
  rw [Nat.sub_add_cancel lo]
  exact mem

private theorem reachable_count : reachable.card ≤ cost :=
  card_biUnion_le.trans (sum_le_sum fun i _ => band_count (i+513))


set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem price :
    0<cost ∧ 2^234*2*44331*cost ≤ (2:ℕ)^1023 := by
  decide +kernel

attribute [local irreducible] reachable cost

/-- The finite count before multiplying by the analytic population ratio. -/
theorem geometric_count {pairs : Finset (ℕ × ℕ)} {pool : Finset ℕ}
    (covered : ∀ x∈pairs, x.1∈pool ∧ x.2∈pool ∧ 2^1023≤x.1 ∧ x.1<2^1024 ∧
      2^1023≤x.2 ∧ x.2<2^1024 ∧ ∃ e, 513≤e ∧ e≤1024 ∧
      ((∃ a : ℕ, |(x.1:ℤ)-a*(2:ℤ)^e|≤(radius e:ℕ)) ∨
        (∃ b : ℕ, |(x.2:ℤ)-b*(2:ℤ)^e|≤(radius e:ℕ)))) : pairs.card ≤ pool.card*(2*cost) := by
  have sub : pairs ⊆ (reachable ×ˢ pool) ∪ (pool ×ˢ reachable) := by
    intro x hx
    obtain ⟨p,q,plo,phi,qlo,qhi,e,lo,hi,w⟩ := covered x hx
    rcases w with ⟨a,h⟩|⟨b,h⟩
    · exact mem_union_left _ (mem_product.mpr ⟨mem_reachable lo hi (mem_band lo hi phi plo h),q⟩)
    · exact mem_union_right _ (mem_product.mpr ⟨p,mem_reachable lo hi (mem_band lo hi qhi qlo h)⟩)
  have cnt := (card_le_card sub).trans (card_union_le _ _)
  rw [card_product,card_product,Nat.mul_comm pool.card reachable.card,←two_mul] at cnt
  exact cnt.trans (by
    calc
      2*(reachable.card*pool.card) ≤ 2*(cost*pool.card) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ reachable_count)
      _ = _ := by ring)

/-- The price still admits an extra 2^550 partners per first prime. -/
theorem reserve : 2^234*44331*(2*cost+2^550)≤(2:ℕ)^1023 := by
  unfold cost
  set_option maxRecDepth 12000 in decide +kernel

/-- The population premise is the published prime-count estimate. Both
orientations are counted. Every other finite bound is checked in Lean. -/
theorem population_fraction {pairs : Finset (ℕ × ℕ)} {pool : Finset ℕ} {pop : ℕ}
    (den : 2^1023*pool.card < 44331*pop)
    (covered : ∀ x∈pairs, x.1∈pool ∧ x.2∈pool ∧ 2^1023≤x.1 ∧ x.1<2^1024 ∧
      2^1023≤x.2 ∧ x.2<2^1024 ∧ ∃ e, 513≤e ∧ e≤1024 ∧
      ((∃ a : ℕ, |(x.1:ℤ)-a*(2:ℤ)^e|≤(radius e:ℕ)) ∨
        (∃ b : ℕ, |(x.2:ℤ)-b*(2:ℤ)^e|≤(radius e:ℕ)))) :
    2^234*pairs.card<pop := by
  have cnt := geometric_count covered
  have pos := price.1
  apply Nat.lt_of_mul_lt_mul_left (a:=2^1023)
  calc
    _ ≤ 2^1023*(2^234*(pool.card*(2*cost))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ cnt)
    _ = (2^1023*pool.card)*(2^234*2*cost) := by ac_rfl
    _ < (44331*pop)*(2^234*2*cost) := Nat.mul_lt_mul_of_pos_right den (by positivity)
    _ = (2^234*2*44331*cost)*pop := by ac_rfl
    _ ≤ _ := Nat.mul_le_mul_right _ price.2

/-- Population bound for all proper outputs with any high carry and any exponent
513 through 1024. A product-dependent selection of probes is permitted. -/
theorem successful_fraction {pairs : Finset (ℕ × ℕ)} {pool : Finset ℕ} {pop : ℕ}
    (den : 2^1023*pool.card < 44331*pop)
    (valid : ∀ x∈pairs, x.1∈pool ∧ x.2∈pool ∧ 2^1023≤x.1 ∧ x.1<2^1024 ∧
      2^1023≤x.2 ∧ x.2<2^1024 ∧ x.1.Prime ∧ x.2.Prime ∧ x.1≠x.2 ∧
      ∃ e, 513≤e ∧ e≤1024 ∧ ∃ h k : ℤ, |k|≤4 ∧ ∃ f,
        PredictedTraceCarries.probe (x.1*x.2) (2^e) h k=some f) :
    2^234*pairs.card<pop := by
  apply population_fraction den
  intro x hx
  obtain ⟨p,q,pl,pu,ql,qu,pp,qp,ne,e,lo,hi,h,k,cap,f,hit⟩ := valid x hx
  exact ⟨p,q,pl,pu,ql,qu,e,lo,hi,near_of_probe pp qp ne cap hit⟩

end PrimeFactors.ShiftedEndpointPopulation
