import PrimeFactors.TracePrimePartners
import PrimeFactors.TraceCollisionOrder
import PrimeFactors.TraceCollisionWidth
import PrimeFactors.TraceCollisionPopulation

/-! Incidence limit for powers of two in the initial weighted-trace blocks.
A congruence modulo either prime suffices, including a match at a padded label. -/

namespace PrimeFactors.TraceCollisionLimit
open Finset TraceCoverCertificate

set_option exponentiation.threshold 8192
set_option maxRecDepth 8192

/-- The period of the chosen starting-power base on a coprime modulus. -/
noncomputable def periodFor (base p : ℕ) : ℕ :=
  if h : base.Coprime p then orderOf ((ZMod.unitOfCoprime base h)^24) else 0

/-- The powers compared by a stride-24 record agree modulo the distinguished
prime. Every index in every permitted block is allowed, even padding in the last block. -/
def RowMatchAt (base p q : ℕ) : Prop :=
  ∃ (s : Slope) (m g j : ℕ), (s.a,s.b)∈TraceHitFrequency.directions (2^32) ∧
    validStart (p*q) s ∧ m≤2^64 ∧ g≤2^64 ∧ j<m*g ∧
    (base:ZMod p)^((24/s.step)*(s.a+s.b*(p*q))) =
      (base:ZMod p)^((24/s.step)*(s.start+s.step*j))

/-- A starting-power order check or a match in the block search. -/
def MatchAt (base p q : ℕ) : Prop :=
  (∃ j : ℕ, 0<j ∧ j≤2^64 ∧ p∣base^(24*j)-1) ∨ RowMatchAt base p q

/-- The first label alone can split the product even though its true sum is
larger. This is one of the extra events counted by the modular theorem. -/
theorem accidental_33017 :
    Nat.Prime 137 ∧ Nat.Prime 241 ∧ 137*241=33017 ∧
    validStart 33017 ⟨1,1,366,12⟩ ∧ 137+241=378 ∧
    (2:ℕ)^((24/12)*(1+33017-366))%33017=4580 ∧ Nat.gcd (4580-1) 33017=241 := by
  decide +kernel

private theorem nonnegative_tick {h H S z M L : ℕ} {E : ℝ} (hp : 0<H)
    (order : H≤h) (short : L<H) (size : S≤M) (cong : (h:ℤ)∣(S:ℤ)-z) (pos : 0≤E)
    (above : 0≤E-((S:ℝ)-z)) (below : E-((S:ℝ)-z)≤L) :
    ∃ t : ℕ, t<M/H+1 ∧ ((t*h:ℕ):ℝ)≤E ∧ E≤((t*h:ℕ):ℝ)+L := by
  obtain ⟨k,eq⟩ := cong
  have e : (S:ℝ)-z=(h:ℝ)*k := by exact_mod_cast eq
  have kn : 0≤k := by
    by_contra! neg
    have negOne : (k:ℝ)≤-1 := by exact_mod_cast (show k≤-1 by omega)
    have v := mul_le_mul_of_nonneg_left negOne (show (0:ℝ)≤h by positivity)
    have small : (L:ℝ)<h := by exact_mod_cast short.trans_le order
    linarith
  lift k to ℕ using kn with t
  have actual : t*h≤S := by
    exact_mod_cast (show (t:ℤ)*h≤S by linarith only [eq,Int.natCast_nonneg z])
  have bound := (Nat.mul_le_mul_left t order).trans (actual.trans size)
  refine ⟨t,Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hp).mpr bound),?_,?_⟩ <;>
    push_cast at * <;> linarith

private theorem coordinate_bounds {a b k : ℕ} (mem : (a,b)∈TraceHitFrequency.directions k) :
    a≤2*k ∧ b≤k := by
  have inside := mem_product.mp (mem_filter.mp mem).1
  exact ⟨(mem_Icc.mp inside.1).2,(mem_Icc.mp inside.2).2⟩

attribute [local irreducible] TraceHitFrequency.directions TraceCollisionPopulation.oriented

/-- A real modular-power match has a nonnegative period multiple in this
bounded list unless the anchor prime belongs to the exceptional order set. -/
theorem bands_of_match {base p q : ℕ} (bmin : 2≤base) (bmax : base≤2^22)
    (ep : TracePrimePartners.Eligible p) (eq : TracePrimePartners.Eligible q)
    (hit : MatchAt base p q) :
    p∈TraceCollisionOrder.lowFor base (2^470) ∨
    ∃ w∈TraceHitFrequency.directions (2^32), ∃ t<3*(2*(2^32))*2^1024/2^470+1,
      ((t*periodFor base p:ℕ):ℝ)≤TraceCollisionWidth.excess w.1 w.2 p q ∧
      TraceCollisionWidth.excess w.1 w.2 p q≤((t*periodFor base p:ℕ):ℝ)+(2^133:ℕ) := by
  obtain ⟨pp,lo,hi⟩ := ep
  rcases hit with ⟨j,jp,jb,div⟩ | ⟨s,m,g,j,mem,ok,mb,gb,jb,matchP⟩
  · exact Or.inl (TraceCollisionOrder.mem_lowFor.mpr ⟨lo,hi,pp,j,jp,
      jb.trans (by decide +kernel),div⟩)
  by_cases bad : p∈TraceCollisionOrder.lowFor base (2^470)
  · exact Or.inl bad
  right
  have cop := TraceCollisionOrder.target_base_coprime bmin bmax lo pp
  have large : 2^470≤periodFor base p := by
    rw [periodFor,dif_pos cop]
    by_contra! small
    exact bad (TraceCollisionOrder.mem_of_order_le_base lo hi pp cop small.le)
  have st := (of_decide_eq_true ok).2.1
  have step : s.step ∣ 24 := st ▸ Nat.gcd_dvd_left _ _
  have congr := TraceCollisionOrder.record_difference_base pp cop step matchP
  let S := s.a*p+s.b*q
  let z := s.start+s.step*j
  have congr' : (periodFor base p:ℤ) ∣ (S:ℤ)-z := by
    rw [periodFor,dif_pos cop]
    simpa only [S,z,Nat.cast_add,Nat.cast_mul] using congr
  obtain ⟨amax,bmax⟩ := @coordinate_bounds s.a s.b (2^32) mem
  have upper : S≤3*(2*(2^32))*2^1024 := by
    have lhs := Nat.mul_le_mul amax hi.le
    have rhs := Nat.mul_le_mul bmax eq.2.2.le
    dsimp [S]
    exact (Nat.add_le_add lhs rhs).trans (by decide +kernel)
  have raw := TraceCollisionWidth.label_window ok jb
  have cap : s.step*(m*g)≤2^133 :=
    (Nat.mul_le_mul (Nat.le_of_dvd (by decide) step) (Nat.mul_le_mul mb gb)).trans (by decide +kernel)
  have bound := nonnegative_tick (by decide +kernel : 0<(2:ℕ)^470) large
    (by decide +kernel : (2:ℕ)^133<2^470) upper congr' (TraceCollisionWidth.excess_nonneg _ _ _ _)
    raw.1 (raw.2.le.trans (by exact_mod_cast cap))
  exact ⟨(s.a,s.b),mem,bound⟩

private theorem event {base p q : ℕ} (minB : 2≤base) (maxB : base≤2^22)
    (ep : TracePrimePartners.Eligible p) (eq : TracePrimePartners.Eligible q)
    (hit : MatchAt base p q ∨ MatchAt base q p) :
    TraceCollisionPopulation.Event (TraceCollisionOrder.lowFor base (2^470))
      (fun r _ => periodFor base r) p q := by
  have anchored {r v : ℕ} (er : TracePrimePartners.Eligible r) (ev : TracePrimePartners.Eligible v)
      (matchR : MatchAt base r v) : r∈TraceCollisionOrder.lowFor base (2^470) ∨
      TraceCollisionPopulation.HighHit (fun u _ => periodFor base u) r v := by
    rcases bands_of_match minB maxB er ev matchR with low | ⟨w,mem,t,cap,band⟩
    · exact Or.inl low
    · exact Or.inr ⟨w,TraceCollisionPopulation.mem_weights mem,t,cap,band⟩
  rcases hit with h | h
  · rcases anchored ep eq h with bad | good
    · exact Or.inl bad
    · exact Or.inr (Or.inl good)
  · exact Or.inr (Or.inr (anchored eq ep h))

/-- For any single fixed small integer base (including 2), a starting-power
or block equality at either prime occurs for fewer than one pair in 2^66
under the stated population normalization. -/
theorem fraction {pairs : Finset (ℕ×ℕ)} {pool : Finset ℕ} {pop base : ℕ}
    (minB : 2≤base) (maxB : base≤2048^2)
    (primes : ∀ p∈pool, TracePrimePartners.Eligible p) (den : 2^1023*pool.card<44331*pop)
    (support : ∀ x∈pairs, x.1∈pool ∧ x.2∈pool ∧ (MatchAt base x.1 x.2 ∨ MatchAt base x.2 x.1)) :
    2^66*pairs.card<pop := by
  have cap : base≤2^22 := maxB.trans (by decide +kernel)
  apply TraceCollisionPopulation.fixed_small_base minB cap (fun p _ => periodFor base p)
    (fun q hq => (primes q hq).2.2.le) den
  intro x hx
  obtain ⟨hp,hq,hit⟩ := support x hx
  exact ⟨hp,hq,event minB cap (primes _ hp) (primes _ hq) hit⟩

/-- Even trying every integer base up to the squared product bit length (or
choosing the base after inspecting the input) can reach fewer than one in
2^44 target pairs at the same block and denominator budgets. -/
theorem small_bases {pairs : Finset (ℕ×ℕ)} {pool : Finset ℕ} {pop : ℕ}
    (primes : ∀ p∈pool, TracePrimePartners.Eligible p)
    (den : 2^1023*pool.card<44331*pop)
    (support : ∀ x∈pairs, x.1∈pool ∧ x.2∈pool ∧ ∃ base : ℕ, 2≤base ∧ base≤2048^2 ∧
      (MatchAt base x.1 x.2 ∨ MatchAt base x.2 x.1)) :
    2^44*pairs.card<pop := by
  apply TraceCollisionPopulation.adaptive_fraction (fun base p _ => periodFor base p)
    (fun q hq => (primes q hq).2.2.le) den
  intro x hx
  obtain ⟨hp,hq,base,minB,maxB,hit⟩ := support x hx
  have cap : base≤2^22 := maxB.trans (by decide +kernel)
  exact ⟨hp,hq,base,minB,cap,event minB cap (primes _ hp) (primes _ hq) hit⟩

end PrimeFactors.TraceCollisionLimit
