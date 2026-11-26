import PrimeFactors.CenteredCarryDistances
import Mathlib.Data.Nat.Log

/-! Count *both* remainders in a successful carry probe. Dyadic ranges for
the first distance give a reciprocal range for the second one. -/

namespace PrimeFactors.CarryRemainderPairs

open Finset
set_option exponentiation.threshold 8192
set_option maxRecDepth 8192

private def origins (e : ℕ) := 2^(1024-e)+1

private noncomputable def band (e r : ℕ) : Finset ℕ :=
  (range (origins e)).biUnion fun a => Icc (a*2^e-r) (a*2^e+r)

private noncomputable def box (e extra i : ℕ) :=
  band e (2^(i+1)) ×ˢ band e (2^(e+extra-i))

private theorem band_card (e r : ℕ) :
    (band e r).card ≤ origins e*(2*r+1) := by
  calc
    _ ≤ _ := card_biUnion_le
    _ ≤ ∑ _a ∈ range (origins e), (2*r+1) := by
      apply sum_le_sum
      intro a _
      rw [Nat.card_Icc]
      omega
    _ = _ := by simp

private theorem box_card {e extra i : ℕ} (le : i ≤ e+extra) :
    (box e extra i).card ≤ (origins e)^2*18*2^(e+extra) := by
  have width (j : ℕ) : 2*2^j+1 ≤ 3*2^j := by
    have := Nat.two_pow_pos j
    omega
  have cap := Nat.mul_le_mul (band_card e (2^(i+1))) (band_card e (2^(e+extra-i)))
  rw [box,card_product]
  apply cap.trans
  calc
    _ ≤ (origins e*(3*2^(i+1)))*(origins e*(3*2^(e+extra-i))) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (width _)) (Nat.mul_le_mul_left _ (width _))
    _ = origins e^2*18*(2^i*2^(e+extra-i)) := by rw [pow_succ]; ring
    _ = _ := by rw [←pow_add,Nat.add_sub_of_le le]

private def distance (p a e : ℕ) := ((p:ℤ)-(a:ℤ)*2^e).natAbs

private theorem distance_pos {p a e : ℕ} (pp : p.Prime) (large : 2<p) (ep : 0<e) :
    0<distance p a e := by
  apply Int.natAbs_pos.mpr
  intro z
  have eq : p=a*2^e := by exact_mod_cast sub_eq_zero.mp z
  have two : 2∣p := eq ▸ dvd_mul_of_dvd_right (dvd_pow_self 2 (by omega : e≠0)) a
  rcases (Nat.dvd_prime pp).mp two with h|h <;> omega

private theorem mem_band {p a e r : ℕ} (pmax : p<2^1024) (emax : e≤1024)
    (anchor : distance p a e ≤ 2^e) (width : distance p a e ≤ r) : p∈band e r := by
  have abs_width : |(p:ℤ)-(a:ℤ)*2^e|≤(r:ℤ) := by
    rw [←Int.natCast_natAbs]; exact Int.ofNat_le.mpr width
  have abs_anchor : |(p:ℤ)-(a:ℤ)*2^e|≤((2^e:ℕ):ℤ) := by
    rw [←Int.natCast_natAbs]; exact Int.ofNat_le.mpr anchor
  obtain ⟨lo,hi⟩ := abs_le.mp abs_width
  have lo' := (abs_le.mp abs_anchor).1
  have am : a*2^e ≤ p+2^e := by
    push_cast at lo'
    exact_mod_cast (show (a:ℤ)*2^e ≤ p+2^e by linarith only [lo'])
  have amem : a<origins e := by
    apply lt_of_not_ge
    intro bound
    have huge := Nat.mul_le_mul_right (2^e) bound
    unfold origins at huge
    rw [Nat.add_mul,←pow_add,Nat.sub_add_cancel emax] at huge
    have := Nat.two_pow_pos e
    omega
  have l : a*2^e≤p+r := by exact_mod_cast (show (a:ℤ)*2^e≤p+r by linarith only [lo])
  have u : p≤a*2^e+r := by exact_mod_cast (show (p:ℤ)≤a*2^e+r by linarith only [hi])
  exact mem_biUnion.mpr ⟨a,mem_range.mpr amem,mem_Icc.mpr ⟨by omega,u⟩⟩

private theorem mem_box {p q a b e extra : ℕ} (pp : p.Prime) (qp : q.Prime)
    (pl : 2<p) (pu : p<2^1024) (ql : 2<q) (qu : q<2^1024)
    (ep : 0<e) (em : e≤1024) (ax : distance p a e ≤ 2^e) (ay : distance q b e ≤ 2^e)
    (area : distance p a e * distance q b e ≤ 2^(e+extra)) :
    ∃ i<e+extra+1, (p,q)∈box e extra i := by
  let x := distance p a e
  let y := distance q b e
  have xp : 0<x := distance_pos pp pl ep
  have yp : 0<y := distance_pos qp ql ep
  have xcap : x≤2^(e+extra) := (Nat.le_mul_of_pos_right x yp).trans area
  let i := Nat.log 2 x
  have ilo : 2^i≤x := Nat.pow_log_le_self _ xp.ne'
  have im : i≤e+extra := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (ilo.trans xcap)
  have xl : x≤2^(i+1) := (Nat.lt_pow_succ_log_self (by decide : 1<2) _).le
  have yl : y≤2^(e+extra-i) := by
    apply Nat.le_of_mul_le_mul_left _ (Nat.two_pow_pos i)
    rw [←pow_add,Nat.add_sub_of_le im]
    exact (Nat.mul_le_mul_right y ilo).trans area
  exact ⟨i,by omega,mem_product.mpr ⟨mem_band pu em ax xl,mem_band qu em ay yl⟩⟩

/-- Upper bound on the number of pairs in the dyadic rectangles. Overlaps
and nonprime coordinates are included. -/
def budget (e extra : ℕ) := (e+extra+1)*(origins e)^2*18*2^(e+extra)

private theorem total (e extra : ℕ) :
    ((range (e+extra+1)).biUnion (box e extra)).card ≤ budget e extra := by
  calc
    _ ≤ _ := card_biUnion_le
    _ ≤ ∑ _i ∈ range (e+extra+1), (origins e)^2*18*2^(e+extra) := by
      exact sum_le_sum fun i hi => box_card (by have := mem_range.mp hi; omega)
    _ = _ := by simp [budget,Nat.mul_assoc]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem sum_budget :
    (∑ j ∈ range 512, budget (513+j) 3) + 2^1551 < (2:ℕ)^1553 := by decide +kernel

private theorem count_cover {s : Finset (ℕ × ℕ)} {indices : Finset ℕ}
    (cells : ℕ → Finset (ℕ × ℕ)) (cost : ℕ → ℕ)
    (hit : ∀ z∈s, ∃ i∈indices, z∈cells i)
    (sizes : ∀ i∈indices, (cells i).card≤cost i) :
    s.card ≤ ∑ i∈indices, cost i := by
  have sub : s ⊆ indices.biUnion cells := fun z hz => mem_biUnion.mpr (hit z hz)
  exact (card_le_card sub).trans (card_biUnion_le.trans (sum_le_sum sizes))

private theorem nat_distance_bound {p a e v : ℕ} (h : |(p:ℤ)-a*(2:ℤ)^e|≤(v:ℤ)) :
    distance p a e ≤ v := by
  apply Int.ofNat_le.mp
  simpa only [distance,Int.natCast_natAbs] using h

/-- Count all pairs in the allowed remainder rectangles at the 512 tested
radices. The extra bits control the permitted product of the distances. -/
theorem count (extra : ℕ) {pairs : Finset (ℕ × ℕ)}
    (valid : ∀ z∈pairs, z.1.Prime ∧ z.2.Prime ∧ 2<z.1 ∧ z.1<2^1024 ∧
       2<z.2 ∧ z.2<2^1024 ∧ ∃ e, 513≤e ∧ e≤1024 ∧ ∃ a b : ℕ,
       |(z.1:ℤ)-a*(2:ℤ)^e|≤(2:ℤ)^e ∧ |(z.2:ℤ)-b*(2:ℤ)^e|≤(2:ℤ)^e ∧
       |(z.1:ℤ)-a*(2:ℤ)^e| * |(z.2:ℤ)-b*(2:ℤ)^e| ≤ 2^(e+extra)) :
    pairs.card ≤ ∑ j∈range 512, budget (513+j) extra := by
  let cells (j : ℕ) := (range (513+j+extra+1)).biUnion (box (513+j) extra)
  have cover : ∀ z∈pairs, ∃ j∈range 512, z∈cells j := by
    intro z hz
    obtain ⟨pp,qp,pl,pu,ql,qu,e,lo,hi,a,b,ax,ay,cap⟩ := valid z hz
    have area : distance z.1 a e * distance z.2 b e ≤ 2^(e+extra) := by
      apply Int.ofNat_le.mp
      simpa only [distance,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,Int.natCast_natAbs] using cap
    have ax' : distance z.1 a e ≤ 2^e := nat_distance_bound (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using ax)
    have ay' : distance z.2 b e ≤ 2^e := nat_distance_bound (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using ay)
    obtain ⟨i,im,hit⟩ := mem_box pp qp pl pu ql qu (by omega) hi ax' ay' area
    refine ⟨e-513,mem_range.mpr (by omega),?_⟩
    simp only [cells,Nat.add_sub_of_le lo]
    exact mem_biUnion.mpr ⟨i,mem_range.mpr im,hit⟩
  exact count_cover cells (fun j => budget (513+j) extra) cover (fun j _ => total (513+j) extra)

/-- The high correction can depend arbitrarily on the full product.
The low correction lies anywhere in the specified symmetric interval. -/
def HitWithin (K : ℕ) (z : ℕ × ℕ) : Prop :=
  z.1.Prime ∧ z.2.Prime ∧ z.1≠z.2 ∧ 2<z.1 ∧ z.1<2^1024 ∧
    2<z.2 ∧ z.2<2^1024 ∧ ∃ e, 513≤e ∧ e≤1024 ∧ ∃ h k : ℤ, |k|≤K ∧ ∃ f,
      PredictedTraceCarries.probe (z.1*z.2) (2^e) h k=some f

/-- A count for all proper probe outputs in a whole low-carry interval.
Choosing guesses or compressing the interval does not affect this bound. -/
theorem interval_count {K extra : ℕ} {pairs : Finset (ℕ × ℕ)} (width : K+1≤2^extra)
    (hits : ∀ z∈pairs, HitWithin K z) :
    pairs.card ≤ ∑ j∈range 512, budget (513+j) extra := by
  apply count
  intro z hz
  obtain ⟨pp,qp,ne,pl,pu,ql,qu,e,lo,hi,h,k,cap,f,hit⟩ := hits z hz
  obtain ⟨a,b,ax,ay,area⟩ := CenteredCarryDistances.of_probe pp qp ne (Nat.two_pow_pos e) cap hit
  push_cast at ax ay area
  have grow := mul_le_mul_of_nonneg_right
    (show (K:ℤ)+1≤2^extra by exact_mod_cast width) (by positivity : (0:ℤ)≤2^e)
  rw [mul_comm (2^extra:ℤ),←pow_add] at grow
  exact ⟨pp,qp,pl,pu,ql,qu,e,lo,hi,a,b,ax,ay,area.trans grow⟩

/-- The additive slack also accommodates the smaller-radix family. -/
theorem hit_count {pairs : Finset (ℕ × ℕ)} (hits : ∀ z∈pairs, HitWithin 4 z) :
    pairs.card + 2^1551 < 2^1553 := by
  have bound := interval_count (extra:=3) (by decide) hits
  exact (Nat.add_le_add_right bound _).trans_lt sum_budget

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem wide_budgets :
    (∑ j∈range 512, budget (513+j) 257) < (2:ℕ)^1807 ∧
    (∑ j∈range 512, budget (513+j) 358) < (2:ℕ)^1908 ∧
    (∑ j∈range 512, budget (513+j) 401) < (2:ℕ)^1952 := by decide +kernel

private theorem scale {K extra upper rate pop : ℕ} {pairs : Finset (ℕ × ℕ)}
    (width : K+1≤2^extra) (bound : (∑ j∈range 512, budget (513+j) extra)<2^upper)
    (exponents : rate+upper=2021) (den : 2^2021≤pop) (hits : ∀ z∈pairs, HitWithin K z) :
    2^rate*pairs.card<pop := by
  have h := Nat.mul_lt_mul_of_pos_left ((interval_count width hits).trans_lt bound) (Nat.two_pow_pos rate)
  rw [←pow_add,exponents] at h
  exact h.trans_le den

/-- The entire 256-bit tolerance has very small coverage, even if every
radix band can be checked at zero cost. -/
theorem fraction_256 {pairs : Finset (ℕ × ℕ)} {pop : ℕ} (den : 2^2021≤pop)
    (hits : ∀ z∈pairs, HitWithin (2^256) z) : 2^214*pairs.card<pop :=
  scale (by decide +kernel) wide_budgets.1 (by decide) den hits

/-- Population bound for the tolerance used in the constructed 2048-bit experiment. -/
theorem fraction_357 {pairs : Finset (ℕ × ℕ)} {pop : ℕ} (den : 2^2021≤pop)
    (hits : ∀ z∈pairs, HitWithin (2^357) z) : 2^113*pairs.card<pop :=
  scale (by decide +kernel) wide_budgets.2.1 (by decide) den hits

/-- Even a 400-bit tolerance leaves most target pairs outside every band. -/
theorem fraction_400 {pairs : Finset (ℕ × ℕ)} {pop : ℕ} (den : 2^2021≤pop)
    (hits : ∀ z∈pairs, HitWithin (2^400) z) : 2^69*pairs.card<pop :=
  scale (by decide +kernel) wide_budgets.2.2 (by decide) den hits

end PrimeFactors.CarryRemainderPairs
