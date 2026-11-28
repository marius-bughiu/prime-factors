import PrimeFactors.CircleMarkRationalTwoHoles

/-! For a specified prime, locate the last total list length before complete
coverage. The balanced rectangle at this length always lies in the exact
small-deficit regime; its omissions can therefore be read off from divisors. -/
namespace PrimeFactors.CircleMarkLastBalancedRectangle

open CircleMarkRationalCover CircleMarkRationalTwoHoles

def height (p : ℕ) := p.sqrt-1

def depth (p : ℕ) := if p<p.sqrt*(p.sqrt+1) then p.sqrt-1 else p.sqrt

def shortfall (p : ℕ) := p-(height p+1)*(depth p+1)

private theorem root_bounds {p : ℕ} [pr : Fact p.Prime] (large : 5≤p) :
    2≤p.sqrt ∧ p.sqrt<p ∧ p.sqrt^2<p ∧ p<p.sqrt*(p.sqrt+2) ∧
    p≠p.sqrt*(p.sqrt+1) := by
  let z := p.sqrt
  have low : z^2≤p := Nat.sqrt_le' _
  have high : p<(z+1)^2 := Nat.lt_succ_sqrt' _
  have two : 2≤z := by
    by_contra! small
    interval_cases z <;> norm_num at high <;> omega
  have short : z<p := by nlinarith only [low,two]
  have nd : ¬z∣p := fun dv => (pr.out.eq_one_or_self_of_dvd z dv).elim (by omega) (by omega)
  have square : z^2≠p := fun e => nd (e ▸ (show z∣z^2 by rw [pow_two]; exact dvd_mul_right ..))
  have edge (k : ℕ) : p≠z*(z+k) := fun e => nd (e ▸ dvd_mul_right ..)
  exact ⟨two,short,lt_of_le_of_ne low square,
    lt_of_le_of_ne (by nlinarith only [high]) (edge 2),edge 1⟩

/-- The two alternatives are the consecutive endpoint products z² and z(z+1).
Primality rules out z², z(z+1), and the highest possible endpoint remainder,
which would give the composite z(z+2). -/
theorem geometry {p : ℕ} [Fact p.Prime] (large : 5≤p) :
    0<height p ∧ height p≤depth p ∧ depth p≤height p+1 ∧
    0<shortfall p ∧ shortfall p≤height p ∧
    p=(height p+1)*(depth p+1)+shortfall p := by
  obtain ⟨two,_,low,high,ne⟩ := root_bounds large
  have add : p.sqrt-1+1=p.sqrt := by omega
  by_cases first : p<p.sqrt*(p.sqrt+1)
  · simp only [shortfall,height,depth,if_pos first,add]
    have a := Nat.sub_add_cancel (by nlinarith only [low] : p.sqrt*p.sqrt≤p)
    have b : p<p.sqrt*p.sqrt+p.sqrt := by nlinarith only [first]
    rw [pow_two] at low
    omega
  · simp only [shortfall,height,depth,if_neg first,add]
    have a := Nat.sub_add_cancel (by omega : p.sqrt*(p.sqrt+1)≤p)
    have b : p<p.sqrt*(p.sqrt+1)+p.sqrt := by nlinarith only [high]
    omega

/-- The shorter of the two balanced lists can gain one entry. This gives
universal coverage at total length height+depth+1. The order of the two
lists in the conclusion keeps their lengths nondecreasing. -/
theorem next_covers {p : ℕ} [Fact p.Prime] (large : 5≤p) :
    ∀ r : ZMod p, r≠0 → Represents r (depth p) (height p+1) := by
  obtain ⟨two,short,_,_,_⟩ := root_bounds large
  have add : p.sqrt-1+1=p.sqrt := by omega
  have next : p<(depth p+1)*(height p+1+1) := by
    by_cases first : p<p.sqrt*(p.sqrt+1)
    · simpa only [depth,height,if_pos first,add] using first
    · simpa only [depth,height,if_neg first,add,pow_two] using Nat.lt_succ_sqrt' p
  exact cover (by omega) (by simpa only [height,add] using short) next

/-- No arrangement of either list within the preceding total budget can
reach every nonzero root. -/
theorem budget_fails {p : ℕ} [Fact p.Prime] (large : 5≤p) :
    ¬ ∃ H D : ℕ, 0<H ∧ 0<D ∧ D<p ∧ H+D≤height p+depth p ∧
      ∀ r : ZMod p, r≠0 → Represents r H D := by
  obtain ⟨two,short,low,_,ne⟩ := root_bounds large
  obtain ⟨pos,order,balanced,_⟩ := geometry large
  have add : p.sqrt-1+1=p.sqrt := by omega
  have top : depth p≤p.sqrt := by unfold depth; split <;> omega
  have valid : (height p+depth p+1)/2<p := by omega
  rw [list_budget (by omega) valid]
  by_cases first : p<p.sqrt*(p.sqrt+1)
  · simp only [height,depth,if_pos first]
    rw [show p.sqrt-1+(p.sqrt-1)+2=2*p.sqrt by omega]
    nlinarith only [low]
  · simp only [height,depth,if_neg first]
    rw [show p.sqrt-1+p.sqrt+2=2*p.sqrt+1 by omega]
    have ge : p.sqrt*(p.sqrt+1)≤p := by omega
    nlinarith only [ge]

/-- Exactly one square class per divisor of the computed shortfall is missed
at the last balanced rectangle, for every prime at least five. -/
theorem last_missing {p : ℕ} [Fact p.Prime] (large : 5≤p) :
    (missingSquares p (height p) (depth p)).card=(shortfall p).divisors.card ∧
    ∀ a : ℤ, legendreSym p a=1 →
      (¬SquareHit p a (height p) (depth p) ↔ ∃ t∈(shortfall p).divisors,
        (a:ZMod p)=((height p+1:ℕ):ZMod p)^2/(t:ZMod p)^2) := by
  obtain ⟨_,order,_,pos,bound,eqn⟩ := geometry large
  exact ⟨(missing_counts pos bound (bound.trans order) eqn).2,
    fun _ sq => square_miss_iff sq pos bound (bound.trans order) eqn⟩

end PrimeFactors.CircleMarkLastBalancedRectangle
