import PrimeFactors.PrimeSignIsolation
import PrimeFactors.AffineNonsquareSign

/-! The affine sign isolates the smaller factor without a primality test
uniformly across the equal-width interval, once even numbers and squares
have been removed. -/
namespace PrimeFactors.NonsquareSignIsolation
open Finset

/-- A smaller-factor interval computable from N and the factor width h+1.
The last two inequalities mean c ≤ √N and c ≥ ceil(N/(2^(h+1)−1)). -/
noncomputable def candidates (N h : ℕ) : Finset ℕ := by
  classical
  exact (Ico (2^h) (2*2^h)).filter fun c =>
    Odd c ∧ ¬IsSquare c ∧ c^2≤N ∧ N≤c*(2*2^h-1)

/-- The preliminary checks use an interval comparison, parity, and the
integer square root. No primality test is involved. -/
theorem mem_candidates {c N h : ℕ} : c∈candidates N h ↔
    2^h≤c ∧ c<2*2^h ∧ c%2=1 ∧ c.sqrt^2≠c ∧ c^2≤N ∧ N≤c*(2*2^h-1) := by
  have square : IsSquare c ↔ c.sqrt^2=c := by
    constructor
    · rintro ⟨x,rfl⟩
      rw [Nat.sqrt_eq,pow_two]
    · intro eq
      exact ⟨c.sqrt,by simpa only [pow_two] using eq.symm⟩
  simp only [candidates,mem_filter,mem_Ico,Nat.odd_iff,square,and_assoc]

noncomputable def genuine (N h : ℕ) : Finset ℕ :=
  (candidates N h).filter fun c => c∣N

/-- If c shares a prime factor with pq, its bound by 2p forces equality
with p or q. The square-root cap permits q only when p=q. -/
theorem coprime_of_other {p q c : ℕ} (pp : p.Prime) (qp : q.Prime) (order : p≤q)
    (positive : 0<c) (short : c<2*p) (fit : c^2≤p*q) (other : c≠p) :
    c.Coprime (p*q) := by
  have pUnit := pp.coprime_iff_not_dvd.mpr (fun divides =>
    other (Nat.eq_of_dvd_of_lt_two_mul positive.ne' divides short))
  have qUnit : q.Coprime c := by
    apply qp.coprime_iff_not_dvd.mpr
    intro divides
    have eq := Nat.eq_of_dvd_of_lt_two_mul positive.ne' divides (show c<2*q by omega)
    have le : q≤p := by
      rw [eq,pow_two] at fit
      exact Nat.le_of_mul_le_mul_right fit qp.pos
    exact other (eq.trans (le_antisymm le order))
  exact pUnit.symm.mul_right qUnit.symm

theorem member_smaller {p q h : ℕ} (pp : p.Prime) (odd : Odd p)
    (ordered : p≤q) (low : 2^h≤p) (high : q<2*2^h) : p∈candidates (p*q) h := by
  classical
  apply mem_filter.mpr
  exact ⟨mem_Ico.mpr ⟨low,ordered.trans_lt high⟩,odd,pp.prime.not_isSquare,
    by rw [pow_two]; exact Nat.mul_le_mul_left _ ordered,
    Nat.mul_le_mul_left p (by omega)⟩

theorem other_unit {p q c h : ℕ} (pp : p.Prime) (qp : q.Prime) (order : p≤q)
    (low : 2^h≤p) (here : c∈candidates (p*q) h) (other : c≠p) :
    c.Coprime (p*q) := by
  obtain ⟨interval,_,_,fit,_⟩ := mem_filter.mp here
  obtain ⟨left,right⟩ := mem_Ico.mp interval
  have positive : 0<c := (pow_pos (by decide : 0<2) h).trans_le left
  exact coprime_of_other pp qp order positive (by omega) fit other

theorem genuine_eq {p q h : ℕ} (pp : p.Prime) (qp : q.Prime) (odd : Odd p)
    (order : p≤q) (low : 2^h≤p) (high : q<2*2^h) : genuine (p*q) h = {p} := by
  ext c
  rw [genuine,mem_filter,mem_singleton]
  constructor
  · rintro ⟨here,div⟩
    by_contra other
    have unit := (other_unit pp qp order low here other).gcd_eq_one
    rw [Nat.gcd_eq_left div] at unit
    exact (mem_filter.mp here).2.2.1 (unit ▸ IsSquare.one)
  · intro h
    subst c
    exact ⟨member_smaller pp odd order low high,dvd_mul_right p q⟩

/-- Dividing an odd candidate by two injects the width-(b+2) search space
into the interval [2^b,2^(b+1)), which has 2^b positions. -/
theorem card_le (N b : ℕ) : (candidates N (b+1)).card ≤ 2^b := by
  classical
  let C := candidates N (b+1)
  let f : ℕ → ℕ := fun c => c/2
  have region (c : ℕ) (hc : c∈C) : 2^b≤f c ∧ f c<2*2^b := by
    obtain ⟨left,right⟩ := mem_Ico.mp (mem_filter.mp hc).1
    rw [pow_succ] at left right
    dsimp [f]
    omega
  have injective : Set.InjOn f ↑C := by
    intro c hc d hd same
    obtain ⟨x,hx⟩ := (mem_filter.mp hc).2.1
    obtain ⟨y,hy⟩ := (mem_filter.mp hd).2.1
    dsimp [f] at same
    omega
  calc
    _ = (C.image f).card := (card_image_of_injOn injective).symm
    _ ≤ (Ico (2^b) (2*2^b)).card := card_le_card (by
      intro x hx
      obtain ⟨c,hc,rfl⟩ := mem_image.mp hx
      exact mem_Ico.mpr (region c hc))
    _ = 2^b := by rw [Nat.card_Ico]; omega

/-- Every exceptional ordered panel retains a false nonsquare candidate. The
definition uses only the product to describe which candidates are false. -/
noncomputable def exceptional (N h k : ℕ) : Finset (Fin k → ℕ) :=
  PrimeSignIsolation.bad (candidates N h \ genuine N h) (AffinePrimeSign.seeds N) k

theorem exceptional_subset (N h k : ℕ) :
    exceptional N h k ⊆ PrimeSignIsolation.panels (range N) k :=
  PrimeSignIsolation.bad_subset k fun _ _ _ hr => mem_range.mpr (AffinePrimeSign.mem_seeds.mp hr).1

/-- On valid panels, being outside the exceptional set is equivalent to
having just the smaller factor survive all sign checks. -/
theorem exact_iff {p q h k : ℕ} (pp : p.Prime) (qp : q.Prime) (odd : Odd p)
    (order : p≤q) (low : 2^h≤p) (high : q<2*2^h) {w : Fin k → ℕ}
    (valid : w∈PrimeSignIsolation.panels (range (p*q)) k) :
    PrimeSignIsolation.surviving (candidates (p*q) h) (AffinePrimeSign.seeds (p*q)) w = {p} ↔
      w∉exceptional (p*q) h k := by
  rw [exceptional,genuine_eq pp qp odd order low high]
  apply PrimeSignIsolation.exact_iff (singleton_subset_iff.mpr (member_smaller pp odd order low high)) _ valid
  intro c hc r hr
  rw [mem_singleton.mp hc]
  exact AffinePrimeSign.mem_seeds.mpr ⟨mem_range.mp hr,AffinePrimeSign.true_pass pp (dvd_mul_right p q) r⟩

/-- The halving premise is on false odd nonsquares in the physical interval,
independently of any primality check. -/
theorem count {p q b : ℕ} (pp : p.Prime) (qp : q.Prime) (order : p≤q)
    (low : 2^(b+1)≤p) (s : ℕ) :
    2^s*(exceptional (p*q) (b+1) (b+s)).card ≤ (p*q)^(b+s) := by
  apply PrimeSignIsolation.bit_margin
  · intro c hc
    obtain ⟨here,miss⟩ := mem_sdiff.mp hc
    obtain ⟨_,odd,ns,fit,_⟩ := mem_filter.mp here
    apply AffineNonsquareSign.false_bound odd ns (other_unit pp qp order low here ?_) fit
    intro eq
    exact miss (mem_filter.mpr ⟨here,eq ▸ dvd_mul_right p q⟩)
  · exact (card_le_card sdiff_subset).trans (card_le (p*q) b)

theorem fraction {p q b : ℕ} (pp : p.Prime) (qp : q.Prime) (order : p≤q)
    (low : 2^(b+1)≤p) (s : ℕ) :
    ((exceptional (p*q) (b+1) (b+s)).card:ℚ)/((p*q:ℕ):ℚ)^(b+s) ≤ 1/(2:ℚ)^s := by
  have pos : 0<p*q := Nat.mul_pos pp.pos qp.pos
  rw [div_le_div_iff₀ (by positivity) (by positivity),one_mul,mul_comm]
  exact_mod_cast count pp qp order low s

set_option maxRecDepth 8192 in
set_option exponentiation.threshold 2048 in
/-- Both 1024-bit factors may coincide. All eligibility and affine sign checks
use just the product and a proposed integer. This theorem counts the failures
of recognition when the ordered panel is drawn uniformly with replacement. -/
theorem full_size_1100 {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (order : p≤q) (low : 2^1023≤p) (high : q<2^1024) :
    (∀ w∈PrimeSignIsolation.panels (range (p*q)) 1100,
      PrimeSignIsolation.surviving (candidates (p*q) 1023) (AffinePrimeSign.seeds (p*q)) w = {p} ↔
      w∉exceptional (p*q) 1023 1100) ∧
    ((exceptional (p*q) 1023 1100).card:ℚ)/((p*q:ℕ):ℚ)^1100 ≤ 1/(2:ℚ)^78 := by
  have odd := pp.odd_of_ne_two (ne_of_gt ((by decide : 2<2^1023).trans_le low))
  have up : q<2*2^1023 := by
    rwa [show 2*2^1023=2^1024 by decide +kernel]
  exact ⟨fun _ valid => exact_iff (h:=1023) (k:=1100) pp qp odd order low up valid,
    fraction (b:=1022) pp qp order low 78⟩

end PrimeFactors.NonsquareSignIsolation
