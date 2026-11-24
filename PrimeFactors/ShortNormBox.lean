import PrimeFactors.NormOrbit
import Mathlib.Tactic.IntervalCases
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

namespace PrimeFactors.ShortNormBox

private theorem sq_mod_two (x : ℤ) : x^2%2=x%2 := by
  have lo := Int.emod_nonneg x (by decide : (2:ℤ)≠0)
  have hi := Int.emod_lt_of_pos x (by decide : (0:ℤ)<2)
  rw [pow_two, Int.mul_emod]
  interval_cases x%2 <;> decide

private theorem odd_sq_mod_eight {x : ℤ} (odd : x%2=1) : x^2%8=1 := by
  have lo := Int.emod_nonneg x (by decide : (8:ℤ)≠0)
  have hi := Int.emod_lt_of_pos x (by decide : (0:ℤ)<8)
  rw [pow_two, Int.mul_emod]
  interval_cases h : x%8 <;> norm_num at * <;> omega

private theorem twice_square (x : ℤ) : (2*x^2)%8 = if x%2=0 then 0 else 2 := by
  have lo := Int.emod_nonneg x (by decide : (8:ℤ)≠0)
  have hi := Int.emod_lt_of_pos x (by decide : (0:ℤ)<8)
  rw [Int.mul_emod, pow_two, Int.mul_emod x x]
  split <;> interval_cases h : x%8 <;> norm_num at * <;> omega

/-- The sum of two positive squares in the local box is exactly the prime.
The odd coordinate can always be put first. -/
theorem gaussian {p u v : ℤ} (hp : 0<p) (odd : p%2=1) (u0 : 0<u) (v0 : 0<v)
    (u2 : u^2<p) (v2 : v^2<p) (div : p∣u^2+v^2) :
    u^2+v^2=p ∧ ((u%2=1 ∧ v%2=0) ∨ (v%2=1 ∧ u%2=0)) := by
  obtain ⟨k, hk⟩ := div
  have hpos : 0<p*k := hk ▸ (by positivity)
  have hlow := pos_of_mul_pos_right hpos hp.le
  have hhigh : p*k<p*2 := by linarith
  have kl := (mul_lt_mul_left hp).mp hhigh
  have ke : k=1 := by omega
  rw [ke,mul_one] at hk
  have residues := congrArg (fun x : ℤ => x%2) hk
  change (u^2+v^2)%2=p%2 at residues
  rw [Int.add_emod, sq_mod_two, sq_mod_two, odd] at residues
  exact ⟨hk, by omega⟩

/-- A positive multiple in the second box is p or 2p. In the latter case
switch coordinates and halve the even one to represent p itself. -/
theorem positive_two {p u v : ℤ} (hp : 0<p) (u0 : 0<u) (v0 : 0<v)
    (u2 : u^2<p) (v2 : v^2<p) (div : p∣u^2+2*v^2) :
    ∃ t a : ℤ, 0<t ∧ 0<a ∧ p=t^2+2*a^2 ∧
      ((t=u ∧ a=v) ∨ (t=v ∧ 2*a=u)) := by
  obtain ⟨k, hk⟩ := div
  have hpos : 0<p*k := hk ▸ (by positivity)
  have low := pos_of_mul_pos_right hpos hp.le
  have hi : p*k<p*3 := by linarith
  have high := (mul_lt_mul_left hp).mp hi
  obtain he | he : k=1 ∨ k=2 := by omega
  · exact ⟨u,v,u0,v0,by simpa [he] using hk.symm,Or.inl ⟨rfl,rfl⟩⟩
  · rw [he] at hk
    have ur := sq_mod_two u
    have even : u%2=0 := by omega
    have d := Int.dvd_of_emod_eq_zero even
    obtain ⟨a,ha⟩ := d
    exact ⟨v,a,v0,by omega,by rw [ha] at hk; nlinarith,Or.inr ⟨rfl,ha.symm⟩⟩

/-- The indefinite local-box multiple is necessarily -p. -/
theorem negative_two {p u v : ℤ} (hp : 0<p) (u2 : u^2<p) (v2 : v^2<p)
    (nz : u^2≠2*v^2) (div : p∣u^2-2*v^2) : u^2-2*v^2 = -p := by
  obtain ⟨k,hk⟩ := div
  have hlow : p*(-2)<p*k := by nlinarith [sq_nonneg u]
  have hhigh : p*k<p*1 := by nlinarith [sq_nonneg v]
  have lo := (mul_lt_mul_left hp).mp hlow
  have hi := (mul_lt_mul_left hp).mp hhigh
  have kn : k≠0 := by intro z; rw [z,mul_zero] at hk; omega
  have ke : k= -1 := by omega
  simpa [ke] using hk

/-- The odd baby coordinate works in both forms. The smaller prime's
residue class also fixes the parity of the second coordinate. -/
theorem coordinate_parity {p t a : ℤ} (hp : p%2=1) :
    (p=t^2+2*a^2 → t%2=1 ∧ (p%8=3 → a%2=1)) ∧
    (p=2*a^2-t^2 → t%2=1 ∧ (p%8=7 → a%2=0)) := by
  have ts := sq_mod_two t
  have ay := twice_square a
  constructor <;> intro e
  · have tOdd : t%2=1 := by omega
    have t8 := odd_sq_mod_eight tOdd
    exact ⟨tOdd, by intro h; split at ay <;> omega⟩
  · have tOdd : t%2=1 := by omega
    have t8 := odd_sq_mod_eight tOdd
    exact ⟨tOdd, by intro h; split at ay <;> omega⟩

private theorem short_hit {p : ℕ} [Fact p.Prime] (b : ℤ)
    (nonzero : (b : ZMod p)≠0) (square : IsSquare (b : ZMod p)) :
    ∃ u v : ℤ, 0<u ∧ 0<v ∧ u^2<p ∧ v^2<p ∧ (p:ℤ)∣u^2-b*v^2 := by
  have pp : p.Prime := Fact.out
  have sz : p.sqrt^2<p := lt_of_le_of_ne (Nat.sqrt_le' _) (fun h =>
    pp.prime.not_isSquare ⟨p.sqrt, by simpa only [pow_two] using h.symm⟩)
  have castSz : (p.sqrt:ℤ)^2<p := by exact_mod_cast sz
  obtain ⟨r, hr⟩ := square
  have rn : r ≠ 0 := by intro eq; simp [eq] at hr; exact nonzero hr
  have rz : ((r.val:ℤ) : ZMod p)=r := by simp
  have ru : IsUnit ((r.val:ℤ) : ZMod p) := by rw [rz]; exact isUnit_iff_ne_zero.mpr rn
  have root : (((r.val:ℤ) : ZMod p))^2 = -((-b:ℤ) : ZMod p) := by
    rw [rz,Int.cast_neg,neg_neg,hr,pow_two]
  obtain ⟨a,t,apos,al,tn,tl,cong⟩ := NormOrbit.local_box (-b) (r.val:ℤ)
    (Nat.sqrt_pos.mpr pp.pos) (Nat.sqrt_lt_self pp.one_lt) (Nat.lt_succ_sqrt' p) ru root
  have az : (a:ℤ) ≤ p.sqrt := by exact_mod_cast al
  refine ⟨|t|,a,abs_pos.mpr tn,by exact_mod_cast (show 0<a by omega),
    (pow_le_pow_left₀ (abs_nonneg t) tl 2).trans_lt castSz,
    (pow_le_pow_left₀ (Int.natCast_nonneg _) az 2).trans_lt castSz,?_⟩
  rw [sq_abs, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  simpa [sub_eq_add_neg] using cong

/-- Every odd prime itself occurs in a parity-restricted box at its square
root. This theorem takes no supplied local square root or coordinates. -/
theorem prime_representation {p : ℕ} [Fact p.Prime] (odd : p ≠ 2) :
    ∃ t a : ℤ, 0<t ∧ 0<a ∧ t^2<p ∧ a^2<p ∧ t%2=1 ∧
      ((a%2=0 ∧ (p:ℤ)=t^2+a^2) ∨
       (a%2=1 ∧ (p:ℤ)=t^2+2*a^2) ∨
       (a%2=0 ∧ (p:ℤ)=2*a^2-t^2)) := by
  have pp : p.Prime := Fact.out
  have parity := Nat.Prime.mod_two_eq_one_iff_ne_two.mpr odd
  have po : (p:ℤ)%2=1 := by exact_mod_cast parity
  have hp : 0<(p:ℤ) := by exact_mod_cast pp.pos
  have two : (2 : ZMod p)≠0 := by exact_mod_cast ZMod.prime_ne_zero p 2 odd
  by_cases mod4 : p%4≠3
  · obtain ⟨u,v,hu,hv,u2,v2,div⟩ := short_hit (p := p) (-1)
      (by rw [Int.cast_neg,Int.cast_one]; exact neg_ne_zero.mpr one_ne_zero)
      (by rw [Int.cast_neg,Int.cast_one]; exact ZMod.exists_sq_eq_neg_one_iff.mpr mod4)
    have g := gaussian hp po hu hv u2 v2 (by simpa using div)
    rcases g.2 with uv | vu
    · exact ⟨u,v,hu,hv,u2,v2,uv.1,Or.inl ⟨uv.2,g.1.symm⟩⟩
    · exact ⟨v,u,hv,hu,v2,u2,vu.1,Or.inl ⟨vu.2,by linarith [g.1]⟩⟩
  by_cases mod8 : p%8=3
  · obtain ⟨u,v,hu,hv,u2,v2,div⟩ := short_hit (p := p) (-2) (by simpa using (neg_ne_zero.mpr two))
      (by simpa using (ZMod.exists_sq_eq_neg_two_iff odd).mpr (Or.inr mod8))
    obtain ⟨t,a,ht,ha,eq,which⟩ := positive_two hp hu hv u2 v2 (by simpa using div)
    obtain ⟨to',ao⟩ := (coordinate_parity po).1 eq
    have modZ : (p:ℤ)%8=3 := by exact_mod_cast mod8
    exact ⟨t,a,ht,ha,by nlinarith [sq_pos_of_pos ha],by nlinarith [sq_pos_of_pos ht],
      to',Or.inr (Or.inl ⟨ao modZ,eq⟩)⟩
  · have seven : p%8=7 := by omega
    obtain ⟨t,a,ht,ha,t2,a2,div⟩ := short_hit (p := p) 2 (by simpa using two)
      (by simpa using (ZMod.exists_sq_eq_two_iff odd).mpr (Or.inr seven))
    have nz : t^2≠2*a^2 := by
      intro eq
      have abseq := congrArg Int.natAbs eq
      apply NormOrbit.unequal_squares (u := t.natAbs) (v := a.natAbs)
        (Int.natAbs_pos.mpr ha.ne')
      simpa [Int.natAbs_pow,Int.natAbs_mul] using abseq
    have norm := negative_two hp t2 a2 nz div
    have eq : (p:ℤ)=2*a^2-t^2 := by omega
    obtain ⟨to',ae⟩ := (coordinate_parity po).2 eq
    have modZ : (p:ℤ)%8=7 := by exact_mod_cast seven
    exact ⟨t,a,ht,ha,t2,a2,to',Or.inr (Or.inr ⟨ae modZ,eq⟩)⟩

end PrimeFactors.ShortNormBox
