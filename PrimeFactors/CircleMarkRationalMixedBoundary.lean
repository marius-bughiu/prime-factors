import PrimeFactors.CircleMarkRationalTargetCount
import PrimeFactors.CircleMarkRationalProduct

/-! At a fixed semiprime the smaller prime may be below the universal coverage
threshold while the larger prime is just above it. Only the larger prime then
contributes missing square residues to the exact negative-target frequency. -/
namespace PrimeFactors.CircleMarkRationalMixedBoundary

open Finset CircleMarkRationalFrequency CircleMarkRationalCover CircleMarkTargetFrequency
open private PrimeFactors.CircleMarkTargetFrequency.plus PrimeFactors.CircleMarkTargetFrequency.squares
  PrimeFactors.CircleMarkTargetFrequency.local_cards PrimeFactors.CircleMarkTargetFrequency.covered_sub
  from PrimeFactors.CircleMarkTargetFrequency
open private PrimeFactors.CircleMarkRationalTargetCount.menu_hit
  PrimeFactors.CircleMarkRationalTargetCount.side_bounds PrimeFactors.CircleMarkRationalTargetCount.contribution
  from PrimeFactors.CircleMarkRationalTargetCount

/-- When the grid's endpoint area exceeds the prime, every nonzero square
at that prime occurs among the public menu's reductions. -/
theorem full_count {n p H D : ℕ} [NeZero n] [Fact p.Prime] (dv : p∣n) (op : p≠2)
    (units : ∀ z∈rectangle H D, z.2.Coprime n) (dp : 0<D) (short : D<p)
    (area : p<(H+1)*(D+1)) : (covered p (menu n H D)).card=(p-1)/2 := by
  have eqn : covered p (menu n H D)=PrimeFactors.CircleMarkTargetFrequency.plus p := by
    apply Subset.antisymm (PrimeFactors.CircleMarkTargetFrequency.covered_sub ..)
    intro a mem
    obtain ⟨nz,hm⟩ := mem_erase.mp mem
    obtain ⟨r,root⟩ := (isSquare_iff_exists_sq _).mp (mem_filter.mp hm).2
    have rn : r≠0 := fun zero => nz (by simp [root,zero])
    apply (PrimeFactors.CircleMarkRationalTargetCount.menu_hit dv units nz).mpr
    apply (square_iff (r:=r) (by simpa only [Int.cast_natCast,ZMod.natCast_zmod_val] using root.symm) H D).mpr
    exact cover dp short area r rn
  rw [eqn,(PrimeFactors.CircleMarkTargetFrequency.local_cards p op).1]

/-- If the other prime is just above the boundary, the exact fraction missed is
`τ(s)/(q−1)` for a uniformly chosen negative-Jacobi target at this fixed product. -/
theorem coverage {p q H D s : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (op : p≠2) (short : D<p) (below : p<(H+1)*(D+1))
    (sp : 0<s) (sh : s≤H) (sd : s≤D) (above : q=(H+1)*(D+1)+s) :
    rate (p*q) (menu (p*q) H D)=1-(s.divisors.card:ℚ)/(q-1) := by
  obtain ⟨qs,oq⟩ := PrimeFactors.CircleMarkRationalTargetCount.side_bounds sp sh sd above
  have diff : p≠q := by omega
  have unitAt {r j : ℕ} [hr : Fact r.Prime] (lim : D<r) (m : j∈Icc 1 D) : j.Coprime r :=
    (hr.out.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (mem_Icc.mp m).1
      ((mem_Icc.mp m).2.trans_lt lim))).symm
  have units (z : ℕ×ℕ) (m : z∈rectangle H D) : z.2.Coprime (p*q) :=
    (unitAt short (mem_product.mp m).2).mul_right (unitAt qs (mem_product.mp m).2)
  have full := full_count (H:=H) (dvd_mul_right p q) op units (sp.trans_le sd) short below
  rw [rate_eq diff op oq,PrimeFactors.CircleMarkRationalTargetCount.contribution (e:=0) op (by simpa using full),
    PrimeFactors.CircleMarkRationalTargetCount.contribution oq
      (CircleMarkRationalTargetCount.local_count (dvd_mul_left q p) oq units sp sh sd above)]
  push_cast
  ring

private theorem divisor_test {q h s a t u : ℕ} [Fact q.Prime] (sp : 0<s) (sh : s≤h)
    (area : q=(h+1)*(h+1)+s) (fac : s=t*u) :
    (a:ZMod q)=((h+1:ℕ):ZMod q)^2/(t:ZMod q)^2 ↔ q∣a*t+u := by
  have tp : 0<t := by by_contra! z; simp [show t=0 by omega] at fac; omega
  have tl := (Nat.le_of_dvd sp (show t∣s from ⟨u,fac⟩)).trans sh
  have tq : t<q := by nlinarith only [area,tl,Nat.zero_le (h*h),sp]
  have nz : (t:ZMod q)≠0 := fun z => Nat.not_dvd_of_pos_of_lt tp tq ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp z)
  have sum : ((h+1:ℕ):ZMod q)^2+(t:ZMod q)*u=0 := by
    simpa only [fac,Nat.cast_add,Nat.cast_mul,Nat.cast_one,sq,ZMod.natCast_self] using
      (congrArg (fun x:ℕ => (x:ZMod q)) area.symm)
  rw [eq_div_iff (pow_ne_zero 2 nz),←ZMod.natCast_zmod_eq_zero_iff_dvd]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one] at sum ⊢
  constructor
  · intro eqn
    apply mul_right_cancel₀ nz
    rw [zero_mul]
    linear_combination eqn + sum
  · intro zero
    linear_combination (t:ZMod q)*zero - sum

/-- The exceptional squares for a square grid have an integer description
without modular division. A positive factor pair of the excess gives a miss
exactly when its weighted sum vanishes modulo the prime. -/
theorem square_miss_iff {q h s a : ℕ} [Fact q.Prime] (square : legendreSym q (a:ℤ)=1)
    (sp : 0<s) (sh : s≤h) (area : q=(h+1)*(h+1)+s) :
    ¬SquareHit q (a:ℤ) h h ↔ ∃ t u : ℕ, s=t*u ∧ q∣a*t+u := by
  rw [CircleMarkRationalTwoHoles.square_miss_iff square sp sh sh area]
  simp only [Int.cast_natCast]
  constructor
  · rintro ⟨t,tm,eqn⟩
    obtain ⟨u,fac⟩ := (Nat.mem_divisors.mp tm).1
    exact ⟨t,u,fac,(divisor_test sp sh area fac).mp eqn⟩
  · rintro ⟨t,u,fac,dv⟩
    exact ⟨t,Nat.mem_divisors.mpr ⟨⟨u,fac⟩,sp.ne'⟩,(divisor_test sp sh area fac).mpr dv⟩

/-- Every positive square target below this cutoff is guaranteed to be hit,
although the grid misses exactly one square residue for each divisor of `s`. -/
theorem small_target {q h s a : ℕ} [Fact q.Prime] (square : legendreSym q (a:ℤ)=1)
    (sp : 0<s) (sh : s≤h) (area : q=(h+1)*(h+1)+s) (ap : 0<a) (small : a*s+1<q) :
    SquareHit q (a:ℤ) h h := by
  by_contra miss
  obtain ⟨t,u,fac,dv⟩ := (square_miss_iff square sp sh area).mp miss
  have tp : 0<t := by by_contra! z; simp [show t=0 by omega] at fac; omega
  have up : 0<u := by by_contra! z; simp [show u=0 by omega] at fac; omega
  have lower := Nat.le_of_dvd (show 0<a*t+u by positivity) dv
  obtain ⟨x,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ap.ne'
  obtain ⟨y,rfl⟩ := Nat.exists_eq_succ_of_ne_zero tp.ne'
  obtain ⟨z,rfl⟩ := Nat.exists_eq_succ_of_ne_zero up.ne'
  nlinarith only [small,lower,fac,Nat.zero_le (x*y*z),Nat.zero_le (x*z),Nat.zero_le (y*z)]

private theorem factor_of_hit {p q h a : ℕ} [Fact p.Prime] [Fact q.Prime] (short : h<q)
    (hit : SquareHit p (a:ℤ) h h) (inert : legendreSym q (a:ℤ)= -1) :
    (CircleMarkRationalProduct.product a h h).gcd (p*q)=p := by
  obtain ⟨i,im,j,jm,mark⟩ := hit
  have dv := (CircleMarkRationalProduct.local_hit (p:=p) a h h).mpr ⟨j,jm,i,im,mark⟩
  rw [CircleMarkRationalProduct.gcd_eq ((legendreSym.eq_neg_one_iff q).mp inert) h short,if_pos dv]

/-- For a public negative-Jacobi target, the small-target bound makes the
batch gcd a proper factor in either sign orientation. -/
theorem small_gcd {p q h s a : ℕ} [Fact p.Prime] [Fact q.Prime]
    (short : h<p) (below : p<(h+1)*(h+1)) (sp : 0<s) (sh : s≤h)
    (above : q=(h+1)*(h+1)+s) (neg : jacobiSym (a:ℤ) (p*q)= -1) (ap : 0<a) (small : a*s+1<q) :
    (CircleMarkRationalProduct.product a h h).gcd (p*q)=p ∨
    (CircleMarkRationalProduct.product a h h).gcd (p*q)=q := by
  obtain ⟨qs,oq⟩ := PrimeFactors.CircleMarkRationalTargetCount.side_bounds sp sh sh above
  rcases CircleBranchCount.opposite neg with ⟨left,right⟩|⟨left,right⟩
  · have hp := (targets_iff (q:=q) (by omega : p≠q) oq (sp.trans_le sh) short).mpr below a neg left
    exact Or.inl (factor_of_hit qs hp right)
  · exact Or.inr (by simpa only [mul_comm q p] using factor_of_hit short (small_target right sp sh above ap small) left)

/-- Choosing a target at most the public grid side suffices whenever the
larger prime is in the small-deficit strip; the target may depend on N. -/
theorem side_target {p q h s a : ℕ} [Fact p.Prime] [Fact q.Prime]
    (short : h<p) (below : p<(h+1)*(h+1)) (sp : 0<s) (sh : s≤h)
    (above : q=(h+1)*(h+1)+s) (neg : jacobiSym (a:ℤ) (p*q)= -1) (ap : 0<a) (ah : a≤h) :
    (CircleMarkRationalProduct.product a h h).gcd (p*q)=p ∨
    (CircleMarkRationalProduct.product a h h).gcd (p*q)=q := by
  apply small_gcd short below sp sh above neg ap
  nlinarith only [Nat.mul_le_mul ah sh,above,sp]

/-- The square grid chosen by `floor(N^(1/4))` at 8,453 hits 4,056 of its
4,134 negative targets. The excess at 107 is seven. -/
theorem control : Nat.sqrt (Nat.sqrt 8453)=9 ∧ (targets 8453).card=4134 ∧
    (hits 8453 (menu 8453 9 9)).card=4056 ∧ rate 8453 (menu 8453 9 9)=52/53 := by
  letI : Fact (Nat.Prime 79) := ⟨by decide⟩
  letI : Fact (Nat.Prime 107) := ⟨by decide⟩
  have rate' := coverage (p:=79) (q:=107) (H:=9) (D:=9) (s:=7)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have total := (counts (p:=79) (q:=107) (by decide) (by decide) (by decide) (menu 8453 9 9)).1
  change (targets 8453).card=4134 at total
  have result : rate 8453 (menu 8453 9 9)=52/53 := by
    change rate (79*107) (menu (79*107) 9 9)=_
    rw [rate',show (7:ℕ).divisors.card=2 by decide]
    norm_num
  have rt : Nat.sqrt 8453=91 := (Nat.eq_sqrt.mpr (by decide)).symm
  refine ⟨by rw [rt]; exact (Nat.eq_sqrt.mpr (by decide)).symm,total,?_,result⟩
  rw [rate,total] at result
  exact_mod_cast (show ((hits 8453 (menu 8453 9 9)).card:ℚ)=4056 by linarith)

/-- At equality the cutoff can fail. At 41 times 53 the target 13 has
negative Jacobi symbol, and 13 times the deficit 4 plus 1 equals 53. -/
theorem cutoff_control : jacobiSym 13 2173= -1 ∧
    (CircleMarkRationalProduct.product 13 6 6).gcd 2173=1 := by
  letI : Fact (Nat.Prime 41) := ⟨by decide⟩
  letI : Fact (Nat.Prime 53) := ⟨by decide⟩
  have sq53 : legendreSym 53 (13:ℤ)=1 := by rw [jacobiSym.legendreSym.to_jacobiSym]; norm_num
  have ns41 : legendreSym 41 (13:ℤ)= -1 := by rw [jacobiSym.legendreSym.to_jacobiSym]; norm_num
  have miss : ¬SquareHit 53 (13:ℤ) 6 6 :=
    (square_miss_iff (a:=13) sq53 (by decide : 0<4) (by decide) (by decide)).mpr ⟨4,1,rfl,by decide⟩
  have absent : ¬53∣CircleMarkRationalProduct.product 13 6 6 := by
    intro dv
    obtain ⟨j,jm,i,im,mark⟩ := (CircleMarkRationalProduct.local_hit 13 6 6).mp dv
    exact miss ⟨i,im,j,jm,mark⟩
  refine ⟨by norm_num,?_⟩
  change (CircleMarkRationalProduct.product 13 6 6).gcd (53*41)=1
  rw [CircleMarkRationalProduct.gcd_eq ((legendreSym.eq_neg_one_iff 41).mp ns41) 6 (by decide),if_neg absent]

/-- Both rectangles use twelve list entries on the same semiprime. The 5×7
rectangle covers more targets with one fewer cell. Each rectangle has a
negative target for which it succeeds and the other fails. -/
theorem equal_budget : (targets 2491).card=1196 ∧
    (hits 2491 (menu 2491 6 6)).card=1127 ∧ (hits 2491 (menu 2491 5 7)).card=1150 ∧
    jacobiSym 13 2491= -1 ∧ jacobiSym 29 2491= -1 ∧
    (CircleMarkRationalProduct.product 13 6 6).gcd 2491=1 ∧ (CircleMarkRationalProduct.product 13 5 7).gcd 2491=53 ∧
    (CircleMarkRationalProduct.product 29 6 6).gcd 2491=53 ∧ (CircleMarkRationalProduct.product 29 5 7).gcd 2491=1 := by
  letI : Fact (Nat.Prime 47) := ⟨by decide⟩
  letI : Fact (Nat.Prime 53) := ⟨by decide⟩
  have total := (counts (p:=47) (q:=53) (by decide) (by decide) (by decide) (menu 2491 6 6)).1
  change (targets 2491).card=1196 at total
  have six := coverage (p:=47) (q:=53) (H:=6) (D:=6) (s:=4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have five := coverage (p:=47) (q:=53) (H:=5) (D:=7) (s:=5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [rate,total,show (4:ℕ).divisors.card=3 by decide] at six
  rw [rate,total,show (5:ℕ).divisors.card=2 by decide] at five
  refine ⟨total,?_,?_,by norm_num,by norm_num,?_⟩
  · exact_mod_cast (show ((hits 2491 (menu 2491 6 6)).card:ℚ)=1127 by linarith)
  · exact_mod_cast (show ((hits 2491 (menu 2491 5 7)).card:ℚ)=1150 by linarith)
  · decide +kernel

end PrimeFactors.CircleMarkRationalMixedBoundary
