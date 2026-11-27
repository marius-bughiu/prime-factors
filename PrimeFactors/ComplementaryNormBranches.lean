import PrimeFactors.ComplementaryKeys

/-! Six integral quadratic norms for complementary labels. Their homogeneous
form lets us compare a manufactured match with an ordinary quadratic gcd. -/
namespace PrimeFactors.ComplementaryNormBranches
open Finset TwelveResidueCollision TwelveImageSize

/-- The two conjugate signs of the chosen square root of three. -/
def norm {R : Type*} [CommRing R] (u v : R) : R := u^2-3*v^2

/-- Three conjugate pairs for one signed comparison. -/
def three {R : Type*} [CommRing R] (u v : R) : List R :=
  [norm u v, norm (u+3*v) (2*v), norm (u-3*v) (2*v)]

/-- The six integer forms, with the last three obtained by negating y. -/
def branches {R : Type*} [CommRing R] (x y : R) : List R :=
  three (x*y+3) (x-y) ++ three (3-x*y) (x+y)

private def cosForm {R : Type*} [CommRing R] (u v : R) : R :=
  u^6-45*u^4*v^2+135*u^2*v^4-27*v^6

private theorem triple_product {R : Type*} [CommRing R] (u v : R) :
    (three u v).prod=cosForm u v := by simp [three,norm,cosForm]; ring

/-- Exact factorization of the cleared rational-label equation. It holds
over any commutative ring, including the public composite residue ring. -/
theorem complement_product {R : Type*} [CommRing R] (x y : R) :
    (branches x y).prod=num x*den y+num y*den x-den x*den y := by
  rw [branches,List.prod_append,triple_product,triple_product]
  unfold cosForm num sextic den
  ring

/-- For either prime coordinate, a complement match is exactly the
vanishing of at least one norm, when both quotients are defined. -/
theorem complement_iff_norm {K : Type*} [Field K] {x y : K}
    (dx : den x≠0) (dy : den y≠0) : value y=1-value x ↔ (0:K)∈branches x y := by
  rw [←List.prod_eq_zero_iff,complement_product]
  unfold value
  field_simp [dx,dy]
  constructor <;> intro h <;> linear_combination h

/-- Homogeneous numerator of the initial norm, allowing composite moduli
without performing any division. -/
def initial {R : Type*} [CommRing R] (x a b : R) : R := norm (x*a+3*b) (x*b-a)

/-- Substituting the public candidate t for a square root of three in the
rotation merely rescales the original t²−3 test by a known square. -/
theorem forced_identity {R : Type*} [CommRing R] (x t : R) :
    initial x (t*x-3) (x+t)=(t^2-3)*(x^2+3)^2 := by
  unfold initial norm
  ring

/-- This covers both signs of the rotation and both shifted conjugate
pairs. With u+c*v = t*(k*v), the norm reduces to a scaled quadratic test. -/
theorem rescale {R : Type*} [CommRing R] {u v c k t : R} (atRoot : u+c*v=t*(k*v)) :
    norm (u+c*v) (k*v)=(t^2-3)*(k*v)^2 := by rw [norm,atRoot]; ring

/-- Equal gcds on actual integers, including negative seeds and t. -/
theorem forced_gcd (n : ℕ) (x t : ℤ) (unit : n.Coprime (x^2+3).natAbs) :
    n.gcd (initial x (t*x-3) (x+t)).natAbs=n.gcd (t^2-3).natAbs := by
  rw [forced_identity,Int.natAbs_mul,Int.natAbs_pow]
  rw [Nat.gcd_comm n, Nat.Coprime.gcd_mul_right_cancel _ (unit.pow_right 2).symm, Nat.gcd_comm]

/-- A signed norm in homogeneous coordinates y=a/b. To test the three other
forms, use -a in place of a. -/
def shifted {R : Type*} [CommRing R] (x a b c k : R) : R :=
  norm (x*a+3*b+c*(x*b-a)) (k*(x*b-a))

theorem normalization {R : Type*} [CommRing R] {x y a b : R} (h : y*b=a) (c k : R) :
    shifted x a b c k = b^2*norm (x*y+3+c*(x-y)) (k*(x-y)) := by
  rw [←h]
  unfold shifted norm
  ring

/-- Entire family of public root-guided choices, including rational root
approximations r/s. The appropriate signed branch is always the same direct
quadratic test times a square, even over a composite residue ring. -/
theorem forced_all {R : Type*} [CommRing R] (x r s c k : R) :
    shifted x ((k*r-c*s)*x-3*s) (s*x+(k*r-c*s)) c k =
      norm r s * (k*(x^2+3))^2 := by unfold shifted norm; ring

theorem forced_all_gcd (n : ℕ) (x r s c k : ℤ) (unit : n.Coprime (k*(x^2+3)).natAbs) :
    n.gcd (shifted x ((k*r-c*s)*x-3*s) (s*x+(k*r-c*s)) c k).natAbs =
      n.gcd (norm r s).natAbs := by
  rw [forced_all,Int.natAbs_mul,Int.natAbs_pow,Nat.gcd_comm n,
      Nat.Coprime.gcd_mul_right_cancel _ (unit.pow_right 2).symm,Nat.gcd_comm]

/-- Pell approximations with norm one produce a unit at every coprime
setup, however large the resulting seeds are. -/
theorem pell_miss (n : ℕ) (x r s c k : ℤ) (unit : n.Coprime (k*(x^2+3)).natAbs)
    (pell : r^2-3*s^2=1) :
    n.gcd (shifted x ((k*r-c*s)*x-3*s) (s*x+(k*r-c*s)) c k).natAbs=1 := by
  rw [forced_all_gcd _ _ _ _ _ _ unit,norm,pell]
  simp

private theorem norm_zero {u v : ℤ} (h : norm u v=0) : u=0 ∧ v=0 := by
  by_cases hv : v=0
  · subst v
    simp [norm] at h
    exact ⟨h,rfl⟩
  · have hq : (u:ℚ)^2=3*(v:ℚ)^2 := by
      exact_mod_cast (show u^2=3*v^2 by simpa [norm,sub_eq_zero] using h)
    have vq : (v:ℚ)≠0 := by exact_mod_cast hv
    have sq : IsSquare (3:ℚ) := ⟨(u:ℚ)/v,by field_simp [vq]; nlinarith only [hq]⟩
    have impossible := (Rat.isSquare_natCast_iff (n:=3)).mp sq
    exact ((by decide : ¬IsSquare (3:ℕ)) impossible).elim

private theorem all_nonzero (x y : ℤ) (v : ℤ) (hv : v ∈ three (x*y+3) (x-y)) : v≠0 := by
  simp only [three,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl <;> intro bad <;>
    obtain ⟨h1,h2⟩ := norm_zero bad <;>
    have xy : x=y := by omega
  all_goals subst y; nlinarith [sq_nonneg x]

theorem nonzero_branch (x y : ℤ) {z : ℤ} (h : z∈branches x y) : z≠0 := by
  rcases List.mem_append.mp h with h|h
  · exact all_nonzero _ _ _ h
  · apply all_nonzero x (-y) z
    simpa [mul_neg,sub_eq_add_neg,add_comm] using h

private theorem norm_size {u v D : ℤ} (hu : |u|≤D) (hv : 2*|v|≤D) :
    |norm u v|≤D^2 := by
  have d0 := (abs_nonneg u).trans hu
  have u0 := abs_nonneg u
  have v0 := abs_nonneg v
  have a := mul_self_le_mul_self u0 hu
  have b := mul_self_le_mul_self (by omega : 0≤2*|v|) hv
  rw [←sq, sq_abs] at a
  have sv : |v| * |v|=v^2 := by rw [←sq,sq_abs]
  apply abs_le.mpr
  constructor <;> unfold norm <;> nlinarith [sq_nonneg u,sq_nonneg v]

private theorem three_size (x y z : ℤ) (h : z∈three (x*y+3) (x-y)) :
    |z|≤((|x|+4)*(|y|+4))^2 := by
  let D := (|x|+4)*(|y|+4)
  have xy : |x*y+3|≤|x| * |y|+3 := by
    simpa [abs_mul] using abs_add_le (x*y) (3:ℤ)
  have d : |x-y|≤|x|+|y| := abs_sub _ _
  have d3 : |3*(x-y)|≤3*(|x|+|y|) := by rw [abs_mul]; norm_num; omega
  have pos : 0≤|x| * |y| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have both : 4*(|x|+|y|)≤D := by dsimp [D]; nlinarith
  have u : |x*y+3|≤D := by dsimp [D]; nlinarith [abs_nonneg x,abs_nonneg y]
  have plus : |x*y+3+3*(x-y)|≤D := by
    apply (abs_add_le _ _).trans
    dsimp [D]; nlinarith [abs_nonneg x,abs_nonneg y]
  have minus : |x*y+3-3*(x-y)|≤D := by
    apply (abs_sub _ _).trans
    dsimp [D]; nlinarith [abs_nonneg x,abs_nonneg y]
  have twice : 2*|2*(x-y)|≤D := by rw [abs_mul]; norm_num; omega
  simp only [three,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl
  · exact norm_size u (by have := abs_nonneg (x-y); omega)
  · exact norm_size plus twice
  · exact norm_size minus twice

/-- Integer representatives in a small rectangle cannot produce even one
complementary match modulo a prime exceeding this explicit bound. -/
theorem short_seed_exclusion {p : ℕ} (x y z : ℤ) (member : z∈branches x y)
    (large : ((|x|+4)*(|y|+4))^2 < (p:ℤ)) : ¬(p:ℤ)∣z := by
  have hz := nonzero_branch x y member
  have small : |z|≤((|x|+4)*(|y|+4))^2 := by
    rcases List.mem_append.mp member with h|h
    · exact three_size _ _ _ h
    · simpa using three_size x (-y) z (by simpa [mul_neg,sub_eq_add_neg,add_comm] using h)
  intro divisor
  have pos : 0 < |z| := abs_pos.mpr hz
  have divides : (p:ℤ)∣|z| := by rw [Int.abs_eq_natAbs]; exact Int.dvd_natAbs.mpr divisor
  exact (not_le_of_gt (small.trans_lt large)) (Int.le_of_dvd pos divides)

set_option maxRecDepth 4096 in
set_option exponentiation.threshold 1030 in
/-- In particular, taking two signed seeds of magnitude at most 2^255 can
never produce a complementary branch match at a 1024-bit prime. -/
theorem narrow_seeds {p : ℕ} (hp : 2^1023≤p) (x y z : ℤ) (member : z∈branches x y)
    (hx : |x|≤2^255) (hy : |y|≤2^255) : ¬(p:ℤ)∣z := by
  apply short_seed_exclusion x y z member
  have bound : (|x|+4)*(|y|+4)≤(2^255+4:ℤ)*(2^255+4) :=
    mul_le_mul (add_le_add_right hx 4) (add_le_add_right hy 4) (by positivity) (by positivity)
  have sqbound := mul_self_le_mul_self (by positivity : 0≤(|x|+4)*(|y|+4)) bound
  rw [←sq,←sq] at sqbound
  exact sqbound.trans_lt ((by norm_num : ((2^255+4:ℤ)*(2^255+4))^2<2^1023).trans_le
    (by exact_mod_cast hp))

abbrev Branch := Fin 2 × Fin 3

/-- The same six forms indexed by sign and one of the three shifts. -/
noncomputable def branchAt {R : Type*} [CommRing R] (x y : R) (i : Branch) : R :=
  let t := if i.1=0 then y else -y
  let c : R := if i.2=0 then 0 else if i.2=1 then 3 else -3
  let k : R := if i.2=0 then 1 else 2
  norm (x*t+3+c*(x-t)) (k*(x-t))

theorem member_at {R : Type*} [CommRing R] (x y z : R) :
    z∈branches x y ↔ ∃ i : Branch, branchAt x y i=z := by
  simp [branches,three,branchAt,Prod.exists,Fin.exists_fin_succ,sub_eq_add_neg,add_comm,eq_comm,or_assoc]

noncomputable def options {p : ℕ} [Fact p.Prime] (x : ZMod p) :=
  (regulars p).filter (fun y => value y=1-value x)

private noncomputable def fiber {p : ℕ} [Fact p.Prime] (x : ZMod p) (i : Branch) :=
  (options x).filter (fun y => branchAt x y i=0)

private theorem nonpole {p : ℕ} [Fact p.Prime] {x : ZMod p} (rx : x∈regulars p) :
    x^2+3≠0 := by
  intro zero
  apply (Finset.mem_filter.mp rx).2
  simp [mask,zero]

private theorem fiber_bound {p : ℕ} [Fact p.Prime] {x : ZMod p} (rx : x∈regulars p) (i : Branch) :
    (fiber x i).card≤2 := by
  classical
  let poly : Polynomial (ZMod p) := branchAt (Polynomial.C x) Polynomial.X i
  have eval (y : ZMod p) : poly.eval y=branchAt x y i := by
    by_cases a : i.1=0 <;> by_cases b : i.2=0 <;> by_cases c : i.2=1 <;>
      simp [poly,branchAt,norm,a,b,c]
  have nonzero : poly≠0 := by
    intro h
    let y := if i.1=0 then x else -x
    have e := eval y
    rw [h,Polynomial.eval_zero] at e
    have d := nonpole rx
    by_cases sig : i.1=0 <;> simp [branchAt,norm,y,sig,←sq] at e <;> exact (pow_ne_zero 2 d) e.symm
  have deg : poly.natDegree≤2 := by
    dsimp only [poly,branchAt,norm]
    split_ifs <;> compute_degree
  by_contra! over
  exact nonzero (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' poly
    (fiber x i) (fun y hy => (eval y).trans (Finset.mem_filter.mp hy).2) (deg.trans_lt over))

/-- Partners whose complementary matches can be explained by a common norm
branch at both primes. Outside this set a vanishing norm at p cannot vanish
at q, so the gcd of that individual norm splits the product. -/
noncomputable def sameBranch {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (x : ZMod p) (u : ZMod q) :=
  Finset.univ.biUnion (fun i : Branch => (fiber x i) ×ˢ (fiber u i))

theorem same_branch_bound {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {x : ZMod p} {u : ZMod q} (rx : x∈regulars p) (ru : u∈regulars q) :
    (sameBranch x u).card≤24 := by
  classical
  have h (i : Branch) : ((fiber x i) ×ˢ (fiber u i)).card ≤ 4 := by
    rw [Finset.card_product]
    exact Nat.mul_le_mul (fiber_bound rx i) (fiber_bound ru i)
  apply (Finset.card_biUnion_le_card_mul _ _ 4 (fun i _ => h i)).trans
  simp [Fintype.card_prod]

/-- Every counted separating partner has a specific one-sided zero among
the six checked integer forms. -/
theorem separating_index {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {x y : ZMod p} {u v : ZMod q} (rx : x∈regulars p)
    (hit : (y,v)∈(options x) ×ˢ (options u) \ sameBranch x u) :
    ∃ i : Branch, branchAt x y i=0 ∧ branchAt u v i≠0 := by
  classical
  obtain ⟨both,different⟩ := mem_sdiff.mp hit
  obtain ⟨first,second⟩ := mem_product.mp both
  obtain ⟨ry,key⟩ := mem_filter.mp first
  have dx : den x≠0 := pow_ne_zero _ (nonpole rx)
  have dy : den y≠0 := pow_ne_zero _ (nonpole ry)
  obtain ⟨i,zero⟩ := (member_at x y 0).mp ((complement_iff_norm dx dy).mp key)
  refine ⟨i,zero,?_⟩
  intro same
  exact different (mem_biUnion.mpr ⟨i,mem_univ _,
    mem_product.mpr ⟨mem_filter.mpr ⟨first,zero⟩,mem_filter.mpr ⟨second,same⟩⟩⟩)

private theorem partition {p : ℕ} [Fact p.Prime] (hp : 864<p)
    {x : ZMod p} (rx : x∈regulars p) (sp : IsSquare (3:ZMod p)) :
    (∀ i, (fiber x i).card=2) ∧ (univ : Finset Branch).toSet.PairwiseDisjoint (fiber x) := by
  classical
  let S : Finset ((i : Branch) × ZMod p) := univ.sigma (fiber x)
  have all : S.image Sigma.snd=options x := by
    ext y
    constructor
    · intro hy
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hy
      exact (mem_filter.mp (mem_sigma.mp ha).2).1
    · intro hy
      obtain ⟨ry,hit⟩ := mem_filter.mp hy
      have dx : den x≠0 := pow_ne_zero _ (nonpole rx)
      have dy : den y≠0 := pow_ne_zero _ (nonpole ry)
      obtain ⟨i,zero⟩ := (member_at x y 0).mp ((complement_iff_norm dx dy).mp hit)
      exact mem_image.mpr ⟨⟨i,y⟩,mem_sigma.mpr ⟨mem_univ _,mem_filter.mpr ⟨hy,zero⟩⟩,rfl⟩
  have count : (options x).card=12 := by
    simpa [options,sp] using ComplementaryKeys.complement_count hp rx
  have upper : S.card≤12 := by
    rw [card_sigma]
    exact (sum_le_sum (fun i _ => fiber_bound rx i)).trans_eq (by simp [Fintype.card_prod])
  have equal : (S.image Sigma.snd).card = S.card := by
    apply le_antisymm card_image_le
    simpa [all,count] using upper
  have size : S.card=12 := by rw [←equal,all,count]
  constructor
  · intro i
    apply (fiber_bound rx i).antisymm
    by_contra! short
    have impossible := sum_lt_sum (s:=(univ : Finset Branch)) (fun j _ => fiber_bound rx j)
      ⟨i,mem_univ _,short⟩
    rw [card_sigma] at size
    simp [size,Fintype.card_prod] at impossible
  · intro i _ j _ different
    apply disjoint_left.mpr
    intro y hi hj
    have inj : Set.InjOn (fun a : (k : Branch) × ZMod p => a.2) S := card_image_iff.mp equal
    have a : (⟨i,y⟩ : (k : Branch) × ZMod p)∈S := mem_sigma.mpr ⟨mem_univ _,hi⟩
    have b : (⟨j,y⟩ : (k : Branch) × ZMod p)∈S := mem_sigma.mpr ⟨mem_univ _,hj⟩
    have eq := inj a b rfl
    exact different (congrArg Sigma.fst eq)

/-- Exactly 120 of the 144 globally complementary partners give at least
one one-sided norm zero. The other 24 have the same unique branch at both
primes. CRT identifies these pairs with distinct public residues. -/
theorem one_twenty_partners {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp : 864<p) (hq : 864<q)
    {x : ZMod p} {u : ZMod q} (rx : x∈regulars p) (ru : u∈regulars q)
    (sp : IsSquare (3:ZMod p)) (sq : IsSquare (3:ZMod q)) :
    (sameBranch x u).card=24 ∧ ((options x) ×ˢ (options u) \ sameBranch x u).card=120 := by
  classical
  obtain ⟨sizeP,disP⟩ := partition hp rx sp
  obtain ⟨sizeQ,_⟩ := partition hq ru sq
  have dis : (univ : Finset Branch).toSet.PairwiseDisjoint
      (fun i => (fiber x i) ×ˢ (fiber u i)) := by
    intro i hi j hj different
    apply disjoint_left.mpr
    intro y h1 h2
    exact (disjoint_left.mp (disP hi hj different)) (mem_product.mp h1).1 (mem_product.mp h2).1
  have same : (sameBranch x u).card=24 := by
    rw [sameBranch,card_biUnion dis]
    simp [card_product,sizeP,sizeQ,Fintype.card_prod]
  have sub : sameBranch x u ⊆ (options x) ×ˢ (options u) := by
    intro y hy
    obtain ⟨i,_,both⟩ := mem_biUnion.mp hy
    exact mem_product.mpr ⟨(mem_filter.mp (mem_product.mp both).1).1,
      (mem_filter.mp (mem_product.mp both).2).1⟩
  have px : (options x).card=12 := by simpa [options,sp] using ComplementaryKeys.complement_count hp rx
  have qu : (options u).card=12 := by simpa [options,sq] using ComplementaryKeys.complement_count hq ru
  exact ⟨same,by rw [card_sdiff sub,card_product,px,qu,same]⟩

/-- A global complement tie whose unfactored comparisons miss both primes.
The signed norm refinement separates them. -/
theorem shared_complement_witness :
    let n := 1040279
    let x : ℤ := 4
    let y : ℤ := 11
    n.gcd (mask x*mask y).natAbs=1 ∧
    (1001365*den x-num x)%n=0 ∧ (38915*den y-num y)%n=0 ∧
    n.gcd (1001365-38915)=1 ∧ n.gcd (1001365+38915-1)=n ∧
    (branches x y).map (fun z => n.gcd z.natAbs)=[1031,1,1009,1,1,1] ∧
    1009*1031=n ∧ Nat.Prime 1009 ∧ Nat.Prime 1031 := by decide +kernel

end PrimeFactors.ComplementaryNormBranches
