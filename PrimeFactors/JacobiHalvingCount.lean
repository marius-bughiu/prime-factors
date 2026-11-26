import PrimeFactors.JacobiSeparation

/-! Finite cyclic-group count for Leander's Jacobi-negative choice of a base
(arXiv:quant-ph/0208183, Theorem 4). Indices a,b below denote valuations minus one. -/
namespace PrimeFactors.JacobiHalvingCount
open Finset

variable {G H : Type*} [Group G] [Fintype G] [DecidableEq G]
  [Group H] [Fintype H] [DecidableEq H]

/-- The elements whose odd-cofactor power has order exactly 2^(i+1). -/
noncomputable def layer (G : Type*) [Group G] [Fintype G] [DecidableEq G] (u i : ℕ) : Finset G :=
  univ.filter fun x => x^(u*2^(i+1))=1 ∧ x^(u*2^i)≠1

theorem mem_layer {x : G} {u i : ℕ} : x∈layer G u i ↔ orderOf (x^u)=2^(i+1) := by
  simp only [layer,mem_filter,mem_univ,true_and,pow_mul,ne_eq,←orderOf_dvd_iff_pow_eq_one]
  constructor
  · rintro ⟨hi,lo⟩
    obtain ⟨j,le,eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hi
    rw [eq,Nat.pow_dvd_pow_iff_le_right (by decide : 1<(2:ℕ))] at lo
    exact eq.trans (by congr 1; omega)
  · rintro eq
    rw [eq]
    exact ⟨dvd_rfl,by simp [Nat.pow_dvd_pow_iff_le_right (by decide : 1<(2:ℕ))]⟩

private theorem kernel_count [IsCyclic G] {e : ℕ} (pos : 0<e) (divides : e∣Fintype.card G) :
    (univ.filter fun x : G => x^e=1).card=e := by
  rw [←sum_card_orderOf_eq_card_pow_eq_one pos.ne']
  calc
    _ = ∑ d ∈ e.divisors, d.totient := sum_congr rfl fun d hd =>
      IsCyclic.card_orderOf_eq_totient ((Nat.dvd_of_mem_divisors hd).trans divides)
    _ = _ := Nat.sum_totient _

theorem layer_count [IsCyclic G] {u a i : ℕ} (size : Fintype.card G=u*2^(a+1))
    (up : 0<u) (ia : i≤a) : (layer G u i).card=u*2^i := by
  let K (j : ℕ) := univ.filter (fun x : G => x^(u*2^j)=1)
  have bound {j} (hj : j≤a+1) : (K j).card=u*2^j :=
    kernel_count (by positivity) (size ▸ Nat.mul_dvd_mul_left u (pow_dvd_pow _ hj))
  have diff : layer G u i = K (i+1) \ K i := by ext; simp [layer,K]
  have sub : K i ⊆ K (i+1) := by
    intro x hx
    have eq := (mem_filter.mp hx).2
    apply mem_filter.mpr
    exact ⟨mem_univ _, by simp only [pow_succ,←mul_assoc,pow_mul,eq,one_pow,mul_one]⟩
  have both := card_sdiff_add_card_eq_card sub
  rw [←diff,bound (by omega),bound (by omega),pow_succ,←mul_assoc] at both
  omega

/-- Opposite local quadratic characters: a full 2-primary order at exactly
one prime. The two rectangles are disjoint. -/
noncomputable def opposite (A : Finset G) (B : Finset H) : Finset (G×H) :=
  (A ×ˢ (univ\B)) ∪ ((univ\A) ×ˢ B)

omit [Group G] [Group H] in
private theorem mem_opposite {A : Finset G} {B : Finset H} {x : G×H} :
    x∈opposite A B ↔ (x.1∈A ∧ x.2∉B) ∨ (x.1∉A ∧ x.2∈B) := by simp [opposite]

theorem opposite_card {a b u v : ℕ} [IsCyclic G] [IsCyclic H]
    (sizeG : Fintype.card G=u*2^(a+1)) (sizeH : Fintype.card H=v*2^(b+1))
    (up : 0<u) (vp : 0<v) :
    (opposite (layer G u a) (layer H v b)).card=2*(u*2^a)*(v*2^b) := by
  let A := layer G u a
  let B := layer H v b
  have ac : A.card=u*2^a := layer_count sizeG up le_rfl
  have bc : B.card=v*2^b := layer_count sizeH vp le_rfl
  have disj : Disjoint (A ×ˢ (univ\B)) ((univ\A) ×ˢ B) := by
    apply disjoint_left.mpr
    intro z left right
    exact (mem_sdiff.mp (mem_product.mp right).1).2 (mem_product.mp left).1
  have ca := card_sdiff_add_card_eq_card (subset_univ A)
  have cb := card_sdiff_add_card_eq_card (subset_univ B)
  rw [card_univ,sizeG,pow_succ,←mul_assoc,ac] at ca
  rw [card_univ,sizeH,pow_succ,←mul_assoc,bc] at cb
  change (opposite A B).card=_
  rw [opposite,card_union_of_disjoint disj,card_product,card_product,ac,bc,
    show (univ\A).card=u*2^a by omega,show (univ\B).card=v*2^b by omega]
  ring

/-- Equal 2-primary orders persist at every link of the halving chain. -/
noncomputable def failures (G H : Type*) [Group G] [Fintype G] [DecidableEq G]
    [Group H] [Fintype H] [DecidableEq H] (u v a b : ℕ) : Finset (G×H) :=
  (opposite (layer G u a) (layer H v b)).filter (fun z => orderOf (z.1^u)=orderOf (z.2^v))

omit [DecidableEq G] in
private theorem primary_bound {u a : ℕ} (size : Fintype.card G=u*2^(a+1)) (x : G) :
    orderOf (x^u)∣2^(a+1) := by
  apply orderOf_dvd_of_pow_eq_one
  rw [←pow_mul,←size,pow_card_eq_one]

theorem failures_equal (u v a : ℕ) : failures G H u v a a=∅ := by
  ext z
  simp only [Finset.not_mem_empty,iff_false]
  intro hz
  obtain ⟨opp,same⟩ := mem_filter.mp hz
  rcases mem_opposite.mp opp with ⟨left,right⟩|⟨left,right⟩
  · exact right (mem_layer.mpr (same.symm.trans (mem_layer.mp left)))
  · exact left (mem_layer.mpr (same.trans (mem_layer.mp right)))

/-- The only exceptional rectangle when the right valuation is larger. -/
theorem failures_rect {u v a b : ℕ} (sizeG : Fintype.card G=u*2^(a+1)) (lt : a<b) :
    failures G H u v a b=layer G u a ×ˢ layer H v a := by
  have ne : (2:ℕ)^(a+1)≠2^(b+1) := (Nat.pow_lt_pow_right (by decide) (by omega)).ne
  ext z
  constructor
  · intro hz
    obtain ⟨opp,same⟩ := mem_filter.mp hz
    rcases mem_opposite.mp opp with ⟨left,_⟩|⟨_,right⟩
    · exact mem_product.mpr ⟨left,mem_layer.mpr (same.symm.trans (mem_layer.mp left))⟩
    · have dv := primary_bound sizeG z.1
      rw [same,mem_layer.mp right,Nat.pow_dvd_pow_iff_le_right (by decide : 1<(2:ℕ))] at dv
      omega
  · intro hz
    obtain ⟨left,right⟩ := mem_product.mp hz
    apply mem_filter.mpr
    refine ⟨mem_opposite.mpr (Or.inl ⟨left,fun h => ne ((mem_layer.mp right).symm.trans (mem_layer.mp h))⟩),
      (mem_layer.mp left).trans (mem_layer.mp right).symm⟩

/-- Positive actual valuations are a+1 and b+1. For b>a the failure fraction
is exactly one in 2^(b-a+1), at most one in four. -/
theorem exact_fraction {u v a b : ℕ} [IsCyclic G] [IsCyclic H]
    (sizeG : Fintype.card G=u*2^(a+1)) (sizeH : Fintype.card H=v*2^(b+1))
    (up : 0<u) (vp : 0<v) (lt : a<b) :
    2^(b-a+1)*(failures G H u v a b).card = (opposite (layer G u a) (layer H v b)).card := by
  rw [failures_rect sizeG lt,card_product,layer_count sizeG up le_rfl,layer_count sizeH vp lt.le,
    opposite_card sizeG sizeH up vp,show b-a+1=(b-a)+1 by rfl,pow_succ,
    show (2:ℕ)^b = 2^(b-a)*2^a by rw [←pow_add,Nat.sub_add_cancel lt.le]]
  ring

omit [DecidableEq G] in
private theorem odd_power_same {x : G} {d t : ℕ} (odd : Odd d) (killed : x^((2:ℕ)^t)=1) :
    orderOf (x^d)=orderOf x := by
  have cop := (odd.coprime_two_left.pow_left t).of_dvd_left (orderOf_dvd_of_pow_eq_one killed)
  rw [orderOf_pow,cop.gcd_eq_one,Nat.div_one]

omit [DecidableEq G] in
private theorem odd_project {x : G} {d u t a : ℕ}
    (size : Fintype.card G=u*2^(a+1)) (du : Odd d) (ou : Odd u)
    (killed : x^(d*2^t)=1) : orderOf (x^d)=orderOf (x^u) := by
  have kill := killed
  rw [pow_mul] at kill
  have canonical : (x^u)^((2:ℕ)^(a+1))=1 := by rw [←pow_mul,←size,pow_card_eq_one]
  calc
    _ = orderOf ((x^d)^u) := (odd_power_same ou kill).symm
    _ = orderOf ((x^u)^d) := by rw [←pow_mul,←pow_mul,mul_comm d u]
    _ = _ := odd_power_same du canonical

omit [DecidableEq G] [DecidableEq H] in
/-- The odd part of any positive annihilator yields the same separation as
the odd parts of the group sizes. No global-exponent premise is needed. -/
theorem separates {u v a b d t : ℕ} (x : G) (y : H)
    (sizeG : Fintype.card G=u*2^(a+1)) (sizeH : Fintype.card H=v*2^(b+1))
    (ou : Odd u) (ov : Odd v) (od : Odd d) (kx : x^(d*2^t)=1) (ky : y^(d*2^t)=1)
    (different : orderOf (x^u)≠orderOf (y^v)) :
    ∃ i<t, (x^(d*2^i)=1 ∧ y^(d*2^i)≠1) ∨ (x^(d*2^i)≠1 ∧ y^(d*2^i)=1) := by
  have diff : orderOf (x^d)≠orderOf (y^d) := by
    rwa [odd_project sizeG od ou kx,odd_project sizeH od ov ky]
  simp only [pow_mul] at kx ky ⊢
  exact halving_chain_separates (x^d) (y^d) kx ky diff

/-- The counted equal-order tuples are exactly those for which no comparison
along this particular annihilator's chain distinguishes the two components. -/
theorem failure_iff {u v a b d t : ℕ} (x : G) (y : H)
    (sizeG : Fintype.card G=u*2^(a+1)) (sizeH : Fintype.card H=v*2^(b+1))
    (ou : Odd u) (ov : Odd v) (od : Odd d) (kx : x^(d*2^t)=1) (ky : y^(d*2^t)=1)
    (sign : (x,y)∈opposite (layer G u a) (layer H v b)) :
    (x,y)∈failures G H u v a b ↔ ∀ i<t, (x^(d*2^i)=1 ↔ y^(d*2^i)=1) := by
  constructor
  · intro hf i _
    have same : orderOf (x^u)=orderOf (y^v) := (mem_filter.mp hf).2
    rw [pow_mul,pow_mul,←orderOf_dvd_iff_pow_eq_one,←orderOf_dvd_iff_pow_eq_one,
      odd_project sizeG od ou kx,odd_project sizeH od ov ky,same]
  · intro all
    apply mem_filter.mpr
    refine ⟨sign,?_⟩
    by_contra ne
    obtain ⟨i,hi,dis⟩ := separates x y sizeG sizeH ou ov od kx ky ne
    rcases dis with ⟨l,r⟩|⟨l,r⟩
    · exact r ((all i hi).mp l)
    · exact l ((all i hi).mpr r)

/-- The local top layer of the multiplicative field group is exactly its
nonsquares, by Euler's criterion. -/
theorem top_iff_nonsquare {p u a : ℕ} [Fact p.Prime] (size : p-1=u*2^(a+1))
    (x : (ZMod p)ˣ) : x∈layer (ZMod p)ˣ u a ↔ ¬∃ y : (ZMod p)ˣ, y^2=x := by
  have pc := (Nat.prime_iff_card_units p).mp (Fact.out : p.Prime)
  have full : x^(u*2^(a+1))=1 := by rw [←size,←pc,pow_card_eq_one]
  have half : p/2=u*2^a := by
    have pp := (Fact.out : p.Prime).two_le
    rw [pow_succ,←mul_assoc] at size
    omega
  simp only [layer,mem_filter,mem_univ,true_and,full,ZMod.euler_criterion_units,half]

private theorem top_legendre {p u a : ℕ} [Fact p.Prime] (size : p-1=u*2^(a+1))
    (z : ℤ) (x : (ZMod p)ˣ) (coord : (x:ZMod p)=z) :
    x∈layer (ZMod p)ˣ u a ↔ legendreSym p z = -1 := by
  have nz : (z:ZMod p)≠0 := coord ▸ x.ne_zero
  rw [top_iff_nonsquare size,ZMod.euler_criterion_units,legendreSym.eq_neg_one_iff,
    ZMod.euler_criterion p nz,←coord]
  simp [Units.ext_iff]

/-- A representative's computable Jacobi symbol selects exactly the
opposite-character rectangles counted above for its two reductions. -/
theorem jacobi_iff {p q u v a b : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (ps : p-1=u*2^(a+1)) (qs : q-1=v*2^(b+1)) (z : ℤ)
    (x : (ZMod p)ˣ) (y : (ZMod q)ˣ) (cx : (x:ZMod p)=z) (cy : (y:ZMod q)=z) :
    jacobiSym z (p*q) = -1 ↔
      (x,y)∈opposite (layer (ZMod p)ˣ u a) (layer (ZMod q)ˣ v b) := by
  rw [mem_opposite,jacobiSym.mul_right' z hp.out.ne_zero hq.out.ne_zero,
    ←jacobiSym.legendreSym.to_jacobiSym,←jacobiSym.legendreSym.to_jacobiSym]
  simp only [top_legendre ps z x cx,top_legendre qs z y cy]
  have nzp : (z:ZMod p)≠0 := cx ▸ x.ne_zero
  have nzq : (z:ZMod q)≠0 := cy ▸ y.ne_zero
  rcases legendreSym.eq_one_or_neg_one p nzp with h|h <;>
    rcases legendreSym.eq_one_or_neg_one q nzq with j|j <;> simp [h,j]

end PrimeFactors.JacobiHalvingCount
