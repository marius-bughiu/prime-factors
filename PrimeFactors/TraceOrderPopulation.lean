import PrimeFactors.WeightedGlobalTrace
import PrimeFactors.FrobeniusFixedCounts
import PrimeFactors.GeometricOrderFailure
import Mathlib.Data.Nat.Dist

/-! A finite test for all possible base orders in a fixed weighted power
comparison schedule. Each product in that schedule has a known prime
factorization for the purpose of evaluating the search. -/
namespace PrimeFactors.TraceOrderPopulation
open Finset

abbrev Query := ℕ × ℕ

/-- The two equalities X=Y and XY=1 use these unsigned exponents. -/
def query (h c s d : ℕ) : Query :=
  (Nat.dist s ((h+1)*c+h*d),Nat.dist (s+h*d) ((h+1)*c))

private theorem eq_pow {G : Type*} [Group G] (u : G) (a b : ℕ) :
    u^a=u^b ↔ orderOf u∣Nat.dist a b := by
  rcases le_total a b with h|h
  · rw [Nat.dist_eq_sub_of_le h,pow_eq_pow_iff_modEq,Nat.modEq_iff_dvd' h]
  · rw [eq_comm,Nat.dist_eq_sub_of_le_right h,pow_eq_pow_iff_modEq,Nat.modEq_iff_dvd' h]

theorem orientations {G : Type*} [CommGroup G] (u : G) (h c s d : ℕ) :
    (WeightedGlobalTrace.left u h c s=WeightedGlobalTrace.right u h d ↔
      orderOf u∣(query h c s d).1) ∧
    (WeightedGlobalTrace.left u h c s*WeightedGlobalTrace.right u h d=1 ↔
      orderOf u∣(query h c s d).2) := by
  unfold WeightedGlobalTrace.left WeightedGlobalTrace.right query
  constructor
  · rw [div_eq_iff_eq_mul',←pow_add]
    exact eq_pow ..
  · rw [div_mul_eq_mul_div,div_eq_one,←pow_add]
    exact eq_pow ..

/-- An exponent in setup splits the two primes exactly when it kills the
base on just one side. -/
def Clear (setup : List ℕ) (r t : ℕ) : Prop :=
  ∀ e∈setup, (r∣e ↔ t∣e)

/-- The scalar equality holds on the first side only. The inverse
equality on the second makes the two traces equal modulo the product. -/
def Branch (r t : ℕ) (z : Query) : Prop := r∣z.1 ∧ t∣z.2 ∧ ¬t∣z.1

/-- On a pair of prime fields, a shared trace and a scalar equality on
exactly one side are equivalent to the two order-divisibility branches. -/
theorem mixed_readout {F K : Type*} [Field F] [Field K] (u : Fˣ) (v : Kˣ) (h c s d : ℕ) :
    let x := WeightedGlobalTrace.left u h c s
    let y := WeightedGlobalTrace.right u h d
    let x' := WeightedGlobalTrace.left v h c s
    let y' := WeightedGlobalTrace.right v h d
    (TraceFoldedRight.trace 1 x=TraceFoldedRight.trace 1 y ∧
      TraceFoldedRight.trace 1 x'=TraceFoldedRight.trace 1 y' ∧
      ((x=y ∧ x'≠y') ∨ (x'=y' ∧ x≠y))) ↔
      Branch (orderOf u) (orderOf v) (query h c s d) ∨
      Branch (orderOf v) (orderOf u) (query h c s d) := by
  dsimp only
  simp only [ne_eq,TraceFoldedRight.field_match,
    (orientations u h c s d).1,(orientations u h c s d).2,
    (orientations v h c s d).1,(orientations v h c s d).2]
  unfold Branch
  tauto

def Wins (setup : List ℕ) (qs : List Query) (r t : ℕ) : Prop :=
  Clear setup r t ∧ ∃ z∈qs, Branch r t z ∨ Branch t r z

instance (setup : List ℕ) (r t : ℕ) : Decidable (Clear setup r t) := by unfold Clear; infer_instance
instance (z : Query) (r t : ℕ) : Decidable (Branch r t z) := by unfold Branch; infer_instance
instance (setup : List ℕ) (qs : List Query) (r t : ℕ) : Decidable (Wins setup qs r t) := by
  unfold Wins; infer_instance

/-- If every order dividing the first bound is killed, a base surviving
setup must also be killed on the second side, and conversely. -/
def step (bounds : ℕ × ℕ) (e : ℕ) : ℕ × ℕ :=
  let b := if bounds.1∣e then bounds.2.gcd e else bounds.2
  (if b∣e then bounds.1.gcd e else bounds.1,b)

private theorem step_dvd {e r t : ℕ} {b : ℕ × ℕ} (hr : r∣b.1) (ht : t∣b.2)
    (agree : r∣e ↔ t∣e) : r∣(step b e).1 ∧ t∣(step b e).2 := by
  have right : t ∣ (if b.1∣e then b.2.gcd e else b.2) := by
    split
    next he => exact Nat.dvd_gcd ht (agree.mp (hr.trans he))
    next => exact ht
  let tcap := if b.1∣e then b.2.gcd e else b.2
  change r ∣ (if tcap∣e then b.1.gcd e else b.1) ∧ t∣tcap
  refine ⟨?_,right⟩
  by_cases he : tcap∣e
  · rw [if_pos he]
    exact Nat.dvd_gcd hr (agree.mpr (right.trans he))
  · rwa [if_neg he]

theorem sweep_dvd {r t : ℕ} (setup : List ℕ) (b : ℕ × ℕ) (hr : r∣b.1) (ht : t∣b.2)
    (clear : Clear setup r t) :
    r∣(setup.foldl step b).1 ∧ t∣(setup.foldl step b).2 := by
  induction setup generalizing b with
  | nil => exact ⟨hr,ht⟩
  | cons e es ih =>
    have h := step_dvd hr ht (clear e (by simp))
    exact ih (step b e) h.1 h.2 (fun x hx => clear x (by simp [hx]))

def limits (P Q : ℕ) (setup : List ℕ) (z : Query) : ℕ × ℕ :=
  setup.foldl step (P.gcd z.1,Q.gcd z.2)

def covered (P Q L R : ℕ) (setup : List ℕ) (z : Query) : Bool :=
  let b := limits P Q setup z
  decide (b.2∣z.1 ∨ (0<b.1 ∧ b.1≤L ∧ 0<b.2 ∧ b.2≤R))

private theorem bounded {P Q L R r t : ℕ} {setup : List ℕ} {z : Query}
    (rP : r∣P) (tQ : t∣Q) (cl : Clear setup r t)
    (h : Branch r t z) (cover : covered P Q L R setup z=true) : r≤L ∧ t≤R := by
  let b := limits P Q setup z
  have divs := sweep_dvd setup (P.gcd z.1,Q.gcd z.2)
    (Nat.dvd_gcd rP h.1) (Nat.dvd_gcd tQ h.2.1) cl
  change r∣b.1 ∧ t∣b.2 at divs
  change decide (b.2∣z.1 ∨ (0<b.1 ∧ b.1≤L ∧ 0<b.2 ∧ b.2≤R))=true at cover
  rcases of_decide_eq_true cover with no|yes
  · exact False.elim (h.2.2 (divs.2.trans no))
  · exact ⟨(Nat.le_of_dvd yes.1 divs.1).trans yes.2.1,
      (Nat.le_of_dvd yes.2.2.1 divs.2).trans yes.2.2.2⟩

def coverTable (P Q L R : ℕ) (setup : List ℕ) (qs : List Query) : Bool :=
  qs.all fun z => covered P Q L R setup z && covered Q P R L setup z

def orders (P Q L R : ℕ) (setup : List ℕ) (qs : List Query) : Finset (ℕ × ℕ) :=
  ((Icc 1 L) ×ˢ Icc 1 R).filter fun z => z.1∣P ∧ z.2∣Q ∧ Wins setup qs z.1 z.2

theorem order_table {P Q L R r t : ℕ} {setup : List ℕ} {qs : List Query}
    (checked : coverTable P Q L R setup qs=true) (rp : 0<r) (tp : 0<t)
    (rP : r∣P) (tQ : t∣Q) :
    Wins setup qs r t ↔ (r,t)∈orders P Q L R setup qs := by
  constructor
  · intro win
    obtain ⟨cl,z,hz,br⟩ := win
    have cert := Bool.and_eq_true_iff.mp (List.all_eq_true.mp checked z hz)
    have size : r≤L ∧ t≤R := by
      rcases br with br|br
      · exact bounded rP tQ cl br cert.1
      · exact (bounded tQ rP (fun e he => (cl e he).symm) br cert.2).symm
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨rp,size.1⟩,mem_Icc.mpr ⟨tp,size.2⟩⟩,
      rP,tQ,cl,z,hz,br⟩
  · intro mem
    exact (mem_filter.mp mem).2.2.2

/-- Any order class in a finite cyclic unit group has exactly phi(r)
elements. CRT makes the local base choices independent. -/
theorem population (G H : Type*) [Group G] [Group H] [Fintype G] [Fintype H]
    [IsCyclic G] [IsCyclic H] (S : Finset (ℕ × ℕ))
    (valid : ∀ z∈S, z.1∣Fintype.card G ∧ z.2∣Fintype.card H) :
    letI := Classical.decEq G
    letI := Classical.decEq H
    ((univ : Finset (G × H)).filter fun x => (orderOf x.1,orderOf x.2)∈S).card =
      ∑ z∈S, z.1.totient*z.2.totient := by
  classical
  let box (z : ℕ × ℕ) := (univ.filter fun g : G => orderOf g=z.1) ×ˢ
    (univ.filter fun h : H => orderOf h=z.2)
  have union : (univ.filter fun x : G × H => (orderOf x.1,orderOf x.2)∈S)=S.biUnion box := by
    ext ⟨g,h⟩
    simp only [box,mem_filter,mem_univ,true_and,mem_biUnion,mem_product]
    exact ⟨fun m => ⟨_,m,rfl,rfl⟩,fun ⟨_,m,eg,eh⟩ => by simpa only [eg,eh] using m⟩
  rw [union,card_biUnion]
  · apply sum_congr rfl
    intro z hz
    exact (card_product _ _).trans (congrArg₂ Nat.mul
      (IsCyclic.card_orderOf_eq_totient (α:=G) (valid z hz).1)
      (IsCyclic.card_orderOf_eq_totient (α:=H) (valid z hz).2))
  · intro a _ b _ ne
    apply disjoint_left.mpr
    intro x ha hb
    obtain ⟨m,n⟩ := mem_product.mp ha
    obtain ⟨m',n'⟩ := mem_product.mp hb
    exact ne (Prod.ext ((mem_filter.mp m).2.symm.trans (mem_filter.mp m').2)
      ((mem_filter.mp n).2.symm.trans (mem_filter.mp n').2))

/-- Bases in the original modulus that survive setup and admit a proper
mixed readout at one of the given coordinates. -/
noncomputable def winningBases {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (setup : List ℕ) (qs : List Query) : Finset (ZMod (p*q))ˣ :=
  (univ.filter fun z : (ZMod p)ˣ × (ZMod q)ˣ =>
    Wins setup qs (orderOf z.1) (orderOf z.2)).image (GeometricOrderFailure.localPair cop).symm

theorem certified_count {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (cop : p.Coprime q)
    (L R : ℕ) (setup : List ℕ) (qs : List Query) (S : Finset (ℕ × ℕ)) (n : ℕ)
    (cover : coverTable (p-1) (q-1) L R setup qs=true)
    (table : orders (p-1) (q-1) L R setup qs=S)
    (size : ∑ z∈S, z.1.totient*z.2.totient = n) : (winningBases cop setup qs).card=n := by
  classical
  have pc := (Nat.prime_iff_card_units p).mp hp.out
  have qc := (Nat.prime_iff_card_units q).mp hq.out
  have hmem (x : (ZMod p)ˣ × (ZMod q)ˣ) :
      Wins setup qs (orderOf x.1) (orderOf x.2) ↔ (orderOf x.1,orderOf x.2)∈S := by
    rw [←table]
    exact order_table cover (orderOf_pos _) (orderOf_pos _) (pc ▸ orderOf_dvd_card)
      (qc ▸ orderOf_dvd_card)
  rw [winningBases,card_image_of_injective _ (GeometricOrderFailure.localPair cop).symm.injective]
  simp_rw [hmem]
  apply (population (ZMod p)ˣ (ZMod q)ˣ S ?_).trans size
  intro z hz
  rw [←table] at hz
  rw [pc,qc]
  exact ⟨(mem_filter.mp hz).2.1,(mem_filter.mp hz).2.2.1⟩

end PrimeFactors.TraceOrderPopulation
