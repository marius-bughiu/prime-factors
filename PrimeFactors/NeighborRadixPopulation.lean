import PrimeFactors.LowBitsCarryMenu
import PrimeFactors.NeighborRadixDivisors
import Mathlib.Data.Nat.Log

/-! Count all radix carry hits when the radix is allowed to be any divisor of
either neighboring integer, even if it was selected using the whole product. -/

namespace PrimeFactors.NeighborRadixPopulation

open Finset NeighborRadixDivisors

set_option exponentiation.threshold 8192

/-- One signed residue has at most B lifts in the factor interval [X,2X),
provided BD≥X. Enumeration is only in the mathematical counting proof. -/
private def lifts (X D B : ℕ) (u : ℤ) : Finset ℕ := (range B).image fun i =>
  X+((u-X)%(D:ℤ)).toNat+D*i

private theorem lifts_card (X D B : ℕ) (u : ℤ) : (lifts X D B u).card≤B :=
  card_image_le.trans_eq (card_range _)

private theorem mem_lifts {p D X B : ℕ} {u : ℤ} (dp : 0<D) (pl : X≤p) (ph : p<2*X)
    (width : X≤B*D) (res : u≡p [ZMOD (D:ℤ)]) : p∈lifts X D B u := by
  let d := p-X
  have dz : (d:ℤ)=(p:ℤ)-X := Int.ofNat_sub pl
  have modEq : u-X≡(d:ℤ) [ZMOD (D:ℤ)] := dz ▸ res.sub_right X
  have r : ((u-X)%(D:ℤ)).toNat = d%D := by
    rw [modEq.eq,←Int.natCast_mod,Int.toNat_natCast]
  refine mem_image.mpr ⟨d/D,mem_range.mpr ((Nat.div_lt_iff_lt_mul dp).mpr (by dsimp [d]; omega)),?_⟩
  rw [r,Nat.add_assoc,Nat.mod_add_div]; dsimp [d]; omega

private def signedCells (X D B : ℕ) (w : ℤ) : Finset (ℕ×ℕ) :=
  w.divisorsAntidiag.biUnion fun z => lifts X D B z.1 ×ˢ lifts X D B z.2

private def cells (X D B m : ℕ) := signedCells X D B (m:ℤ) ∪ signedCells X D B (-(m:ℤ))

private theorem cells_card (X D B m : ℕ) : (cells X D B m).card ≤ m.divisors.card*(4*B^2) := by
  have ac : m.divisorsAntidiagonal.card=m.divisors.card := by rw [←Nat.map_div_right_divisors,card_map]
  have cost (w : ℤ) : (signedCells X D B w).card≤w.divisorsAntidiag.card*(B*B) := by
    apply card_biUnion_le_card_mul; intro z _; rw [card_product]; exact Nat.mul_le_mul (lifts_card ..) (lifts_card ..)
  have pos := cost (m:ℤ); have neg := cost (-(m:ℤ))
  rw [Int.divisorsAntidiag_natCast,card_disjUnion,card_map,card_map,ac] at pos
  rw [Int.divisorsAntidiag_neg_natCast,card_disjUnion,card_map,card_map,ac] at neg
  exact (card_union_le ..).trans ((Nat.add_le_add pos neg).trans_eq (by ring))

private theorem mem_cells {p q X D B : ℕ} {w : ℤ} (dp : 0<D) (width : X≤B*D)
    (pl : X≤p) (ph : p<2*X) (ql : X≤q) (qh : q<2*X) (nz : w≠0)
    (lift : LowBitsCarryMenu.Lift D p q w) : (p,q)∈cells X D B w.natAbs := by
  obtain ⟨a,b,hw⟩ := lift
  let u := (p:ℤ)-a*D
  let v := (q:ℤ)-b*D
  have one : (p,q)∈signedCells X D B w := by
    apply mem_biUnion.mpr; refine ⟨(u,v),(Int.prodMk_mem_divisorsAntidiag nz).mpr hw.symm,mem_product.mpr ⟨?_,?_⟩⟩
    · exact mem_lifts dp pl ph width (Int.modEq_iff_dvd.mpr ⟨a,by dsimp [u]; ring⟩)
    · exact mem_lifts dp ql qh width (Int.modEq_iff_dvd.mpr ⟨b,by dsimp [v]; ring⟩)
  rcases le_total 0 w with pos|neg
  · apply mem_union_left; simpa only [Int.natCast_natAbs,abs_of_nonneg pos] using one
  · apply mem_union_right; simpa only [Int.natCast_natAbs,abs_of_nonpos neg,neg_neg] using one

/-- For a neighboring product the nearest remainder is exactly the chosen
sign. Radix strictly greater than 2 avoids a half tie. -/
theorem output_neighbor {n D : ℕ} {s k : ℤ} (dp : 2<D) (sgn : s=1 ∨ s= -1)
    (dvd : (D:ℤ)∣(n:ℤ)-s) : LowBitsCarryMenu.output n D k=s+D*k := by
  obtain ⟨j,hj⟩ := dvd
  have pos : 0<(D:ℤ) := by exact_mod_cast (by omega : 0<D)
  have mag : |s|=1 := by rcases sgn with rfl|rfl <;> decide
  have zero : PredictedTraceCarries.nearest s D=0 := by
    have H := PredictedTraceCarries.nearest_abs_le (H:=0) (n:=s) pos (by rw [abs_mul,mag]; norm_num; exact_mod_cast dp)
    simpa using H
  have eq : (n:ℤ)=s+(D:ℤ)*j := by omega
  unfold LowBitsCarryMenu.output; rw [eq,PredictedTraceCarries.nearest_shift pos,zero]; ring

private theorem nonzero_neighbor {s k : ℤ} {D : ℕ} (dp : 2<D) (sgn : s=1 ∨ s= -1) : s+(D:ℤ)*k≠0 := by
  intro z
  have dvd : (D:ℤ)∣s := ⟨-k,by linarith only [z]⟩
  have dn := Int.natAbs_dvd_natAbs.mpr dvd
  rcases sgn with rfl|rfl <;> simp at dn <;> omega

private theorem branch {s k : ℤ} (D : ℕ) (sgn : s=1 ∨ s= -1) :
    ∃ plus : Bool, (s+(D:ℤ)*k).natAbs=value k.natAbs D plus := by
  have cases (z : ℤ) : z=(z.natAbs:ℤ) ∨ z= -(z.natAbs:ℤ) := by
    rw [Int.natCast_natAbs]; rcases le_total 0 z with h|h
    · exact Or.inl (abs_of_nonneg h).symm
    · right; rw [abs_of_nonpos h,neg_neg]
  rcases sgn with rfl|rfl <;> rcases cases k with hk|hk
  · exact ⟨true,congrArg Int.natAbs (by dsimp [value]; linear_combination (D:ℤ)*hk)⟩
  · refine ⟨false,?_⟩; unfold value; simp only [Bool.false_eq_true,if_false]
    rw [←Int.natAbs_neg (1+(D:ℤ)*k)]; congr 1; linear_combination -(D:ℤ)*hk
  · exact ⟨false,congrArg Int.natAbs (by dsimp [value]; linear_combination (D:ℤ)*hk)⟩
  · refine ⟨true,?_⟩; unfold value; simp only [if_true]
    rw [←Int.natAbs_neg (-1+(D:ℤ)*k)]; congr 1; linear_combination -(D:ℤ)*hk

private def bands (X D B t : ℕ) := cells X D B (value t D true) ∪ cells X D B (value t D false)
private def octave (X P B K : ℕ) :=
  (range (K+1)).biUnion fun t => (Ico P (2*P)).biUnion fun D => bands X D B t

private theorem octave_card {X P B K : ℕ} (pp : 0<P) (width : 2*K≤P) :
    (octave X P B K).card ≤ (K+1)*(16*P*(P.log2+2)*B^2) := by
  have localBound (t : ℕ) (ht : t≤K) : ((Ico P (2*P)).biUnion fun D => bands X D B t).card ≤ 16*P*(P.log2+2)*B^2 := by
    have le : 2*t≤P := by omega
    let M := Ico P (2*P)
    calc
      _ ≤ ∑ D∈M, (bands X D B t).card := card_biUnion_le
      _ ≤ ∑ D∈M, ((value t D true).divisors.card*(4*B^2)+(value t D false).divisors.card*(4*B^2)) :=
        sum_le_sum fun D _ => (card_union_le ..).trans (Nat.add_le_add (cells_card ..) (cells_card ..))
      _ = (∑ D∈M, (value t D true).divisors.card)*(4*B^2)+(∑ D∈M, (value t D false).divisors.card)*(4*B^2) := by
        rw [sum_add_distrib,Finset.sum_mul,Finset.sum_mul]
      _ ≤ _ := (Nat.add_le_add (Nat.mul_le_mul_right _ (sum_tau pp le true)) (Nat.mul_le_mul_right _ (sum_tau pp le false))).trans_eq (by ring)
  simpa only [card_range] using card_biUnion_le_card_mul (range (K+1)) _ _ (fun t ht => localBound t (by have := mem_range.mp ht; omega))

/-- The whole input may decide the radix and both carries: this includes
all positive radices dividing either N−1 or N+1 in the stated interval. -/
def Hit (K : ℕ) (z : ℕ×ℕ) : Prop :=
  z.1.Prime ∧ z.2.Prime ∧ z.1≠z.2 ∧ 2^1023≤z.1 ∧ z.1<2^1024 ∧ 2^1023≤z.2 ∧ z.2<2^1024 ∧
  ∃ D : ℕ, 2^513≤D ∧ D≤2^1024 ∧ (∃ s : ℤ, (s=1 ∨ s= -1) ∧ (D:ℤ)∣((z.1:ℤ)*z.2-s)) ∧
    ∃ h k : ℤ, |k|≤K ∧ ∃ f, PredictedTraceCarries.probe (z.1*z.2) D h k=some f

def copies (e : ℕ) := 2^(1023-e)
def price (e : ℕ) := 16*2^e*(e+2)*(copies e)^2

private theorem capacity {e : ℕ} : (2:ℕ)^1023 ≤ copies e * 2^e := by
  unfold copies; rw [←pow_add]; apply Nat.pow_le_pow_right (by decide); omega

attribute [local irreducible] octave bands cells signedCells lifts PredictedTraceCarries.probe

private theorem octave_of_hit {K : ℕ} {z : ℕ×ℕ} (H : Hit K z) :
    ∃ e, 513≤e ∧ e≤1024 ∧ z∈octave (2^1023) (2^e) (copies e) K := by
  unfold Hit at H
  obtain ⟨pp,qp,ne,pl,ph,ql,qh,rest⟩ := H
  obtain ⟨D,dl,dh,neighbors,attempt⟩ := rest
  obtain ⟨s,sgn,neighbor⟩ := neighbors
  obtain ⟨h,k,kl,f,hit⟩ := attempt
  let e := Nat.log 2 D
  have dp : 2<D := lt_of_lt_of_le (by decide +kernel) dl
  have Plo : 2^e≤D := Nat.pow_log_le_self _ (by omega)
  have Phi : D<2*2^e := by simpa only [pow_succ,Nat.mul_comm 2] using Nat.lt_pow_succ_log_self (by decide : 1<2) D
  have lo : 513≤e := Nat.le_log_of_pow_le (by decide) dl
  have hi : e≤1024 := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (Plo.trans dh)
  have tcap : k.natAbs≤K := by exact_mod_cast (show (k.natAbs:ℤ)≤K by simpa only [Int.natCast_natAbs] using kl)
  have lifted := LowBitsCarryMenu.lift_of_probe pp qp ne hit
  have eq := output_neighbor (n:=z.1*z.2) (k:=k) dp sgn (by simpa only [Nat.cast_mul] using neighbor)
  rw [eq] at lifted
  obtain ⟨plus,hb⟩ := branch (k:=k) D sgn
  have wide := (capacity (e:=e)).trans (Nat.mul_le_mul_left (copies e) Plo)
  have top : (2:ℕ)^1024=2*2^1023 := by decide +kernel
  have one := mem_cells (by omega : 0<D) wide pl (top ▸ ph) ql (top ▸ qh) (nonzero_neighbor dp sgn) lifted
  rw [hb] at one
  refine ⟨e,lo,hi,?_⟩
  rw [octave]
  apply mem_biUnion.mpr; refine ⟨k.natAbs,mem_range.mpr (by omega),mem_biUnion.mpr ⟨D,mem_Ico.mpr ⟨Plo,Phi⟩,?_⟩⟩
  rw [bands]
  cases plus with
  | false => exact mem_union_right _ one
  | true => exact mem_union_left _ one

private theorem cover_sum {α : Type} [DecidableEq α] {pairs : Finset α}
    (base num : ℕ) (f : ℕ → Finset α)
    (covered : ∀ z∈pairs, ∃ e, base≤e ∧ e<base+num ∧ z∈f e) :
    pairs.card ≤ ∑ i∈range num, (f (base+i)).card := by
  have sub : pairs ⊆ (range num).biUnion (fun i => f (base+i)) := by
    intro z hz
    obtain ⟨e,lo,hi,mem⟩ := covered z hz
    exact mem_biUnion.mpr ⟨e-base,mem_range.mpr (by omega),by simpa only [Nat.add_sub_of_le lo] using mem⟩
  exact (card_le_card sub).trans card_biUnion_le

/-- The final octave starts at the upper endpoint. Its one-lift bound
does not use a zero integer quotient at D=2^1024. -/
theorem count {pairs : Finset (ℕ×ℕ)} {K : ℕ} (kc : 2*K≤2^513)
    (hits : ∀ z∈pairs, Hit K z) : pairs.card ≤ (K+1)*(∑ i∈range 512, price (513+i)) := by
  let family (e : ℕ) := octave (2^1023) (2^e) (copies e) K
  have cov : ∀ z∈pairs, ∃ e, 513≤e ∧ e<513+512 ∧ z∈family e := by
    intro z hz
    obtain ⟨e,lo,hi,mem⟩ := octave_of_hit (hits z hz)
    exact ⟨e,lo,by omega,mem⟩
  have each (i : ℕ) : (family (513+i)).card ≤ (K+1)*price (513+i) := by
    have h := octave_card (X:=2^1023) (B:=copies (513+i)) (Nat.two_pow_pos (513+i))
      (kc.trans (Nat.pow_le_pow_right (by decide) (by omega : 513≤513+i)))
    simpa only [family,price,Nat.log2_eq_log_two,Nat.log_pow (by decide : 1<2)] using h
  exact (cover_sum 513 512 family cov).trans ((sum_le_sum fun i _ => each i).trans_eq (Finset.mul_sum ..).symm)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 6000000 in
private theorem price_budget :
    (2:ℕ)^472*(4+1)*(∑ i∈range 512, price (513+i))*21000000≤2^2046 ∧
    (2:ℕ)^117*(2^357+1)*(∑ i∈range 512, price (513+i))*21000000≤2^2046 := by decide +kernel

private theorem normalize {A K C f pop : ℕ} (card : A≤(K+1)*C)
    (budget : f*(K+1)*C*21000000≤2^2046) (den : 2^2046<21000000*pop) : f*A<pop := by
  apply Nat.lt_of_mul_lt_mul_right (a:=21000000)
  calc
    _ ≤ f*((K+1)*C)*21000000 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ card)
    _ = f*(K+1)*C*21000000 := by ac_rfl
    _ < _ := budget.trans_lt (by simpa [mul_comm] using den)

/-- Fraction of eligible unordered pairs under the explicit population
normalization, with both neighbor signs and arbitrary high correction. -/
theorem small {pairs : Finset (ℕ×ℕ)} {pop : ℕ} (den : 2^2046<21000000*pop)
    (hits : ∀ z∈pairs, Hit 4 z) : 2^472*pairs.card<pop :=
  normalize (count (by decide +kernel) hits) price_budget.1 den

theorem wide {pairs : Finset (ℕ×ℕ)} {pop : ℕ} (den : 2^2046<21000000*pop)
    (hits : ∀ z∈pairs, Hit (2^357) z) : 2^117*pairs.card<pop :=
  normalize (count (by decide +kernel) hits) price_budget.2 den

end PrimeFactors.NeighborRadixPopulation
