import PrimeFactors.LinePower
import Mathlib.Data.ZMod.Units
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! Folding unit lookups along a reciprocal pair. The coefficient c is
optional mathematically, but lets the integer exponents r and m-r use the
same key without doubling exponents or choosing a square root of g^m. -/
namespace PrimeFactors.TraceFoldedRight
open Finset

variable {R : Type*} [CommRing R]

/-- Weight c=1 gives the ordinary unit trace. -/
def trace (c u : Rˣ) : R := (u:R)+(c:R)*(↑(u⁻¹):R)

/-- Replacing a local factor by its negative negates its sum with the
corresponding cofactor, giving the sign stability of local sum residues. -/
theorem neg_local_sum (c u : Rˣ) : trace c (-u) = -trace c u := by
  simp [trace,neg_add',add_comm]

/-- Cleared quadratic identity over rings with arbitrary zero divisors. -/
theorem factor (c y u : Rˣ) :
    (y:R)*(trace c y-trace c u) = ((y:R)-(u:R))*((y:R)-(c:R)*(↑(u⁻¹):R)) := by
  unfold trace
  linear_combination (c:R)*(Units.mul_inv y) - (c:R)*(Units.mul_inv u)

theorem trace_iff (c y u : Rˣ) :
    trace c y=trace c u ↔ ((y:R)-(u:R))*((y:R)-(c:R)*(↑(u⁻¹):R))=0 := by
  rw [←factor]
  constructor
  · intro eq; rw [eq,sub_self,mul_zero]
  · intro zero
    exact sub_eq_zero.mp (y.isUnit.mul_left_cancel (zero.trans (mul_zero _).symm))

theorem same_key {c y u : Rˣ} (paired : y*u=c) : trace c y=trace c u := by
  have eq := eq_mul_inv_iff_mul_eq.mpr paired
  apply (trace_iff ..).mpr
  rw [show (y:R)=(c:R)*(↑(u⁻¹):R) from congrArg Units.val eq,sub_self,mul_zero]

/-- An endpoint-centered exponent pair can share a hash key using ordinary powers. -/
theorem complementary_indices (g : Rˣ) {a m : ℕ} (inside : a≤m) :
    trace (g^m) (g^a)=trace (g^m) (g^(m-a)) :=
  same_key (by rw [←pow_add,Nat.add_sub_of_le inside])

/-- Field fibers of the unweighted key have at most the two orientations. -/
theorem field_match {F : Type*} [Field F] (y u : Fˣ) :
    trace 1 y=trace 1 u ↔ y=u ∨ y*u=1 := by
  rw [Units.ext_iff (a₁:=y) (a₂:=u),Units.ext_iff (a₁:=y*u) (a₂:=1)]
  simpa only [trace,Units.val_one,one_mul,Units.val_inv_eq_inv_val,Units.val_mul] using
    (linePower_trace_eq y.ne_zero u.ne_zero)

/-- A trace match is either an ordinary comparison, a reciprocal comparison,
or a nontrivial gcd of the ordinary residue difference with the modulus. -/
theorem classify {n : ℕ} [NeZero n] (c y u : (ZMod n)ˣ) (hit : trace c y=trace c u) :
    y=u ∨ y*u=c ∨
      (1<((y:ZMod n)-(u:ZMod n)).val.gcd n ∧ ((y:ZMod n)-(u:ZMod n)).val.gcd n<n) := by
  by_cases eq : y=u
  · exact Or.inl eq
  right
  by_cases mate : y*u=c
  · exact Or.inl mate
  right
  let x := (y:ZMod n)-(u:ZMod n)
  have nz : x≠0 := fun zero => eq (Units.ext (sub_eq_zero.mp zero))
  have nonunit : ¬IsUnit x := by
    intro unit
    have zero := (trace_iff ..).mp hit
    have rhs := unit.mul_left_cancel (zero.trans (mul_zero x).symm)
    exact mate (eq_mul_inv_iff_mul_eq.mp (Units.ext (sub_eq_zero.mp rhs)))
  have notOne : x.val.gcd n≠1 := by
    intro cop
    exact nonunit (ZMod.natCast_zmod_val x ▸ (ZMod.isUnit_iff_coprime x.val n).mpr cop)
  have positive := Nat.gcd_pos_of_pos_right x.val (NeZero.pos n)
  have xp : 0<x.val := Nat.pos_of_ne_zero (fun e => nz ((ZMod.val_eq_zero x).mp e))
  change 1<x.val.gcd n ∧ x.val.gcd n<n
  exact ⟨by omega,(Nat.le_of_dvd xp (Nat.gcd_dvd_left ..)).trans_lt (ZMod.val_lt x)⟩

/-- Distinct orientations at the factors 7 and 11 collide in the same
ordinary trace key 41, and the difference yields 7. -/
theorem mixed_example :
    let y : (ZMod 77)ˣ := ⟨72,46,by decide,by decide⟩
    let u : (ZMod 77)ˣ := ⟨2,39,by decide,by decide⟩
    trace 1 y = 41 ∧ trace 1 u = 41 ∧ y≠u ∧ y*u≠1 ∧ ((y:ZMod 77)-(u:ZMod 77)).val.gcd 77=7 := by
  decide +kernel

/-- Inversion orbits of any stable, ordered finite index set. -/
noncomputable def representatives {α : Type*} [LinearOrder α] (S : Finset α) (mate : α → α) : Finset α :=
  S.filter (fun a => a≤mate a)

/-- Exactly one representative for every nonfixed pair, with each fixed
point counted once. This counts stored index pairs, even if more trace keys
coincide over a composite modulus. -/
theorem orbit_count {α : Type*} [LinearOrder α] (S : Finset α) (f : α→α)
    (stable : ∀ a∈S, f a∈S) (inv : ∀ a∈S, f (f a)=a) :
    2*(representatives S f).card=S.card+(S.filter (fun a => a=f a)).card := by
  classical
  let L := S.filter (fun a => a<f a)
  let H := S.filter (fun a => f a<a)
  let F := S.filter (fun a => a=f a)
  have pair : L.image f=H := by
    ext a
    constructor
    · intro h
      obtain ⟨b,hb,rfl⟩ := mem_image.mp h
      obtain ⟨bs,bl⟩ := mem_filter.mp hb
      exact mem_filter.mpr ⟨stable b bs,by simpa only [inv b bs] using bl⟩
    · intro h
      obtain ⟨ha,hlt⟩ := mem_filter.mp h
      exact mem_image.mpr ⟨f a,mem_filter.mpr ⟨stable a ha,by simpa only [inv a ha] using hlt⟩,inv a ha⟩
  have eqcard : L.card=H.card := by
    rw [←pair,card_image_of_injOn]
    intro a ha b hb eq
    exact (inv a (mem_filter.mp ha).1).symm.trans ((congrArg f eq).trans (inv b (mem_filter.mp hb).1))
  have split := filter_card_add_filter_neg_card_eq_card (s:=S) (fun a => a≤f a)
  simp only [not_le] at split
  change (representatives S f).card+H.card=S.card at split
  have rep : representatives S f=L∪F := by
    ext a
    simp only [representatives,L,F,mem_filter,mem_union]
    exact ⟨fun ⟨ha,e⟩ => (lt_or_eq_of_le e).elim (fun l => Or.inl ⟨ha,l⟩) (fun r => Or.inr ⟨ha,r⟩),
      fun h => h.elim (fun ⟨ha,e⟩ => ⟨ha,e.le⟩) (fun ⟨ha,e⟩ => ⟨ha,e.le⟩)⟩
  have dis : Disjoint L F := disjoint_left.mpr (fun _ a b =>
    (mem_filter.mp a).2.ne (mem_filter.mp b).2)
  rw [rep,card_union_of_disjoint dis] at split ⊢
  change 2*(L.card+F.card)=S.card+F.card
  omega

/-- Restricting to representatives preserves all lookup keys. -/
theorem image_keys {α β : Type*} [LinearOrder α] [DecidableEq β]
    (S : Finset α) (f : α→α) (key : α→β) (stable : ∀ a∈S, f a∈S)
    (inv : ∀ a∈S, f (f a)=a) (same : ∀ a∈S, key (f a)=key a) :
    (representatives S f).image key=S.image key := by
  apply Subset.antisymm (image_subset_image (filter_subset ..))
  intro v hv
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hv
  by_cases le : a≤f a
  · exact mem_image.mpr ⟨a,mem_filter.mpr ⟨ha,le⟩,rfl⟩
  · exact mem_image.mpr ⟨f a,mem_filter.mpr ⟨stable a ha,by rw [inv a ha]; exact le_of_not_ge le⟩,
      same a ha⟩

/-- Signed representative of a right CRT residue after shifting the origin.
The positive sign owns the even midpoint. -/
def centered (period r : ℤ) : ℤ := if 2*r≤period then r else r-period

/-- The integer ranks actually stored, before dividing them into trace buckets. -/
noncomputable def stored (period : ℤ) (right : Finset ℤ) : Finset ℤ :=
  right.image (fun r => |centered period r|)

/-- Simultaneous negation of all local CRT digits preserves the stored radius.
The order on tuples may be lexicographic, as in a first-nonfixed-digit walk. -/
theorem stored_of_representatives {α : Type*} [LinearOrder α]
    (S : Finset α) (f : α → α) (raw : α → ℤ) (m : ℤ)
    (stable : ∀ v∈S, f v∈S) (inv : ∀ v∈S, f (f v)=v)
    (inside : ∀ v∈S, 0≤raw v ∧ raw v<m)
    (negate : ∀ v∈S, raw (f v)=if raw v=0 then 0 else m-raw v) :
    (representatives S f).image (fun v => |centered m (raw v)|)=stored m (S.image raw) := by
  unfold stored
  rw [image_image]
  apply image_keys S f (fun v => |centered m (raw v)|) stable inv
  intro v hv
  obtain ⟨v0,vm⟩ := inside v hv
  rw [negate v hv]
  by_cases zero : raw v=0
  · simp [zero]
  · rw [if_neg zero]
    unfold centered
    split_ifs <;> rw [abs_eq_max_neg,abs_eq_max_neg] <;> omega

/-- For a modular CRT encoding, the negation law gives the required
canonical integer-residue identity, including when the encoding is zero. -/
theorem stored_of_crt {α : Type*} [LinearOrder α] {m : ℕ} [NeZero m]
    (S : Finset α) (f : α → α) (encode : α → ZMod m)
    (stable : ∀ v∈S, f v∈S) (inv : ∀ v∈S, f (f v)=v)
    (negate : ∀ v∈S, encode (f v) = -encode v) :
    let raw : α → ℤ := fun v => (encode v).val
    (representatives S f).image (fun v => |centered m (raw v)|)=stored m (S.image raw) := by
  dsimp only
  apply stored_of_representatives S f (fun v => ((encode v).val : ℤ)) m stable inv
  · intro v _
    exact ⟨Int.natCast_nonneg _,by exact_mod_cast ZMod.val_lt (encode v)⟩
  · intro v hv
    rw [negate v hv,ZMod.neg_val]
    by_cases zero : encode v=0
    · simp [zero]
    · rw [if_neg zero, Nat.cast_sub (ZMod.val_lt _).le]
      have ne : ((encode v).val : ℤ) ≠ 0 := by
        exact_mod_cast fun h => zero ((ZMod.val_eq_zero _).mp h)
      rw [if_neg ne]

def signedRank (plus : Bool) (t : ℤ) : ℤ := if plus then t else -t

/-- Inclusive bounds used to restrict a sorted bucket in each orientation. -/
def rankWindow (period offset width : ℤ) (plus : Bool) (t : ℤ) : Prop :=
  if plus then max 0 (-offset)≤t ∧ t≤min (period/2) (width-offset)
  else max 1 (offset-width)≤t ∧ t≤min ((period-1)/2) offset

/-- The actual loop bounds on the integer period shift. -/
def wrapWindow (period a center width k : ℤ) : Prop :=
  -((width+period/2-a-center)/period)≤k ∧ k≤(a+center+period/2)/period

private theorem wrap_of_rank {m a c w k t : ℤ} {plus : Bool} (mp : 0<m)
    (ok : rankWindow m (a+c-k*m) w plus t) : wrapWindow m a c w k := by
  unfold wrapWindow
  have bounds : (-k)*m≤w+m/2-a-c ∧ k*m≤a+c+m/2 := by
    cases plus <;> simp only [rankWindow, Bool.false_eq_true, ↓reduceIte, max_le_iff,
      le_min_iff, neg_mul] at ok ⊢ <;> omega
  have lo := (Int.le_ediv_iff_mul_le mp).mpr bounds.1
  exact ⟨by omega,(Int.le_ediv_iff_mul_le mp).mpr bounds.2⟩

/-- With canonical left coordinates and width smaller than the period, the
computed target shifts are among −1, 0, 1 and 2. -/
theorem wrap_limits {m a c w k : ℤ} (mp : 0<m) (a0 : 0≤a) (am : a<m)
    (c0 : 0≤c) (cm : c<m) (wm : w<m) (ok : wrapWindow m a c w k) :
    -1≤k ∧ k≤2 := by
  obtain ⟨lo,hi⟩ := ok
  have lo' : -k≤(w+m/2-a-c)/m := by omega
  have first := (Int.le_ediv_iff_mul_le mp).mp lo'
  have last := (Int.le_ediv_iff_mul_le mp).mp hi
  constructor
  · by_contra! h
    have big := mul_le_mul_of_nonneg_right (show (2:ℤ)≤ -k by omega) mp.le
    omega
  · by_contra! h
    have big := mul_le_mul_of_nonneg_right (show (3:ℤ)≤k by omega) mp.le
    omega

private theorem centered_mod (a c m r : ℤ) :
    (a+c+centered m r)%m=(a+c+r)%m := by
  unfold centered
  split
  · rfl
  · rw [show a+c+(r-m)=a+c+r-m by ring, Int.sub_emod_right]

/-- The folded lookup covers every admissible offset in an arbitrary finite
negation-stable right table, and every emitted offset belongs to that table.
The predicate may also specify a power equality or a particular matching sum. -/
theorem stored_coverage {m a c w : ℤ} (mp : 0<m) (wm : w<m)
    (right : Finset ℤ) (inside : ∀ r∈right, 0≤r ∧ r<m)
    (stable : ∀ r∈right, (if r=0 then 0 else m-r)∈right) (P : ℤ → Prop) :
    (∃ r∈right, (a+c+r)%m≤w ∧ P ((a+c+r)%m)) ↔
      ∃ t∈stored m right, ∃ (k : ℤ) (plus : Bool),
        wrapWindow m a c w k ∧ rankWindow m (a+c-k*m) w plus t ∧
        P (a+c-k*m+signedRank plus t) := by
  constructor
  · rintro ⟨r,hr,hw,hP⟩
    obtain ⟨r0,rm⟩ := inside r hr
    let z := centered m r
    let k := (a+c+z)/m
    have same : (a+c+z)%m=(a+c+r)%m := centered_mod ..
    have division := Int.emod_add_ediv (a+c+z) m
    rw [same, mul_comm m] at division
    have offset : a+c-k*m+z=(a+c+r)%m := by
      change (a+c+r)%m+k*m=a+c+z at division
      omega
    have x0 := Int.emod_nonneg (a+c+r) mp.ne'
    have witness : |z|∈stored m right := mem_image.mpr ⟨r,hr,rfl⟩
    by_cases pos : 2*r≤m
    · have hz : z=r := if_pos pos
      rw [hz,abs_of_nonneg r0] at witness
      rw [hz] at offset
      have ok : rankWindow m (a+c-k*m) w true r := by
        simp only [rankWindow,↓reduceIte,max_le_iff,le_min_iff]
        omega
      exact ⟨r,witness,k,true,wrap_of_rank mp ok,ok,offset.symm ▸ hP⟩
    · have hz : z=r-m := if_neg pos
      have mag : |z|=m-r := by rw [hz,abs_of_neg (show r-m<0 by omega)]; omega
      rw [mag] at witness
      have sign : signedRank false (m-r)=z := by simp [signedRank,hz]
      have ok : rankWindow m (a+c-k*m) w false (m-r) := by
        simp only [rankWindow,Bool.false_eq_true,↓reduceIte,max_le_iff,le_min_iff]
        rw [hz] at offset
        omega
      exact ⟨m-r,witness,k,false,wrap_of_rank mp ok,ok,by rwa [sign,offset]⟩
  · rintro ⟨t,ht,k,plus,_,hk,hP⟩
    obtain ⟨r,hr,rfl⟩ := mem_image.mp ht
    obtain ⟨r0,rm⟩ := inside r hr
    let z := signedRank plus |centered m r|
    have ranged : 0≤a+c-k*m+z ∧ a+c-k*m+z≤w := by
      cases plus <;> simp only [z,signedRank,rankWindow,Bool.false_eq_true,↓reduceIte,
        max_le_iff,le_min_iff] at hk ⊢ <;> omega
    have represented : ∃ b∈right, (a+c+b)%m=(a+c+z)%m := by
      have other := stable r hr
      by_cases rzero : r=0
      · subst r
        refine ⟨0,hr,?_⟩
        cases plus <;> simp [z,signedRank,centered,mp.le]
      · rw [if_neg rzero] at other
        by_cases low : 2*r≤m
        · have cr : |centered m r|=r := by simp [centered,low,abs_of_nonneg r0]
          cases plus
          · refine ⟨m-r,other,?_⟩
            change (a+c+(m-r))%m=(a+c+signedRank false |centered m r|)%m
            rw [cr,show a+c+(m-r)=a+c+(-r)+m*1 by ring,Int.add_mul_emod_self_left]
            rfl
          · exact ⟨r,hr,by simp [z,signedRank,cr]⟩
        · have cr : |centered m r|=m-r := by
            rw [centered,if_neg low,abs_of_neg (show r-m<0 by omega)]; omega
          cases plus
          · refine ⟨r,hr,?_⟩
            change (a+c+r)%m=(a+c+signedRank false |centered m r|)%m
            rw [cr,show signedRank false (m-r)=r-m by simp [signedRank],
              show a+c+(r-m)=a+c+r-m by ring,Int.sub_emod_right]
          · exact ⟨m-r,other,by simp [z,signedRank,cr]⟩
    obtain ⟨b,hb,eb⟩ := represented
    have canonical : (a+c+z)%m=a+c-k*m+z := by
      rw [show a+c+z=(a+c-k*m+z)+m*k by ring,Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt ranged.1 (ranged.2.trans_lt wm)
    exact ⟨b,hb,by rw [eb,canonical]; exact ranged.2,by rwa [eb,canonical]⟩

/-- At an even midpoint or at zero only the positive branch is queried. -/
theorem self_opposite_singleton {m offset width t : ℤ}
    (fixed : t=0 ∨ 2*t=m) : ¬rankWindow m offset width false t := by
  simp only [rankWindow,Bool.false_eq_true,↓reduceIte,max_le_iff,le_min_iff]
  omega

/-- Moving the nearest period multiple to the query preserves the global signature
for either sign, even for negative query exponents. -/
theorem oriented_signature (g : Rˣ) (E a c k m z : ℤ) :
    g^(E-a-c+k*m)=g^z ↔ g^E=g^(a+c-k*m+z) := by
  have eq : E=(a+c-k*m)+(E-a-c+k*m) := by ring
  calc g^(E-a-c+k*m)=g^z
      ↔ g^(a+c-k*m)*g^(E-a-c+k*m)=g^(a+c-k*m)*g^z := (mul_right_inj _).symm
    _ ↔ g^E=g^(a+c-k*m+z) := by rw [← zpow_add,←zpow_add,←eq]

end PrimeFactors.TraceFoldedRight
