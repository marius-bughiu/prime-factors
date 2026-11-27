import PrimeFactors.RectangularSearchFloor
import PrimeFactors.FareyWork

/-! Many distinct products of comparable odd coprime weights lie immediately
below different squares. This counts values emitted by the exact generator. -/
namespace PrimeFactors.RectangularDistinctProducts
open Finset RectangularSearchFloor RectangularFullWidth
set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

@[irreducible] def width : ℕ := 2^168

/-- Lift a reduced residue x in [1,j] to an odd residue in [1,2j]. -/
def lift (x j : ℕ) := if x%2=1 then x else x+j

private theorem lift_spec {x j : ℕ} (xp : 0<x) (xj : x≤j) (cop : x.Coprime j) :
    0<lift x j ∧ lift x j≤2*j ∧ Odd (lift x j) ∧ (lift x j).Coprime j := by
  by_cases odd : x%2=1
  · simpa [lift,odd,Nat.odd_iff] using
      (show 0<x ∧ x≤2*j ∧ x%2=1 ∧ x.Coprime j from ⟨xp,by omega,odd,cop⟩)
  · have parity : Odd j := by
      apply Nat.coprime_two_left.mp
      exact cop.coprime_dvd_left (Nat.dvd_iff_mod_eq_zero.mpr (by omega))
    rw [lift,if_neg odd]
    refine ⟨by omega,by omega,Nat.odd_iff.mpr ?_,Nat.coprime_add_self_left.mpr cop⟩
    have := Nat.odd_iff.mp parity
    omega

abbrev Input := Fin width × ↥(FareyWork.primitiveOffsets width)

def low (i : Input) : ℕ :=
  2*(width+i.1.val)*i.2.val.2+lift i.2.val.1 i.2.val.2

def center (i : Input) := low i+i.2.val.2
def product (i : Input) := low i*(low i+2*i.2.val.2)

private theorem coordinates {K : ℕ} {z : ℕ × ℕ} (h : z∈FareyWork.primitiveOffsets K) :
    1 ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ K ∧ z.1.Coprime z.2 := by
  unfold FareyWork.primitiveOffsets at h
  obtain ⟨box,le,cop⟩ := mem_filter.mp h
  exact ⟨(mem_Icc.mp (mem_product.mp box).1).1,le,(mem_Icc.mp (mem_product.mp box).2).2,cop⟩

private theorem info (i : Input) :
    1 ≤ i.2.val.1 ∧ i.2.val.1 ≤ i.2.val.2 ∧ i.2.val.2 ≤ width ∧ i.2.val.1.Coprime i.2.val.2 :=
  @coordinates width i.2.val i.2.property

private theorem band (i : Input) :
    (center i-1)^2 ≤ product i ∧ product i < (center i)^2 := by
  let j := i.2.val.2
  have ⟨xp,xj,jw,_⟩ := info i
  have jp : 0<j := by dsimp [j]; omega
  have bound : j*j≤width*j := Nat.mul_le_mul_right j jw
  have off := Nat.zero_le (i.1.val*j)
  have ra := Nat.zero_le (lift i.2.val.1 j)
  have c : 0<center i := by unfold center; omega
  have eq : center i-1+1=center i := by omega
  have sq := congrArg (fun z : ℕ => z^2) eq
  change _≤low i*(low i+2*j) ∧ _<_
  have size : j^2 ≤ low i := by
    change j^2≤2*(width+i.1.val)*j+lift i.2.val.1 j
    nlinarith only [bound,off,ra,Nat.zero_le (width*j)]
  change (low i+j-1)^2≤_ ∧ _<(low i+j)^2
  change (low i+j-1+1)^2=(low i+j)^2 at sq
  constructor
  · nlinarith only [sq,size,show low i+j-1+1=low i+j by omega,jp]
  · change low i*(low i+2*j)<(low i+j)^2
    nlinarith only [Nat.mul_pos jp jp]

private theorem low_injective {i h : Input} (jEq : i.2.val.2=h.2.val.2)
    (eq : low i=low h) : i=h := by
  have ⟨xp,xj,_,cop⟩ := info i
  have ⟨yp,yj,_,cop'⟩ := info h
  obtain ⟨rp,ru,_,_⟩ := lift_spec xp xj cop
  obtain ⟨sp,su,_,_⟩ := lift_spec yp yj cop'
  unfold low at eq
  rw [jEq] at eq ru rp xj
  have limits (a b j r s : ℕ) (ab : a<b) (rp : 0<r) (ru : s≤2*j) :
      2*(width+a)*j+s<2*(width+b)*j+r := by
    have := Nat.mul_le_mul_right (2*j) (show width+a+1≤width+b by omega)
    nlinarith
  have times : i.1.val=h.1.val := by
    rcases lt_trichotomy i.1.val h.1.val with lt|same|gt
    · exact False.elim ((limits _ _ _ _ _ lt sp ru).ne eq)
    · exact same
    · exact False.elim ((limits _ _ _ _ _ gt rp su).ne eq.symm)
  rw [times] at eq
  have lifted := Nat.add_left_cancel eq
  unfold lift at lifted
  have xs : i.2.val.1=h.2.val.1 := by split at lifted <;> split at lifted <;> omega
  exact Prod.ext (Fin.ext times) (Subtype.ext (Prod.ext xs jEq))

theorem product_injective : Function.Injective product := by
  intro i h eq
  have ⟨l,r⟩ := band i
  have ⟨l',r'⟩ := band h
  have ord (i h : Input) (lt : center i<center h) : product i<product h :=
    (band i).2.trans_le ((Nat.pow_le_pow_left (show center i≤center h-1 by omega) 2).trans (band h).1)
  have same : center i=center h := by
    rcases lt_trichotomy (center i) (center h) with lt|s|gt
    · exact False.elim ((ord i h lt).ne eq)
    · exact s
    · exact False.elim ((ord h i gt).ne eq.symm)
  have gap (z : Input) : (center z)^2 = product z+z.2.val.2^2 := by
    unfold center product; ring
  have gi := gap i
  rw [same,eq,gap h] at gi
  have jEq : i.2.val.2=h.2.val.2 := (Nat.pow_left_inj (by decide : 2≠0)).mp (Nat.add_left_cancel gi).symm
  apply low_injective jEq
  unfold center at same
  omega

theorem eligible {limit e : ℕ} (kl : 2^680≤limit) (ep : 1≤e) (i : Input) :
    product i∈emitted limit 1024 e := by
  let j := i.2.val.2
  let a := low i
  have ⟨xp,xj,jw,cop⟩ := info i
  obtain ⟨rp,ru,odd,copr⟩ := lift_spec xp xj cop
  have jp : 0<j := by dsimp [j]; omega
  have size : width+i.1.val+1≤2*width := by have := i.1.isLt; omega
  have bound := Nat.mul_le_mul size jw
  have aw : a+2*j ≤ 2^340 := by
    change 2*(width+i.1.val)*j+lift i.2.val.1 j+2*j≤_
    change lift i.2.val.1 j≤2*j at ru
    change (width+i.1.val+1)*j≤2*width*width at bound
    have jw' : j≤width := jw
    nlinarith only [bound,ru,jw',show 4*width*width+2*width≤2^340 by unfold width; decide +kernel]
  have cap : a*(a+2*j)≤limit := calc
    _ ≤ (2^340)*(2^340) := Nat.mul_le_mul (by omega) aw
    _ ≤ limit := by omega
  have ap : 0<a := by dsimp [a,low]; omega
  have ag : a.Coprime j := by
    change (2*(width+i.1.val)*j+lift i.2.val.1 j).Coprime j
    exact (Nat.coprime_mul_right_add_left ..).mpr copr
  have ao : Odd a := by
    apply Nat.odd_iff.mpr
    have h := Nat.odd_iff.mp odd
    change (2*(width+i.1.val)*j+lift i.2.val.1 j)%2=1
    change lift i.2.val.1 j % 2 = 1 at h
    rw [Nat.mul_assoc,Nat.add_mod,Nat.mul_mod_right]; simpa using h
  have pair : a.Coprime (a+2*j) :=
    Nat.coprime_self_add_right.mpr (Nat.Coprime.mul_right (Nat.coprime_two_right.mpr ao) ag)
  have ratio : a+2*j≤(1024+e)*a/1024 := by
    apply (Nat.le_div_iff_mul_le (by decide)).mpr
    have ea : a≤e*a := by simpa using Nat.mul_le_mul_right a ep
    have large := Nat.mul_le_mul_right j (show 2048≤2*width by unfold width; decide)
    have off := Nat.zero_le (i.1.val*j)
    change 2048*j≤2*width*j at large
    have growing : 2048*j≤a := by
      change _ ≤ 2*(width+i.1.val)*j+lift i.2.val.1 j
      nlinarith only [large,off,Nat.zero_le (lift i.2.val.1 j)]
    nlinarith only [growing,ea]
  have cutoff : a+2*j≤limit/a := (Nat.le_div_iff_mul_le ap).mpr (by rwa [Nat.mul_comm (a+2*j)])
  have sa : a≤limit.sqrt := Nat.le_sqrt.mpr ((Nat.mul_le_mul_left a (show a≤a+2*j by omega)).trans cap)
  apply mem_union_left
  apply mem_biUnion.mpr
  refine ⟨a,mem_filter.mpr ⟨mem_Icc.mpr ⟨ap,sa⟩,Nat.odd_iff.mp ao⟩,?_⟩
  apply mem_image.mpr
  refine ⟨a+2*j,mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, le_min (by simpa using cutoff) ratio⟩,?_⟩,?_⟩
  · exact ⟨by omega,pair⟩
  · simp [product,a,j]

/-- The baseline generator emits at least 2^501 different multipliers on
every full-width product in the stated input class. -/
theorem count_at {limit e : ℕ} (kl : 2^680≤limit) (ep : 1≤e) :
    2^501 ≤ (emitted limit 1024 e).card := by
  let emb : Input ↪ ↥(emitted limit 1024 e) :=
    ⟨fun i => ⟨product i,eligible kl ep i⟩,
      fun _ _ h => product_injective (congrArg Subtype.val h)⟩
  have count := Fintype.card_le_of_embedding emb
  simp only [Input,Fintype.card_prod,Fintype.card_fin,Fintype.card_coe] at count
  have src := FareyWork.primitive_count width
  have enough : 2^333 ≤ (FareyWork.primitiveOffsets width).card := by
    rw [show width^2=(2^168)^2 by unfold width; rfl] at src
    omega
  exact (show 2^501=width*2^333 by unfold width; decide +kernel) ▸ (Nat.mul_le_mul_left width enough).trans count

private theorem included {small large stop e : ℕ} (sl : small ≤ large) (ss : small < stop) :
    emitted small 1024 e ⊆ (emitted large 1024 e).filter (· < stop) := by
  intro k hk
  exact mem_filter.mpr ⟨emitted_mono (K:=small) (L:=large) (scale:=1024) (e:=e) sl hk,
    (emitted_le (K:=small) (scale:=1024) (e:=e) hk).trans_lt ss⟩
private theorem prefixAny {small large stop e goal : ℕ} (sl : small ≤ large) (ss : small < stop)
    (src : goal ≤ (emitted small 1024 e).card) :
    goal ≤ ((emitted large 1024 e).filter (· < stop)).card :=
  src.trans (card_le_card (included sl ss))
/-- Count distinct visits in the full generator before a specified index. -/
theorem prefix_visits {limit stop e : ℕ} (large : 2^680 ≤ limit) (late : 2^680 < stop) (ep : 1 ≤ e) :
    2^501 ≤ ((emitted limit 1024 e).filter (· < stop)).card :=
  prefixAny (small:=2^680) (large:=limit) (stop:=stop) (e:=e) (goal:=2^501) large late
    (count_at (limit:=2^680) (e:=e) le_rfl ep)

theorem full_width {p q : ℕ} (lt : p<q) (qu : q<2^1024)
    (lo : 2^2047≤p*q) (hi : p*q<2^2048) :
    2^501 ≤ (emitted (K (p*q)) 1024 (excess (p*q))).card :=
  count_at (dimensions lo hi).2.2.2.2.2.1 (positive_excess lt qu lo hi)

end PrimeFactors.RectangularDistinctProducts
