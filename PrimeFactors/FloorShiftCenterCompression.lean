import PrimeFactors.FloorShiftDyadicCenters
import PrimeFactors.FactorEndingDecoder
import PrimeFactors.TwoMaximalClueSuffixes

/-! A shared binary root locates all viable lower centers for the dyadic reading. -/
namespace PrimeFactors.FloorShiftCenterCompression

open Finset FloorSquareShift
open private PrimeFactors.FactorEndingDecoder.unit_spec from PrimeFactors.FactorEndingDecoder
open private PrimeFactors.TwoMaximalClueSuffixes.root_signs from PrimeFactors.TwoMaximalClueSuffixes

/-- A single lifted unit root serves all exponents through the width limit. -/
def sharedRoot (N b : ℕ) : ℤ :=
  if N%8=1 then FactorEndingDecoder.unitRoot N (b-2) else 0

/-- Distance down from r to the last representative of class a modulo 2^j. -/
def distance (r j : ℕ) (a : ℤ) : ℕ := (((r:ℤ)-a)%(2:ℤ)^j).toNat

/-- Distances to check. Only levels one and two can contribute at other odd residues mod 8. -/
noncomputable def offsets (N r j : ℕ) (u : ℤ) : Finset ℕ :=
  if j=1 then {0}
  else if j=2 then {0,1}
  else if N%8=1 then
    let a := u+2^(j-1)
    {distance r j a, distance r j (-a)}
  else ∅

/-- Remaining public comparisons include one low-bit check on the remainder.
A shift proposing a sum outside the promised open interval is discarded. -/
noncomputable def row (N r b j : ℕ) (u : ℤ) : Finset ℕ :=
  (((offsets N r j u).filter (fun e => e≤r ∧ 2*e<2^j ∧
      2*(r-e)+2^j<2^(b+1) ∧ (N-(r-e)^2)%2^(j+1)=2^j)).image (fun e => r-e))

theorem card_row (N r b j : ℕ) (u : ℤ) : (row N r b j u).card≤2 := by
  refine card_image_le.trans ((card_filter_le ..).trans ?_)
  unfold offsets
  split_ifs <;> simp
  exact (card_insert_le ..).trans (by simp)

private theorem shifted_root {N b j : ℕ} (lo : 3≤j) (hi : j≤b) (gate : N%8=1) :
    let a := sharedRoot N b+(2:ℤ)^(j-1)
    Odd a ∧ a^2 ≡ (N:ℤ)-2^j [ZMOD (2:ℤ)^(j+1)] := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le lo
  have base : (8:ℤ)∣(N:ℤ)-1 := Int.modEq_iff_dvd.mp
    (Int.natCast_modEq_iff.mpr (show 1 ≡ N [MOD 8] from gate.symm))
  obtain ⟨⟨v,hv⟩,deep⟩ := PrimeFactors.FactorEndingDecoder.unit_spec base (b-2)
  let u := FactorEndingDecoder.unitRoot N (b-2)
  change u=2*v+1 at hv
  have div : (2:ℤ)^(i+4)∣(N:ℤ)-u^2 :=
    (pow_dvd_pow 2 (by omega : i+4≤b-2+3)).trans deep
  obtain ⟨z,hz⟩ := div
  simp only [sharedRoot,if_pos gate,show 3+i-1=i+2 by omega,show 3+i=i+3 by omega,
    show i+3+1=i+4 by omega,show i+3-1=i+2 by omega,pow_add] at *
  change Odd (u+2^i*2^2) ∧ (u+2^i*2^2)^2 ≡ (N:ℤ)-2^i*2^3 [ZMOD (2:ℤ)^i*2^4]
  constructor
  · exact ⟨v+2*2^i,by rw [hv]; ring⟩
  · refine Int.modEq_iff_dvd.mpr ⟨z-v-(2:ℤ)^i-1,?_⟩
    linear_combination hz - 8*(2:ℤ)^i*hv

private theorem distance_eq {r s j : ℕ} {a : ℤ} (le : s≤r) (close : r-s<2^j)
    (cls : (s:ℤ) ≡ a [ZMOD (2:ℤ)^j]) : distance r j a=r-s := by
  have eq := (Int.ModEq.refl (r:ℤ)).sub cls
  change ((r:ℤ)-s)%(2:ℤ)^j=((r:ℤ)-a)%(2:ℤ)^j at eq
  unfold distance
  rw [←eq,←Nat.cast_sub le,Int.emod_eq_of_lt (by positivity) (by exact_mod_cast close)]
  simp

private theorem residue_info {N r s j : ℕ} (odd : Odd N) (rs : r^2≤N) (sr : s≤r)
    (lo : 3≤j) (res : (N-s^2)%2^(j+1)=2^j) :
    N%8=1 ∧ (s:ℤ)^2 ≡ (N:ℤ)-2^j [ZMOD (2:ℤ)^(j+1)] := by
  have sq := (Nat.pow_le_pow_left sr 2).trans rs
  have div := Nat.mod_add_div (N-s^2) (2^(j+1))
  rw [res] at div
  have eq : N=s^2+2^j+2^(j+1)*((N-s^2)/2^(j+1)) := by omega
  have eight : 8∣(2:ℕ)^j := pow_dvd_pow 2 lo
  have next : 8∣(2:ℕ)^(j+1) := pow_dvd_pow 2 (by omega : 3≤j+1)
  have smod : N%8=(s%8)^2%8 := by
    conv_lhs => rw [eq,Nat.add_mod,Nat.mul_mod,Nat.mod_eq_zero_of_dvd next,
      zero_mul,Nat.zero_mod,add_zero,Nat.mod_mod,Nat.add_mod,Nat.mod_eq_zero_of_dvd eight,
      add_zero,Nat.mod_mod,Nat.pow_mod]
  constructor
  · have no := Nat.odd_iff.mp odd
    have parity := Nat.mod_mod_of_dvd N (show 2∣8 by decide)
    have slim := Nat.mod_lt s (by decide : 0<8)
    generalize ha : s%8=a at smod slim
    interval_cases a <;> norm_num at smod <;> omega
  · let c := (N-s^2)/2^(j+1)
    have eqZ : (N:ℤ)=(s:ℤ)^2+2^j+2^(j+1)*(c:ℤ) := by exact_mod_cast eq
    refine Int.modEq_iff_dvd.mpr ⟨c,?_⟩
    linear_combination eqZ

/-- At all high levels the two explicit classes themselves certify the remainder
test, so a generator may omit that redundant check. -/
theorem residue_classes {N r s b j : ℕ} (odd : Odd N) (rs : r^2≤N) (sr : s≤r)
    (lo : 3≤j) (hi : j≤b) :
    let a := sharedRoot N b+(2:ℤ)^(j-1)
    (N-s^2)%2^(j+1)=2^j ↔ N%8=1 ∧
      ((s:ℤ) ≡ a [ZMOD (2:ℤ)^j] ∨ (s:ℤ) ≡ -a [ZMOD (2:ℤ)^j]) := by
  dsimp only
  constructor
  · intro res
    obtain ⟨gate,h⟩ := residue_info odd rs sr lo res
    obtain ⟨ao,root⟩ := shifted_root lo hi gate
    exact ⟨gate,(PrimeFactors.TwoMaximalClueSuffixes.root_signs (by omega) _ _ ao).mp
      (h.trans root.symm)⟩
  · rintro ⟨gate,cls⟩
    obtain ⟨ao,root⟩ := shifted_root lo hi gate
    have h := ((PrimeFactors.TwoMaximalClueSuffixes.root_signs (by omega) _ _ ao).mpr cls).trans root
    have sq := (Nat.pow_le_pow_left sr 2).trans rs
    have hn : N-s^2 ≡ 2^j [MOD 2^(j+1)] := by
      rw [←Int.natCast_modEq_iff]
      push_cast [sq]
      apply Int.modEq_iff_dvd.mpr
      convert dvd_neg.mpr (Int.modEq_iff_dvd.mp h) using 1
      ring
    change (N-s^2)%2^(j+1)=2^j%2^(j+1) at hn
    rw [Nat.mod_eq_of_lt (by rw [pow_succ]; have := Nat.two_pow_pos j; omega :
      (2:ℕ)^j<2^(j+1))] at hn
    exact hn

/-- At every exponent in the inclusive range, the generated centers are exactly
those giving a viable dyadic reading at that exponent. -/
theorem mem_row {N r b j s : ℕ} (odd : Odd N) (rs : r^2≤N) (jp : 1≤j) (hi : j≤b) :
    s∈row N r b j (sharedRoot N b) ↔ s≤r ∧ 2*r<2*s+2^j ∧
      2*s+2^j<2^(b+1) ∧ (N-s^2)%2^(j+1)=2^j := by
  simp only [row,mem_image,mem_filter]
  constructor
  · rintro ⟨e,⟨_,le,low,top,res⟩,rfl⟩
    exact ⟨by omega,by omega,top,res⟩
  · rintro ⟨sr,low,top,res⟩
    have close : 2*(r-s)<2^j := by omega
    have below : r-s<2^j := by omega
    refine ⟨r-s,⟨?_,by omega,close,by simpa [Nat.sub_sub_self sr] using top,
      by simpa [Nat.sub_sub_self sr] using res⟩,Nat.sub_sub_self sr⟩
    by_cases j1 : j=1
    · simp [offsets,j1,show r-s=0 by rw [j1] at close; omega]
    by_cases j2 : j=2
    · have opts : r-s=0 ∨ r-s=1 := by rw [j2] at close; omega
      simpa [offsets,j1,j2] using opts
    have lo : 3≤j := by omega
    obtain ⟨gate,signs⟩ := (residue_classes odd rs sr lo hi).mp res
    simp only [offsets,if_neg j1,if_neg j2,if_pos gate,mem_insert,mem_singleton]
    exact signs.imp (fun h => (distance_eq sr below h).symm) (fun h => (distance_eq sr below h).symm)

/-- The modular test is exactly the largest-power-of-two test, including zero
under the gcd convention, at every positive exponent. -/
theorem part_iff (D : ℕ) {j : ℕ} (jp : 1≤j) :
    twoPart D=2^j ↔ D%2^(j+1)=2^j := by
  have room : (2:ℕ)^j<2^(j+1) := by rw [pow_succ]; have := Nat.two_pow_pos j; omega
  constructor
  · intro part
    by_cases zero : D=0
    · subst D
      have eq : 2^0=2^j := by simpa [twoPart] using part
      have := (Nat.pow_right_inj (by decide : 1<(2:ℕ))).mp eq
      omega
    obtain ⟨i,m,odd,dec⟩ := Nat.exists_eq_two_pow_mul_odd zero
    rw [dec,mul_comm (2^i) m,twoPart_odd_mul i odd] at part
    have same := (Nat.pow_right_inj (by decide : 1<(2:ℕ))).mp part
    subst i
    obtain ⟨a,rfl⟩ := odd
    rw [dec,show (2:ℕ)^j*(2*a+1)=2^j+a*2^(j+1) by rw [pow_succ]; ring,
      Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt room]
  · intro res
    let z := D/2^(j+1)
    have eqn := Nat.mod_add_div D (2^(j+1))
    rw [res,pow_succ] at eqn
    have eq : D=(2*z+1)*2^j := by
      change 2^j+2^j*2*z=D at eqn
      rw [←eqn]; ring
    rw [eq,twoPart_odd_mul j (show Odd (2*z+1) from ⟨z,rfl⟩)]

/-- Distinct candidate sums across every exponent. The shared root and floor
square root are evaluated once before constructing the rows. -/
noncomputable def sums (N b : ℕ) : Finset ℕ :=
  let u := sharedRoot N b
  let r := N.sqrt
  (range b).biUnion fun i =>
    (row N r b (i+1) u).image (fun s => 2*s+2^(i+1))

theorem card_sums (N b : ℕ) : (sums N b).card≤2*b := by
  unfold sums
  calc
    _ ≤ (range b).card*2 := card_biUnion_le_card_mul _ _ _ (fun _ _ =>
      card_image_le.trans (card_row ..))
    _ = 2*b := by simp [mul_comm]

/-- The compressed list retains a true reading at any nonnegative center,
including a possible reading at the last exponent b. Every listed sum comes
from exactly the original rule at some center; different centers may agree. -/
theorem mem_sums {N b S : ℕ} (odd : Odd N) (evenS : Even S)
    (low : 2*N.sqrt<S) (top : S<2^(b+1)) :
    S∈sums N b ↔ ∃ s≤N.sqrt, FloorShiftDyadicCenters.proposed N s=S := by
  simp only [sums,mem_biUnion,mem_range,mem_image]
  constructor
  · rintro ⟨i,ib,s,valid,eq⟩
    obtain ⟨sr,_,_,res⟩ := (mem_row odd (Nat.sqrt_le' N) (by omega) (by omega)).mp valid
    exact ⟨s,sr,by rw [FloorShiftDyadicCenters.proposed,(part_iff _ (by omega)).mpr res,eq]⟩
  · rintro ⟨s,sr,hs⟩
    obtain ⟨j,hj,_⟩ := FloorShiftDyadicCenters.power_divisor (N-s^2)
    rw [FloorShiftDyadicCenters.proposed,hj] at hs
    have jp : 0<j := by
      by_contra! zero
      have : j=0 := by omega
      obtain ⟨v,hv⟩ := evenS
      simp [this] at hs
      omega
    have cap : 2^j<2^(b+1) := by omega
    have jb := (Nat.pow_lt_pow_iff_right (by decide : 1<(2:ℕ))).mp cap
    obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero jp.ne'
    refine ⟨i,by omega,s,(mem_row odd (Nat.sqrt_le' N) (by omega) (by omega)).mpr ?_,hs⟩
    exact ⟨sr,hs ▸ low,hs ▸ top,(part_iff _ (by omega)).mp hj⟩

/-- Distinct odd factors automatically satisfy the lower sum cutoff. -/
theorem true_sum {p q b : ℕ} (lt : p<q) (po : Odd p) (qo : Odd q) (width : q<2^b) :
    p+q∈sums (p*q) b ↔
      ∃ s≤(p*q).sqrt, FloorShiftDyadicCenters.proposed (p*q) s=p+q := by
  have sq := Nat.sqrt_le' (p*q)
  have low : 2*(p*q).sqrt<p+q := by
    apply (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp
    have gap : (0:ℤ)<(q:ℤ)-p := by omega
    zify at sq ⊢
    nlinarith only [sq,sq_pos_of_pos gap]
  exact mem_sums (po.mul qo) (po.add_odd qo) low (by rw [pow_succ]; omega)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
/-- Small direct computations exercise both low levels and the last exponent. -/
theorem controls :
    sums 35 3={12} ∧ sums 21 3={10} ∧
    163*227=37001 ∧ row 37001 192 8 8 (sharedRoot 37001 8)={67} ∧
    2*67+2^8=163+227 := by decide +kernel

/-- The matched nine-bit cases exercise both multiple candidates at one
exponent and the same sum arising at different exponents. -/
theorem matched_controls :
    sums 138953 9={746,762,774,838,954} ∧ sums 141217 9={754,766,802,862} := by
  constructor
  · rw [sums,show (138953:ℕ).sqrt=372 by norm_num]
    decide +kernel
  · rw [sums,show (141217:ℕ).sqrt=375 by norm_num]
    decide +kernel

end PrimeFactors.FloorShiftCenterCompression
