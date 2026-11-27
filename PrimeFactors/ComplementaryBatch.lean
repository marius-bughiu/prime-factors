import PrimeFactors.ComplementaryKeys
import PrimeFactors.TwelveSeedBirthday

namespace PrimeFactors.ComplementaryBatch
open Finset TwelveSeedBirthday TwelveResidueCollision TwelveImageSize ComplementaryKeys
open scoped BigOperators

private theorem large_char {p : ℕ} [Fact p.Prime] (big : 864<p) : (108:ZMod p)≠0 := by
  exact_mod_cast (show ((108:ℕ):ZMod p)≠0 by
    rw [Ne,ZMod.natCast_zmod_eq_zero_iff_dvd]
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega))

/-- Centering the keys at one half turns the extra comparison into
opposite roots of the same split polynomial. Every pair, including
a position with itself, then enters a single public gcd. -/
noncomputable def directedProduct {n : ℕ} [NeZero n] {m : ℕ} (x : Fin m → Input n) : ZMod n :=
  ∏ i, ∏ j, (-(2*publicKey (x i)-1) - (2*publicKey (x j)-1))

private noncomputable def localProduct {p : ℕ} [Fact p.Prime] {m : ℕ} (x : Fin m → Seed p) : ZMod p :=
  ∏ i, ∏ j, (-(2*value (x i).val-1) - (2*value (x j).val-1))

private theorem local_zero_iff {p m : ℕ} [Fact p.Prime] (big : 864<p) (x : Fin m → Seed p) :
    localProduct x=0 ↔ ∃ i j, value (x j).val=1-value (x i).val := by
  have two : (2:ZMod p)≠0 := fun z => large_char big (by linear_combination 54*z)
  have term (a b : ZMod p) : -(2*a-1)-(2*b-1)=0 ↔ b=1-a := by
    rw [show -(2*a-1)-(2*b-1) = 2*((1-a)-b) by ring,mul_eq_zero]
    simp only [two,false_or,sub_eq_zero]
    exact eq_comm
  simp only [localProduct,Finset.prod_eq_zero_iff,Finset.mem_univ,true_and,term]

private theorem coord {p q m : ℕ} [Fact p.Prime] [Fact q.Prime]
    (bp : 864<p) (bq : 864<q) (cop : p.Coprime q) (x : Fin m → Input (p*q)) :
    ZMod.chineseRemainder cop (directedProduct x) =
      (localProduct (fun i => (seedEquiv cop (x i)).1),
       localProduct (fun i => (seedEquiv cop (x i)).2)) := by
  apply Prod.ext
  · let f := (RingHom.fst (ZMod p) (ZMod q)).comp (ZMod.chineseRemainder cop).toRingHom
    have h (i : Fin m) : f (publicKey (x i))=value ((seedEquiv cop (x i)).1).val :=
      congrArg Prod.fst (coordinates bp bq cop (x i))
    change f (directedProduct x) = _
    simp [directedProduct,localProduct,map_ofNat,h]
  · let f := (RingHom.snd (ZMod p) (ZMod q)).comp (ZMod.chineseRemainder cop).toRingHom
    have h (i : Fin m) : f (publicKey (x i))=value ((seedEquiv cop (x i)).2).val :=
      congrArg Prod.snd (coordinates bp bq cop (x i))
    change f (directedProduct x) = _
    simp [directedProduct,localProduct,map_ofNat,h]

/-- Orientation can be fixed in the proof after using the public residue
test. The algorithm does not have to know which of the two primes is p. -/
theorem exact_gcd {p q m : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (bp : 864<p) (bq : 864<q) (cop : p.Coprime q) (no : ¬IsSquare (3:ZMod q))
    (x : Fin m → Input (p*q)) :
    let seeds := fun i => (seedEquiv cop (x i)).1
    let eligible :=  ∃ i j, value (seeds j).val=1-value (seeds i).val
    (eligible → (p*q).gcd (directedProduct x).val=p) ∧
    (¬eligible → (p*q).gcd (directedProduct x).val=1) := by
  intro seeds eligible
  have public := coord bp bq cop x
  let k := (directedProduct x).val
  have cast : ZMod.chineseRemainder cop (k : ZMod (p*q)) =
    (localProduct seeds,localProduct (fun i => (seedEquiv cop (x i)).2)) := by
    simpa [k,seeds] using public
  have pa : (k : ZMod p)=localProduct seeds := by
    simpa only [map_natCast,Prod.fst_natCast] using congrArg Prod.fst cast
  have qa : (k : ZMod q)=localProduct (fun i => (seedEquiv cop (x i)).2) := by
    simpa only [map_natCast,Prod.snd_natCast] using congrArg Prod.snd cast
  have atP : p∣k ↔ eligible := by rw [←ZMod.natCast_zmod_eq_zero_iff_dvd,pa,local_zero_iff bp]
  have atQ : ¬q∣k := by
    rw [←ZMod.natCast_zmod_eq_zero_iff_dvd,qa,local_zero_iff bq]
    rintro ⟨i,j,eq⟩
    exact no (complement_implies_square (large_char bq)
      (mem_filter.mp ((seedEquiv cop (x i)).2.property)).2 eq)
  have cancelled : (p*q).gcd k=p.gcd k := by
    rw [Nat.mul_comm p q]
    exact Nat.Coprime.gcd_mul_left_cancel p (hq.out.coprime_iff_not_dvd.mpr atQ)
  refine ⟨fun yes => cancelled.trans (Nat.gcd_eq_left (atP.mpr yes)), ?_⟩
  exact fun none => cancelled.trans (hp.out.coprime_iff_not_dvd.mpr (fun h => none (atP.mp h))).gcd_eq_one

/-- At a nonmiddle first seed, the collapsed label's number of
proper partners exceeds the original count by exactly twelve times
the nonsquare-side regular population minus twenty-four. -/
theorem partners_gain {r s : ℕ} (hr : 24≤r) (hs : 24≤s) :
    (24*(s-12)+(r-24)*12) = 12*(s-12)+(r-12)*12+12*(s-24) := by omega

end PrimeFactors.ComplementaryBatch
