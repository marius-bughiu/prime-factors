import PrimeFactors.TwelveImageSize
import PrimeFactors.UniformFiberBirthday

namespace PrimeFactors.TwelveSeedBirthday
open Finset TwelveResidueCollision TwelveImageSize UniformFiberBirthday

set_option maxHeartbeats 800000
set_option exponentiation.threshold 2050

abbrev Seed (p : ℕ) [NeZero p] := ↥(regulars p)
abbrev Label (p : ℕ) [NeZero p] := ↥(keys (ZMod p))

/-- Product-only test for a regular input. -/
noncomputable def inputs (n : ℕ) [NeZero n] : Finset (ZMod n) := by
  classical exact univ.filter fun x => IsUnit (mask x)

abbrev Input (n : ℕ) [NeZero n] := ↥(inputs n)

private theorem input_unit {n : ℕ} [NeZero n] (x : Input n) : IsUnit (mask x.val) :=
  (mem_filter.mp x.property).2

private theorem unit_map {R S : Type*} [CommRing R] [CommRing S] (e : R →+* S) {x : R}
    (unit : IsUnit (mask x)) : IsUnit (mask (e x)) := by
  simpa [mask,map_ofNat] using unit.map e

/-- Equality of prime-coordinate pairs is the ordinary CRT bijection
restricted to inputs passing the publicly evaluable unit-mask test. -/
noncomputable def seedEquiv {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q) :
    Input (p*q) ≃ Seed p × Seed q := by
  let e := ZMod.chineseRemainder cop
  refine ⟨fun x => ?_, fun z => ?_, ?_, ?_⟩
  · have h := Prod.isUnit_iff.mp (unit_map e.toRingHom (input_unit x))
    exact (⟨(e x.val).1,mem_filter.mpr ⟨mem_univ _,isUnit_iff_ne_zero.mp h.1⟩⟩,
           ⟨(e x.val).2,mem_filter.mpr ⟨mem_univ _,isUnit_iff_ne_zero.mp h.2⟩⟩)
  · let v := (z.1.val,z.2.val)
    have h : IsUnit (mask v) := Prod.isUnit_iff.mpr
      ⟨isUnit_iff_ne_zero.mpr (mem_filter.mp z.1.property).2,
       isUnit_iff_ne_zero.mpr (mem_filter.mp z.2.property).2⟩
    exact ⟨e.symm v,mem_filter.mpr ⟨mem_univ _,unit_map e.symm.toRingHom h⟩⟩
  · intro x
    exact Subtype.ext (e.symm_apply_apply _)
  · intro z
    exact Prod.ext (Subtype.ext (congrArg Prod.fst (e.apply_symm_apply _)))
      (Subtype.ext (congrArg Prod.snd (e.apply_symm_apply _)))

noncomputable def label {p : ℕ} [Fact p.Prime] (big : 864<p) (x : Seed p) : Label p :=
  ⟨value x.val,by rw [prime_keys big]; exact mem_image_of_mem _ x.property⟩

theorem label_fiber {p : ℕ} [Fact p.Prime] (big : 864<p) (z : Label p) :
    Nat.card {x : Seed p // label big x=z} = 12 := by
  classical
  have hz : z.val ∈ (regulars p).image value :=
    (congrArg (fun s : Finset (ZMod p) => z.val ∈ s) (prime_keys big)).mp z.property
  obtain ⟨a,ha,eq⟩ := mem_image.mp hz
  have iff (y : ZMod p) (hy : y∈regulars p) :
      value y=z.val ↔ num a*den y=num y*den a := by
    rw [←eq]
    have char : (108:ZMod p) ≠ 0 := by
      exact_mod_cast (show ((108:ℕ):ZMod p) ≠ 0 by
        rw [Ne,ZMod.natCast_zmod_eq_zero_iff_dvd]
        exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
    exact (div_eq_div_iff ((regular_iff char y).mp (mem_filter.mp hy).2).1
      ((regular_iff char a).mp (mem_filter.mp ha).2).1).trans eq_comm
  let e : {x : Seed p // label big x=z} ≃
      ↥((regulars p).filter fun y => num a*den y=num y*den a) :=
    { toFun := fun x => ⟨x.1.1,mem_filter.mpr ⟨x.1.2,(iff _ x.1.2).mp (congrArg Subtype.val x.2)⟩⟩
      invFun := fun y => ⟨⟨y.1,(mem_filter.mp y.2).1⟩,
        Subtype.ext ((iff _ (mem_filter.mp y.2).1).mpr (mem_filter.mp y.2).2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe,regular_fiber big ha]

/-- The value actually computed before the factors are known. -/
noncomputable def publicKey {n : ℕ} [NeZero n] (x : Input n) : ZMod n :=
  num x.val * (den x.val)⁻¹

private theorem public_key_eq {n : ℕ} [NeZero n] (x : Input n) :
    publicKey x * den x.val = num x.val := by
  have unit := input_unit x
  simp [mask] at unit
  have h : IsUnit (x.val^2+3) := by tauto
  have hd : IsUnit (den x.val) := h.pow 6
  rw [publicKey,mul_assoc,ZMod.inv_mul_of_unit _ hd,mul_one]

/-- Reducing the public key at either prime gives precisely the local label. -/
theorem coordinates {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : 864<p) (hq : 864<q) (cop : p.Coprime q) (x : Input (p*q)) :
    ZMod.chineseRemainder cop (publicKey x) =
     ((label hp ((seedEquiv cop x).1)).val,(label hq ((seedEquiv cop x).2)).val) := by
  have coord {r : ℕ} [Fact r.Prime] (h : 864<r) (e : ZMod (p*q) →+* ZMod r) :
      e (publicKey x)=value (e x.val) := by
    have unit := isUnit_iff_ne_zero.mp (unit_map e (input_unit x))
    have char : (108:ZMod r) ≠ 0 := by
      exact_mod_cast (show ((108:ℕ):ZMod r) ≠ 0 by
        rw [Ne,ZMod.natCast_zmod_eq_zero_iff_dvd]
        exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
    apply (eq_div_iff ((regular_iff char _).mp unit).1).mpr
    simpa [num,den,sextic,map_ofNat] using congrArg e (public_key_eq x)
  exact Prod.ext (coord hp ((RingHom.fst _ _).comp (ZMod.chineseRemainder cop).toRingHom))
    (coord hq ((RingHom.snd _ _).comp (ZMod.chineseRemainder cop).toRingHom))

/-- Finite probability on independent uniform seed words, sampled with replacement. -/
noncomputable def odds {S B C : Type*} [Fintype S] (f : S → B × C) (m : ℕ) : ℝ :=
  (Nat.card {w : Fin m → S // ProperPair (f ∘ w)} : ℝ) / (Fintype.card S : ℝ)^m

private theorem transfer {S A B C : Type*} [Fintype S] [Fintype A]
    (e : S ≃ A) (f : A → B × C) (m : ℕ) : odds (f ∘ e) m = odds f m := by
  let ew := Equiv.arrowCongr (Equiv.refl (Fin m)) e
  have h := Nat.card_congr (Equiv.subtypeEquivOfSubtype (p:=fun v => ProperPair (f ∘ v)) ew)
  unfold odds
  rw [Fintype.card_congr e]
  exact congrArg (fun k : ℕ => (k:ℝ)/(Fintype.card A : ℝ)^m) h

private theorem prime_size {p : ℕ} [Fact p.Prime] (low : 2^1023≤p) (high : p<2^1024)
    (big : 864<p) : 2^1019 ≤ Fintype.card (Label p) ∧
      12*Fintype.card (Label p) ≤ 2^1024 := by
  apply image_bounds_of_twelve (label big) (label_fiber big) low high
  · simpa [Seed] using (regulars p).card_le_univ
  · simpa [Seed] using regular_count p

/-- Concrete product-residue experiment on the same uniform regular seeds.
The normalized-key chance exceeds 95%; the identity-key chance is at most 7/16. -/
theorem full_size {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (pl : 2^1023≤p) (ph : p<2^1024) (ql : 2^1023≤q) (qh : q<2^1024)
    (bigp : 864<p) (bigq : 864<q) (cop : p.Coprime q) :
    (95:ℝ)/100 < odds ((Prod.map (label bigp) (label bigq)) ∘ (seedEquiv cop)) (2^511) ∧
    odds (seedEquiv cop) (2^511) ≤ 7/16 := by
  obtain ⟨a,b⟩ := prime_size pl ph bigp
  obtain ⟨c,d⟩ := prime_size ql qh bigq
  have psize : 2^1023 ≤ Fintype.card (Seed p)+13 := by
    simpa [Seed] using pl.trans (regular_count p)
  have qsize : 2^1023 ≤ Fintype.card (Seed q)+13 := by
    simpa [Seed] using ql.trans (regular_count q)
  constructor
  · rw [transfer,odds,Fintype.card_prod]
    exact full_size_seed_probability (label bigp) (label bigq) (by decide) (by decide)
      (label_fiber bigp) (label_fiber bigq) a c b d
  · rw [show (seedEquiv cop : Input (p*q) → Seed p × Seed q) = id ∘ (seedEquiv cop) by rfl,
      transfer,odds,Fintype.card_prod]
    exact full_size_plain_probability psize qsize

/-- Difference gcd used in an actual pair comparison over the product. -/
def ProperGcd {n : ℕ} (u v : ZMod n) : Prop :=
  1 < n.gcd (u-v).val ∧ n.gcd (u-v).val < n

theorem proper_gcd_iff {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    (u v : ZMod (p*q)) :
    let e := ZMod.chineseRemainder cop
    ProperGcd u v ↔ ((e u).1=(e v).1 ∧ (e u).2≠(e v).2) ∨
      ((e u).2=(e v).2 ∧ (e u).1≠(e v).1) := by
  let e := ZMod.chineseRemainder cop
  let k := (u-v).val
  have cast : e (k : ZMod (p*q)) = e u-e v := by
    rw [show (k : ZMod (p*q))=u-v from ZMod.natCast_zmod_val _,map_sub]
  have a : (k:ZMod p) = (e u).1-(e v).1 := by
    simpa only [map_natCast, Prod.fst_natCast] using congrArg Prod.fst cast
  have b : (k:ZMod q) = (e u).2-(e v).2 := by
    simpa only [map_natCast, Prod.snd_natCast] using congrArg Prod.snd cast
  have pa : p∣k ↔ (e u).1=(e v).1 := by rw [←ZMod.natCast_zmod_eq_zero_iff_dvd,a,sub_eq_zero]
  have qb : q∣k ↔ (e u).2=(e v).2 := by rw [←ZMod.natCast_zmod_eq_zero_iff_dvd,b,sub_eq_zero]
  change (1 < (p*q).gcd k ∧ (p*q).gcd k < p*q) ↔ _
  rw [←pa,←qb]
  have pp : p.Prime := Fact.out
  have qq : q.Prime := Fact.out
  have lp : p < p*q := by nlinarith only [Nat.mul_le_mul_left p qq.two_le,pp.one_lt]
  have lq : q < p*q := by nlinarith only [Nat.mul_le_mul_left q pp.two_le,qq.one_lt]
  by_cases ip : p∣k <;> by_cases iq : q∣k
  · simp [ip,iq,Nat.gcd_eq_left (cop.mul_dvd_of_dvd_of_dvd ip iq)]
  · have eq : (p*q).gcd k=p := by
      rw [Nat.mul_comm p q,Nat.gcd_mul_of_coprime_of_dvd (qq.coprime_iff_not_dvd.mpr iq) ip]
    simp [ip,iq,eq,lp,pp.one_lt]
  · have eq := Nat.gcd_mul_of_coprime_of_dvd (pp.coprime_iff_not_dvd.mpr ip) iq
    simp [ip,iq,eq,lq,qq.one_lt]
  · have eq := ((pp.coprime_iff_not_dvd.mpr ip).symm.mul_right
      (qq.coprime_iff_not_dvd.mpr iq).symm).symm.gcd_eq_one
    simp [ip,iq,eq]

noncomputable def gcdOdds {n : ℕ} [NeZero n] (f : Input n → ZMod n) (m : ℕ) : ℝ :=
  (Nat.card {w : Fin m → Input n // ∃ i j, i≠j ∧ ProperGcd (f (w i)) (f (w j))} : ℝ) /
    (Fintype.card (Input n) : ℝ)^m

private theorem coordinate_odds {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (cop : p.Coprime q)
    {s : Finset (ZMod p)} {t : Finset (ZMod q)} (m : ℕ) (f : Input (p*q) → ZMod (p*q))
    (g : Input (p*q) → ↥s × ↥t)
    (red : ∀ x, ZMod.chineseRemainder cop (f x) = ((g x).1.val,(g x).2.val)) :
    gcdOdds f m = odds g m := by
  have eq (w : Fin m → Input (p*q)) :
      (∃ i j, i≠j ∧ ProperGcd (f (w i)) (f (w j))) ↔ ProperPair (g ∘ w) := by
    simp only [proper_gcd_iff cop,red,ProperPair,Function.comp_apply,Subtype.ext_iff]
  unfold gcdOdds odds
  rw [Nat.card_congr (Equiv.subtypeEquivRight eq)]

/-- Both odds concern proper divisors returned by the gcd of the two actual
public residues, for normalized keys or for the unmodified seeds. -/
theorem full_size_gcd {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (pl : 2^1023≤p) (ph : p<2^1024) (ql : 2^1023≤q) (qh : q<2^1024)
    (cop : p.Coprime q) :
    (95:ℝ)/100 < gcdOdds (publicKey (n:=p*q)) (2^511) ∧
    gcdOdds (fun x : Input (p*q) => x.val) (2^511) ≤ 7/16 := by
  have bigp : 864<p := (by norm_num : 864<2^1023).trans_le pl
  have bigq : 864<q := (by norm_num : 864<2^1023).trans_le ql
  rw [coordinate_odds cop _ _ ((Prod.map (label bigp) (label bigq)) ∘ (seedEquiv cop))
    (coordinates bigp bigq cop),coordinate_odds cop _ _ (seedEquiv cop) (fun _ => rfl)]
  exact full_size pl ph ql qh bigp bigq cop

end PrimeFactors.TwelveSeedBirthday
