import PrimeFactors.GeometricDoubleMatch
import Mathlib.Tactic

/-! Ranks of a shared exponent in complete contiguous intervals. -/

namespace PrimeFactors.GeometricMatchRank
open Finset

/-- The number of matching indices on each side is antitone in the period.
Consequently equal totals force equal left and equal right counts. -/
theorem equal_rank {j W d e : ℕ} (hd : 0<d) (he : 0<e)
    (totals : j/d+(W-j)/d=j/e+(W-j)/e) :
    j/d=j/e ∧ (W-j)/d=(W-j)/e := by
  rcases le_total d e with h|h
  · have l := Nat.div_le_div_left (a:=j) h hd
    have r := Nat.div_le_div_left (a:=W-j) h hd
    omega
  · have l := Nat.div_le_div_left (a:=j) h he
    have r := Nat.div_le_div_left (a:=W-j) h he
    omega

/-- Write i=(j mod d)+d*t. The parameter t starts at zero and the
distinguished representative j has index floor(j/d). -/
theorem residue_count {j W d : ℕ} (inside : j≤W) (pos : 0<d) :
    ((range (W+1)).filter (fun i => i ≡ j [MOD d])).card = j/d+(W-j)/d+1 := by
  let r := j%d
  have low : r<d := Nat.mod_lt _ pos
  have dec : r+d*(j/d)=j := Nat.mod_add_div j d
  have width : W-r = (W-j)+d*(j/d) := by omega
  calc
    _ = (range ((W-r)/d+1)).card := by
      apply card_bij' (fun i _ => i/d) (fun t _ => r+d*t)
      · intro i hi
        obtain ⟨cap, rem⟩ := mem_filter.mp hi
        have full := Nat.mod_add_div i d
        change i%d=r at rem
        rw [rem] at full
        have ci := mem_range.mp cap
        apply mem_range.mpr
        have bound : (i/d)*d ≤ W-r := by
          rw [mul_comm]
          omega
        have := (Nat.le_div_iff_mul_le pos).mpr bound
        omega
      · intro t ht
        have c := mem_range.mp ht
        have bound := (Nat.le_div_iff_mul_le pos).mp (show t≤(W-r)/d by omega)
        rw [mul_comm] at bound
        apply mem_filter.mpr
        refine ⟨mem_range.mpr (by omega),?_⟩
        change (r+d*t)%d=r
        rw [add_comm,Nat.mul_add_mod,Nat.mod_eq_of_lt low]
      · intro i hi
        have rem : i%d=r := (mem_filter.mp hi).2
        rw [←rem,Nat.mod_add_div]
      · intro t _
        rw [Nat.add_mul_div_left _ _ pos,Nat.div_eq_of_lt low,zero_add]
    _ = _ := by rw [card_range,width,Nat.add_mul_div_left _ _ pos]; omega

theorem power_count {G : Type*} [Group G] [Finite G] [DecidableEq G]
    (g : G) {j W : ℕ} (inside : j≤W) :
    ((range (W+1)).filter (fun i => g^i=g^j)).card =
      j/orderOf g+(W-j)/orderOf g+1 := by
  simpa only [pow_eq_pow_iff_modEq] using (residue_count (d:=orderOf g) inside (orderOf_pos g))

/-- Arbitrary multiplicity, including distinct local periods. The common
index has the same rank in the two local lists whenever their lengths agree. -/
theorem equal_power_rank {G H : Type*} [Group G] [Finite G] [DecidableEq G]
    [Group H] [Finite H] [DecidableEq H] (g : G) (h : H) {j W : ℕ} (inside : j≤W)
    (same : ((range (W+1)).filter (fun i => g^i=g^j)).card =
            ((range (W+1)).filter (fun i => h^i=h^j)).card) :
    j/orderOf g=j/orderOf h ∧ (W-j)/orderOf g=(W-j)/orderOf h := by
  rw [power_count g inside,power_count h inside] at same
  exact equal_rank (orderOf_pos g) (orderOf_pos h) (by omega)

/-- With exactly two hits, the first lies strictly left of the midpoint and
the second strictly right. Halfway itself can never be one of two hits. -/
theorem two_orientation {G : Type*} [Group G] {a b j W : ℕ} (g y : G)
    (ab : a<b) (inside : b≤W) (sj : j≤W) (shared : g^j=y)
    (hits : ∀ i≤W, g^i=y ↔ i=a ∨ i=b) :
    (2*j<W ∧ j=a) ∨ (W<2*j ∧ j=b) := by
  have ha := (hits a (ab.le.trans inside)).mpr (Or.inl rfl)
  have hb := (hits b inside).mpr (Or.inr rfl)
  have period : g^(b-a)=1 := by
    apply mul_left_cancel (a:=g^a)
    rw [←pow_add,Nat.add_sub_of_le ab.le,ha,hb,mul_one]
  have perm (i : ℕ) : g^(i+(b-a))=g^i := by rw [pow_add,period,mul_one]
  rcases (hits j sj).mp shared with rfl|rfl
  · left
    refine ⟨?_,rfl⟩
    by_contra! ge
    have early : g^(j-(b-j))=y := by
      rw [←perm (j-(b-j)), Nat.sub_add_cancel (by omega : b-j≤j), ha]
    have := (hits (j-(b-j)) (by omega)).mp early
    omega
  · right
    refine ⟨?_,rfl⟩
    by_contra! ge
    have := (hits (j+(j-a)) (by omega)).mp ((perm j).trans hb)
    omega

/-- Cancel the period in the first coefficient of an r-root polynomial if the
order cofactor k is shared. The equation only needs the common rank t. -/
theorem eliminate_period {R : Type*} [CommRing R] {A B r t d k j : R}
    (moment : -2*B-2*r*A*j=r*A*(r-1-2*t)*d) (cofactor : k*d= -1) :
    -2*k*B+r*A*(r-1-2*t)=2*k*r*A*j := by
  linear_combination k*moment + (r*A*(r-1-2*t))*cofactor

private theorem local_signed {p W a b j k : ℕ} (g y : (ZMod p)ˣ) (A B : ZMod p)
    (ab : a<b) (inside : b≤W) (sj : j≤W) (shared : g^j=y)
    (hits : ∀ i≤W, g^i=y ↔ i=a ∨ i=b)
    (cofactor : k*(b-a)+1=p) (linear : B=A*((a:ZMod p)+b)) :
    k*B+(if 2*j<W then A else -A) = 2*k*j*A := by
  have eq : (k:ZMod p)*((b:ZMod p)-a) = -1 := by
    apply eq_neg_of_add_eq_zero_left
    rw [←Nat.cast_sub ab.le,←Nat.cast_mul,←Nat.cast_one (R:=ZMod p),←Nat.cast_add,cofactor]
    exact ZMod.natCast_self p
  rw [linear]
  rcases two_orientation g y ab inside sj shared hits with ⟨left, ja⟩|⟨right, jb⟩
  · rw [if_pos left,ja]
    linear_combination A*eq
  · rw [if_neg (by omega),jb]
    linear_combination -A*eq

/-- For the normalized common local coefficients A (leading) and B (linear),
one of two fully public signed candidates gives the shared integer index.
The inverse is of 2*k*A modulo the product. -/
theorem two_candidates {p q W ap bp aq bq j k : ℕ} (cop : p.Coprime q)
    (gp yp : (ZMod p)ˣ) (gq yq : (ZMod q)ˣ) (A B inv : ZMod (p*q))
    (sj : j≤W) (cap : W<p*q) (pl : ap<bp) (pu : bp≤W) (ql : aq<bq) (qu : bq≤W)
    (pj : gp^j=yp) (qj : gq^j=yq)
    (ph : ∀ i≤W, gp^i=yp ↔ i=ap ∨ i=bp) (qh : ∀ i≤W, gq^i=yq ↔ i=aq ∨ i=bq)
    (pk : k*(bp-ap)+1=p) (qk : k*(bq-aq)+1=q)
    (pc : (ZMod.chineseRemainder cop B).1=(ZMod.chineseRemainder cop A).1*((ap:ZMod p)+bp))
    (qc : (ZMod.chineseRemainder cop B).2=(ZMod.chineseRemainder cop A).2*((aq:ZMod q)+bq))
    (unit : 2*k*A*inv=1) :
    (((k*B+A)*inv).val=j ∨ ((k*B-A)*inv).val=j) := by
  let e := ZMod.chineseRemainder cop
  let sign : ZMod (p*q) := if 2*j<W then A else -A
  have pe := local_signed gp yp (e A).1 (e B).1 pl pu sj pj ph pk pc
  have qe := local_signed gq yq (e A).2 (e B).2 ql qu sj qj qh qk qc
  have two : e 2=2 := by simpa only [Nat.cast_ofNat] using map_natCast e 2
  have full : (k:ZMod (p*q))*B+sign=2*k*j*A := by
    apply e.injective
    apply Prod.ext
    · split_ifs at pe ⊢ with hi <;> simpa [sign,hi,two] using pe
    · split_ifs at qe ⊢ with hi <;> simpa [sign,hi,two] using qe
  have dec : (((k:ZMod (p*q))*B+sign)*inv).val=j := by
    rw [full,show (2:ZMod (p*q))*k*j*A*inv=j*(2*k*A*inv) by ring,unit,mul_one,
      ZMod.val_natCast_of_lt (sj.trans_lt cap)]
  by_cases half : 2*j<W
  · exact Or.inl (by simpa only [sign,if_pos half] using dec)
  · exact Or.inr (by simpa only [sign,if_neg half,sub_eq_add_neg] using dec)

open GeometricDoubleMatch

/-- The actual three product readings give the required linear coefficient
after applying any ring projection to a field containing the two hits. -/
theorem projected_linear {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T)
    (I : Finset ℕ) (y g : R) {a b : ℕ} (ha : a∈I) (hb : b∈I) (ne : a≠b)
    (pa : (f g)^a=f y) (pb : (f g)^b=f y) :
    f (linear (reading I y g))=f (leading (reading I y g))*((a:T)+b) := by
  have v := extract (fun z => two_hits ha hb ne (f y) (f g) z pa pb)
  have two : f 2=2 := by simpa only [Nat.cast_ofNat] using map_natCast f 2
  simpa only [linear,leading,map_sub,map_add,map_mul,map_reading,map_one,map_zero,map_neg,two]
    using v.2.1.trans (congrArg (·*((a:T)+b)) v.1.symm)

/-- The factor-labeled projections here specify only the success hypothesis.
The two returned residues depend on the product-side coefficients and k. -/
theorem from_readings {p q W ap bp aq bq j k : ℕ} (cop : p.Coprime q)
    (g y : (ZMod (p*q))ˣ) (inv : ZMod (p*q))
    (sj : j≤W) (cap : W<p*q) (pl : ap<bp) (pu : bp≤W) (ql : aq<bq) (qu : bq≤W)
    (shared : g^j=y)
    (ph : ∀ i≤W, (ZMod.chineseRemainder cop ((g:ZMod (p*q))^i)).1 =
        (ZMod.chineseRemainder cop (y:ZMod (p*q))).1 ↔ i=ap ∨ i=bp)
    (qh : ∀ i≤W, (ZMod.chineseRemainder cop ((g:ZMod (p*q))^i)).2 =
        (ZMod.chineseRemainder cop (y:ZMod (p*q))).2 ↔ i=aq ∨ i=bq)
    (pk : k*(bp-ap)+1=p) (qk : k*(bq-aq)+1=q)
    (unit : 2*k*leading (reading (range (W+1)) (y:ZMod (p*q)) g)*inv=1) :
    let C := reading (range (W+1)) (y:ZMod (p*q)) g
    (((k*linear C+leading C)*inv).val=j ∨ ((k*linear C-leading C)*inv).val=j) := by
  let e := ZMod.chineseRemainder cop
  let f := (RingHom.fst (ZMod p) (ZMod q)).comp e.toRingHom
  let h := (RingHom.snd (ZMod p) (ZMod q)).comp e.toRingHom
  let fp := Units.map f.toMonoidHom
  let fq := Units.map h.toMonoidHom
  have castP (i : ℕ) : (fp g)^i=fp y ↔ (e ((g:ZMod (p*q))^i)).1=(e (y:ZMod (p*q))).1 := by
    change (fp g)^i=fp y ↔ f ((g:ZMod (p*q))^i)=f (y:ZMod (p*q))
    rw [map_pow,Units.ext_iff]
    rfl
  have castQ (i : ℕ) : (fq g)^i=fq y ↔ (e ((g:ZMod (p*q))^i)).2=(e (y:ZMod (p*q))).2 := by
    change (fq g)^i=fq y ↔ h ((g:ZMod (p*q))^i)=h (y:ZMod (p*q))
    rw [map_pow,Units.ext_iff]
    rfl
  have hP (i : ℕ) (t : i≤W) := (castP i).trans (ph i t)
  have hQ (i : ℕ) (t : i≤W) := (castQ i).trans (qh i t)
  apply two_candidates cop (fp g) (fp y) (fq g) (fq y) _ _ inv sj cap pl pu ql qu
    (by rw [←map_pow,shared]) (by rw [←map_pow,shared]) hP hQ pk qk _ _ unit
  · apply projected_linear f _ _ _ (mem_range.mpr (by omega)) (mem_range.mpr (by omega)) pl.ne
    · rw [←map_pow]
      exact (ph ap (by omega)).mpr (Or.inl rfl)
    · rw [←map_pow]
      exact (ph bp pu).mpr (Or.inr rfl)
  · apply projected_linear h _ _ _ (mem_range.mpr (by omega)) (mem_range.mpr (by omega)) ql.ne
    · rw [←map_pow]
      exact (qh aq (by omega)).mpr (Or.inl rfl)
    · rw [←map_pow]
      exact (qh bq qu).mpr (Or.inr rfl)

end PrimeFactors.GeometricMatchRank
