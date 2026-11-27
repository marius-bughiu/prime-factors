import PrimeFactors.CyclotomicRadixLift
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Tactic
import Mathlib.Data.Fintype.Parity

/-! A two-point evaluation of a binary cyclotomic polynomial in the fixed field
of eleven elements detects the quadratic characters of the two factors modulo
five. The full four-point product is one. For the classical evaluations over
the complex numbers see Bzdęga, Herrera-Poyatos and Moree, Lemma 28,
<https://arxiv.org/abs/1611.06783>. The proofs here specialize the binary
product identity directly over a finite field. -/
namespace PrimeFactors.CyclotomicSmallNorm
open Polynomial

local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Evaluation at a conjugate pair of primitive fifth roots in the fixed field. -/
noncomputable def pairValue (N : ℕ) : ZMod 11 :=
  (cyclotomic N (ZMod 11)).eval 3 * (cyclotomic N (ZMod 11)).eval 4

/-- The corresponding product over all four primitive fifth roots. -/
noncomputable def fullValue (N : ℕ) : ZMod 11 :=
  pairValue N * ((cyclotomic N (ZMod 11)).eval 9 * (cyclotomic N (ZMod 11)).eval 5)

/-- The binary cyclotomic identity, valid even when the characteristic divides N. -/
theorem binary {R : Type*} [CommRing R] {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (neq : p≠q) (x : R) :
    (cyclotomic (p*q) R).eval x * ((x^p-1)*(x^q-1)) = (x^(p*q)-1)*(x-1) := by
  letI : Fact p.Prime := ⟨pp⟩
  have nd : ¬q∣p := fun d => neq ((Nat.prime_dvd_prime_iff_eq qp pp).mp d).symm
  have prod := congrArg (eval x) (cyclotomic_expand_eq_cyclotomic_mul qp nd R)
  simp only [expand_eval, eval_mul] at prod
  have geo (y : R) : (cyclotomic p R).eval y * (y-1) = y^p-1 := by
    have h : cyclotomic p R * (X-1) = X^p-1 := by rw [cyclotomic_prime, geom_sum_mul]
    simpa using congrArg (eval y) h
  calc
    _ = ((cyclotomic (p*q) R).eval x * (cyclotomic p R).eval x * (x^q-1))*(x-1) := by
      rw [←geo x]; ring
    _ = _ := by rw [←prod,geo,←pow_mul,Nat.mul_comm q p]

private theorem reduce_exp {x : ZMod 11} (root : x^5=1) (a : ℕ) : x^a=x^(a%5) := by
  calc
    _ = x^(a%5+5*(a/5)) := by rw [Nat.mod_add_div]
    _ = _ := by rw [pow_add,pow_mul,root,one_pow,mul_one]

private def val (x : ZMod 11) (a b : ℕ) : ZMod 11 :=
  ((x^((a*b)%5)-1)*(x-1))*((x^a-1)*(x^b-1))^9

private theorem at_root {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (neq : p≠q)
    (p5 : p%5 ≠ 0) (q5 : q%5 ≠ 0) (x : ZMod 11) (rx : x^5=1) (nx : x≠1) :
    (cyclotomic (p*q) (ZMod 11)).eval x = val x (p%5) (q%5) := by
  have nz : ∀ (z : ZMod 11) (i : Fin 5), z^5=1 → z≠1 → i.val≠0 → z^i.val-1≠0 := by decide
  let d := (x^(p%5)-1)*(x^(q%5)-1)
  have dn : d≠0 := mul_ne_zero (nz x ⟨p%5,Nat.mod_lt _ (by decide)⟩ rx nx p5)
      (nz x ⟨q%5,Nat.mod_lt _ (by decide)⟩ rx nx q5)
  have power : d^9*d = 1 := ZMod.pow_card_sub_one_eq_one dn
  apply mul_right_cancel₀ dn
  change _ * d = ((x^(((p%5)*(q%5))%5)-1)*(x-1))*d^9*d
  rw [mul_assoc,power,mul_one,←Nat.mul_mod,←reduce_exp rx (p*q)]
  dsimp only [d]
  rw [←reduce_exp rx p,←reduce_exp rx q]
  exact binary pp qp neq x

/-- Decode a complete sum modulo five from one small-field value. For value
one a prime is one modulo five. The six other possible values distinguish
the unordered pairs of residues among 2, 3, 4. -/
def decode (N : ℕ) (v : ZMod 11) : ℕ :=
  match v.val with
  | 1 => (N+1)%5
  | 4 | 10 => 1
  | 5 => 2
  | 7 => 0
  | 8 => 4
  | 9 => 3
  | _ => 0

theorem single_value {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (neq : p≠q)
    (p5 : p%5 ≠ 0) (q5 : q%5 ≠ 0) :
    decode (p*q) ((cyclotomic (p*q) (ZMod 11)).eval 3) = (p+q)%5 := by
  rw [at_root pp qp neq p5 q5 3 (by decide) (by decide),Nat.add_mod]
  have reduce (v : ZMod 11) : decode (p*q) v = decode (((p%5)*(q%5))%5) v := by
    have h : (p*q+1)%5=(((p%5)*(q%5))%5+1)%5 := by
      rw [Nat.add_mod (p*q) 1,Nat.mul_mod p q]
    unfold decode
    split <;> simp only [h]
  rw [reduce]
  have table : ∀ a b : Fin 5, a.val≠0 → b.val≠0 →
      decode ((a.val*b.val)%5) (val 3 a b) = (a.val+b.val)%5 := by decide
  exact table ⟨p%5,Nat.mod_lt _ (by decide)⟩ ⟨q%5,Nat.mod_lt _ (by decide)⟩ p5 q5

/-- The nonsquares in the multiplicative group modulo five. -/
def nonresidue (a : ℕ) : Prop := a%5=2 ∨ a%5=3

noncomputable instance (a : ℕ) : Decidable (nonresidue a) := by unfold nonresidue; infer_instance

/-- The relative product detects two nonsquares. Taking the full norm erases this bit. -/
theorem evaluations {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (neq : p≠q)
    (p5 : p%5 ≠ 0) (q5 : q%5 ≠ 0) :
    pairValue (p*q) = (if nonresidue p ∧ nonresidue q then 3 else 1) ∧
    fullValue (p*q) = 1 := by
  have table : ∀ (a b : Fin 5), a.val≠0 → b.val≠0 →
      val 3 a b * val 4 a b = (if (a.val=2 ∨ a.val=3) ∧ (b.val=2 ∨ b.val=3) then 3 else 1) ∧
      val 3 a b * val 4 a b * (val 9 a b * val 5 a b) = 1 := by decide
  unfold fullValue pairValue nonresidue
  rw [at_root pp qp neq p5 q5 3 (by decide) (by decide),
    at_root pp qp neq p5 q5 4 (by decide) (by decide),
    at_root pp qp neq p5 q5 9 (by decide) (by decide),
    at_root pp qp neq p5 q5 5 (by decide) (by decide)]
  exact table ⟨p%5,Nat.mod_lt _ (by decide)⟩ ⟨q%5,Nat.mod_lt _ (by decide)⟩ p5 q5

/-- When the product is 1 or 4 modulo five, the value reads a bit of the sum. -/
theorem reads_sum {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (neq : p≠q)
    (squareClass : (p*q)%5=1 ∨ (p*q)%5=4) :
    5∣p+q ↔ (if (p*q)%5=1 then pairValue (p*q)=3 else pairValue (p*q)=1) := by
  rw [Nat.mul_mod] at squareClass
  have p5 : p%5≠0 := by rintro h; simp [h] at squareClass
  have q5 : q%5≠0 := by rintro h; simp [h] at squareClass
  rw [(evaluations pp qp neq p5 q5).1,Nat.mul_mod,Nat.dvd_iff_mod_eq_zero,Nat.add_mod]
  have table : ∀ (a b : Fin 5), (a.val*b.val)%5=1 ∨ (a.val*b.val)%5=4 →
      ((a.val+b.val)%5=0 ↔ if (a.val*b.val)%5=1 then
        (if (a.val=2 ∨ a.val=3) ∧ (b.val=2 ∨ b.val=3) then (3:ZMod 11) else 1)=3 else
        (if (a.val=2 ∨ a.val=3) ∧ (b.val=2 ∨ b.val=3) then (3:ZMod 11) else 1)=1) := by decide
  exact table ⟨p%5,Nat.mod_lt _ (by decide)⟩ ⟨q%5,Nat.mod_lt _ (by decide)⟩ squareClass

private theorem root5 {p : ℕ} (pp : p.Prime) (odd : p≠2) :
    IsSquare (5 : ZMod p) ↔ ¬ nonresidue p := by
  letI : Fact p.Prime := ⟨pp⟩
  have rec := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p:=5) (q:=p) (by decide) odd
  norm_num only [Nat.cast_ofNat] at rec
  rw [←rec]
  have table : ∀ z : ZMod 5, IsSquare z ↔ ¬(z.val=2 ∨ z.val=3) := by decide
  simpa only [ZMod.val_natCast,nonresidue] using table (p:ZMod 5)

/-- On the public square classes, this small-field evaluation is precisely a
decision of whether 5 has a square root modulo the complete product. -/
theorem detects_square {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (neq : p≠q)
    (op : p≠2) (oq : q≠2) (squareClass : (p*q)%5=1 ∨ (p*q)%5=4) :
    pairValue (p*q)=1 ↔ IsSquare (5 : ZMod (p*q)) := by
  have cop := (Nat.coprime_primes pp qp).mpr neq
  let e := ZMod.chineseRemainder cop
  have local5 : IsSquare (5 : ZMod (p*q)) ↔ IsSquare (5 : ZMod p) ∧ IsSquare (5 : ZMod q) := by
    constructor
    · rintro ⟨z,hz⟩
      have h := congrArg e hz
      rw [map_ofNat,map_mul] at h
      exact ⟨⟨_,congrArg Prod.fst h⟩,⟨_,congrArg Prod.snd h⟩⟩
    · rintro ⟨⟨u,hu⟩,⟨v,hv⟩⟩
      refine ⟨e.symm (u,v),e.injective ?_⟩
      rw [map_ofNat,map_mul,e.apply_symm_apply]
      exact Prod.ext hu hv
  rw [Nat.mul_mod] at squareClass
  have p5 : p%5≠0 := by rintro h; simp [h] at squareClass
  have q5 : q%5≠0 := by rintro h; simp [h] at squareClass
  rw [local5,root5 pp op,root5 qp oq,(evaluations pp qp neq p5 q5).1]
  have table : ∀ a b : Fin 5, (a.val*b.val)%5=1 ∨ (a.val*b.val)%5=4 →
      ((if (a.val=2 ∨ a.val=3) ∧ (b.val=2 ∨ b.val=3) then (3:ZMod 11) else 1)=1 ↔
        ¬(a.val=2 ∨ a.val=3) ∧ ¬(b.val=2 ∨ b.val=3)) := by decide
  exact table ⟨p%5,Nat.mod_lt _ (by decide)⟩ ⟨q%5,Nat.mod_lt _ (by decide)⟩ squareClass

private theorem realize {T : ℕ} (tp : 0<T) (B : ℕ) (u : (ZMod 5)ˣ) :
    ∃ p q : ℕ, B<p ∧ p<q ∧ p.Prime ∧ q.Prime ∧
      p*q ≡ 1 [MOD T] ∧ (p:ZMod 5)=u ∧ (q:ZMod 5)=↑u⁻¹ := by
  let L := 5*T
  letI : NeZero L := ⟨(Nat.mul_pos (by decide) tp).ne'⟩
  have d5 : 5∣L := dvd_mul_right ..
  have dt : T∣L := dvd_mul_left ..
  obtain ⟨w,hw⟩ := ZMod.unitsMap_surjective d5 u
  obtain ⟨p,bp,pp,hp⟩ := Nat.forall_exists_prime_gt_and_eq_mod w.isUnit B
  obtain ⟨q,pq,qp,hq⟩ := Nat.forall_exists_prime_gt_and_eq_mod w⁻¹.isUnit p
  have one : ((p*q:ℕ):ZMod L)=1 := by rw [Nat.cast_mul,hp,hq,←Units.val_mul,mul_inv_cancel]; rfl
  have cong : p*q ≡ 1 [MOD L] := (ZMod.natCast_eq_natCast_iff ..).mp (by simpa using one)
  have red {a : ℕ} {v : (ZMod L)ˣ} (h : (a:ZMod L)=v) :
      (a:ZMod 5) = ZMod.unitsMap d5 v := by
    simpa only [map_natCast,ZMod.unitsMap_val,ZMod.castHom_apply] using
      congrArg (ZMod.castHom d5 (ZMod 5)) h
  exact ⟨p,q,bp,pq,pp,qp,cong.of_dvd dt,by rw [red hp,hw],by rw [red hq,map_inv,hw]⟩

/-- No fixed residue of the public product determines the fifth-root value on
arbitrarily large distinct odd semiprimes, even restricted to products 1 mod 5. -/
theorem collision {T : ℕ} (tp : 0<T) (B : ℕ) :
    ∃ p q r s : ℕ, max 5 B<p ∧ p<q ∧ q<r ∧ r<s ∧
      p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime ∧ p*q ≡ 1 [MOD T] ∧ r*s ≡ 1 [MOD T] ∧
      (p*q)%5=1 ∧ (r*s)%5=1 ∧ pairValue (p*q)=1 ∧ pairValue (r*s)=3 := by
  obtain ⟨p,q,bp,pq,pp,qp,m1,p1,q1⟩ := realize tp (max 5 B) 1
  let u : (ZMod 5)ˣ := ⟨2,3,by decide,by decide⟩
  obtain ⟨r,s,qr,rs,rp,sp,m2,r2,s3⟩ := realize tp q u
  have cv {a : ℕ} {z : ZMod 5} (h : (a:ZMod 5)=z) : a%5=z.val := by
    simpa only [ZMod.val_natCast] using congrArg ZMod.val h
  have ap : p%5=1 := cv p1
  have aq : q%5=1 := cv q1
  have ar : r%5=2 := cv r2
  have as' : s%5=3 := cv s3
  have first := (evaluations pp qp pq.ne (by omega) (by omega)).1
  have second := (evaluations rp sp rs.ne (by omega) (by omega)).1
  refine ⟨p,q,r,s,bp,pq,qr,rs,pp,qp,rp,sp,m1,m2,?_,?_,?_,?_⟩
  · rw [Nat.mul_mod,ap,aq]
  · rw [Nat.mul_mod,ar,as']
  · simpa [nonresidue,ap,aq] using first
  · simpa [nonresidue,ar,as'] using second

/-- The two products already agree modulo 250. Only the second sum is 0 modulo 5. -/
theorem example_pair : 341%250=91%250 ∧ pairValue 341=1 ∧ pairValue 91=3 ∧
    fullValue 341=1 ∧ fullValue 91=1 ∧ (11+31)%5=2 ∧ (7+13)%5=0 := by
  have one := evaluations (p:=11) (q:=31) (by decide) (by decide) (by decide) (by decide) (by decide)
  have three := evaluations (p:=7) (q:=13) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨rfl,one.1,three.1,one.2,three.2,rfl,rfl⟩

/-- A public square test at any chosen multiplier supplies the root directly.
On product class four, this forces the sum to vanish modulo five. -/
theorem public_square {p q k x : ℕ} (pp : p.Prime) (qp : q.Prime) (neq : p≠q)
    (op : p≠2) (oq : q≠2) (four : (p*q)%5=4) (test : x^2=k*(p*q)+5) : 5∣p+q := by
  have root : IsSquare (5 : ZMod (p*q)) := by
    refine ⟨x,?_⟩
    have h := congrArg (fun n : ℕ => (n:ZMod (p*q))) test
    change ((x^2 : ℕ) : ZMod (p*q)) = ((k*(p*q)+5 : ℕ) : ZMod (p*q)) at h
    rw [Nat.cast_pow,Nat.cast_add,Nat.cast_mul k (p*q),ZMod.natCast_self,mul_zero,zero_add] at h
    simpa only [pow_two,Nat.cast_ofNat] using h.symm
  have bit := (detects_square pp qp neq op oq (Or.inr four)).mpr root
  apply (reads_sum pp qp neq (Or.inr four)).mpr
  simpa [four] using bit

private theorem known_stride {p q : ℕ} (po : Odd p) (qo : Odd q) :
    (p+q)%CyclotomicRadixLift.stride (p*q) = (p*q+1)%CyclotomicRadixLift.stride (p*q) := by
  have h := CyclotomicRadixLift.divides po qo
  have eq : p*q+1=(p-1)*(q-1)+(p+q) := by
    have posp := po.pos
    have posq := qo.pos
    obtain ⟨a,ha⟩ := Nat.exists_eq_succ_of_ne_zero posp.ne'
    obtain ⟨b,hb⟩ := Nat.exists_eq_succ_of_ne_zero posq.ne'
    rw [ha,hb]
    simp only [Nat.succ_sub_one,Nat.succ_eq_add_one]
    ring
  rw [eq,Nat.add_mod ((p-1)*(q-1)),Nat.mod_eq_zero_of_dvd h,zero_add,Nat.mod_mod]

/-- Product-only upper and lower inequalities on the sum. Either two factors
above e or two factors below e give e*(p+q) ≤ e²+N. -/
private theorem bounds {p q : ℕ} {n l u e : ℤ} (prod : (p:ℤ)*q=n)
    (left : (l-1)^2<4*n) (right : e^2+n<e*(u+1)) (ep : 0<e)
    (endpoint : (e≤(p:ℤ) ∧ e≤(q:ℤ)) ∨ ((p:ℤ)≤e ∧ (q:ℤ)≤e)) :
    l≤(p:ℤ)+q ∧ (p:ℤ)+q≤u := by
  have gap : (l-1)^2<((p:ℤ)+q)^2 := by nlinarith [sq_nonneg ((p:ℤ)-q)]
  have low := lt_of_pow_lt_pow_left₀ 2 (by positivity : 0≤(p:ℤ)+q) gap
  have upper : e*((p:ℤ)+q)≤e^2+n := by
    rcases endpoint with ⟨a,b⟩|⟨a,b⟩
    · nlinarith [mul_nonneg (sub_nonneg.mpr a) (sub_nonneg.mpr b)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr a) (sub_nonneg.mpr b)]
  have high := lt_of_mul_lt_mul_left (upper.trans_lt right) ep.le
  omega

/-- The ordinary W=24 rule already fixes the sum of this 18-bit control.
No square witness is used. -/
theorem recovered_example {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (low : 256≤p) (ord : p<q) (high : q≤511) (prod : p*q=174719) : p+q=840 := by
  have stride := known_stride (pp.odd_of_ne_two (by omega)) (qp.odd_of_ne_two (by omega))
  rw [prod] at stride
  change (p+q)%24=0 at stride
  have ep : (p:ℤ)*(q:ℤ)=174719 := by exact_mod_cast prod
  have b := bounds (l:=836) (u:=852) (e:=511) ep (by decide) (by decide) (by decide)
    (Or.inr ⟨by exact_mod_cast ord.le.trans high,by exact_mod_cast high⟩)
  omega

/-- The ordinary stride and small-field mod-5 table leave three sums on each
new input. The 10-bit product has the true sum first. -/
theorem ordinary_menus (s : ℕ) :
    ((1296≤s ∧ s≤1331 ∧ s%8=4 ∧ (s%5=0 ∨ s%5=1 ∨ s%5=4)) ↔
        s=1300 ∨ s=1316 ∨ s=1324) ∧
    ((3316≤s ∧ s≤3389 ∧ s%24=0 ∧ (s%5=0 ∨ s%5=1 ∨ s%5=4)) ↔
        s=3336 ∨ s=3360 ∨ s=3384) := by
  omega

/-- With two distinct 10-bit primes the square witness selects the first
of the three ordinary candidate sums. -/
theorem first_selective {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (low : 512≤p)
    (ord : p<q) (_high : q≤1023) (prod : p*q=419899) : p+q=1300 := by
  have po := pp.odd_of_ne_two (by omega)
  have qo := qp.odd_of_ne_two (by omega)
  have div := public_square (k:=1) (x:=648) pp qp ord.ne (by omega) (by omega)
    (by rw [prod]) (by rw [prod]; decide)
  have stride := known_stride po qo
  rw [prod] at stride
  change (p+q)%8=4 at stride
  have ep : (p:ℤ)*(q:ℤ)=419899 := by exact_mod_cast prod
  have above : 513≤p := by obtain ⟨a,ha⟩ := po; omega
  have b := bounds (l:=1296) (u:=1331) (e:=513) ep (by decide) (by decide) (by decide)
    (Or.inl ⟨by exact_mod_cast above,by exact_mod_cast above.trans ord.le⟩)
  omega

/-- With two distinct 11-bit primes the square witness excludes the first
ordinary candidate and selects the second. -/
theorem first_saving {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (low : 1024≤p)
    (ord : p<q) (high : q≤2047) (prod : p*q=2748959) : p+q=3360 := by
  have po := pp.odd_of_ne_two (by omega)
  have qo := qp.odd_of_ne_two (by omega)
  have div := public_square (k:=1) (x:=1658) pp qp ord.ne (by omega) (by omega)
    (by rw [prod]) (by rw [prod]; decide)
  have stride := known_stride po qo
  rw [prod] at stride
  change (p+q)%24=0 at stride
  have ep : (p:ℤ)*(q:ℤ)=2748959 := by exact_mod_cast prod
  have b := bounds (l:=3316) (u:=3389) (e:=2047) ep (by decide) (by decide) (by decide)
    (Or.inr ⟨by exact_mod_cast ord.le.trans high,by exact_mod_cast high⟩)
  omega

/-- Independent primality and product certificates for all three examples. -/
theorem example_factors :
    (Nat.Prime 379 ∧ Nat.Prime 461 ∧ 379*461=174719) ∧
    (Nat.Prime 599 ∧ Nat.Prime 701 ∧ 599*701=419899) ∧
    (Nat.Prime 1409 ∧ Nat.Prime 1951 ∧ 1409*1951=2748959) := by norm_num

end PrimeFactors.CyclotomicSmallNorm
