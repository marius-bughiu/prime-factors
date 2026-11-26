import PrimeFactors.GapStride
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.LinearCombination

/-! Primitive two-weight templates for the negative remainders at N and 2N. -/
namespace PrimeFactors.MixedNegativeTemplates

private theorem residues : ∀ i j : Fin 12, (i.val*j.val)%12=5 →
    (i.val+j.val)%12=6 ∧ i.val%4=j.val%4 := by decide +kernel

/-- For every balanced prime pair in these two residue classes the two
negative magnitudes are 4g and 9g. Both actual square-dependency gcds return
the factors. The displayed labels still depend on the unknown input factors. -/
theorem five_mod_twelve {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (order : p < q) (balanced : q ≤ 2*p) (res : (p*q)%12=5) :
    let t := (p+q)/6
    let s := (q-p)/4
    ∃ g : ℕ, 0 < t ∧ 0 < s ∧ 0 < g ∧ t.Coprime (p*q) ∧ s.Coprime (p*q) ∧
      t^2+4*g=p*q ∧ s^2+9*g=2*(p*q) ∧ 3*t-2*s=p ∧ 3*t+2*s=q ∧ t*s≤6*g ∧ (4*g)*(9*g)=(6*g)^2 ∧
      (6*g-t*s).gcd (p*q)=q ∧ (t*s+6*g).gcd (p*q)=p := by
  let t := (p+q)/6
  let s := (q-p)/4
  change ∃ g : ℕ, 0<t ∧ 0<s ∧ 0<g ∧ _
  have rc := residues ⟨p%12,Nat.mod_lt _ (by decide)⟩ ⟨q%12,Nat.mod_lt _ (by decide)⟩
    (by simpa only [← Nat.mul_mod] using res)
  change (p%12 + q%12)%12=6 ∧ p%12%4=q%12%4 at rc
  rw [←Nat.add_mod,Nat.mod_mod_of_dvd _ (by decide : 4∣12),Nat.mod_mod_of_dvd _ (by decide : 4∣12)] at rc
  have sum : 6*t=p+q := by dsimp [t]; omega
  have gap : 4*s+p=q := by dsimp [s]; omega
  have middle : 3*t=p+2*s := by omega
  have upper : 3*t+2*s=q := by omega
  have ppos := pp.pos
  have spos : 0<s := by omega
  have tpos : 0<t := by omega
  have tp : t<p := by omega
  have sp : s<p := by omega
  have cop {x y : ℕ} (pr : y.Prime) (pos : 0<x) (lt : x<y) : x.Coprime y :=
    (pr.coprime_iff_not_dvd.mpr (fun h => (not_le_of_gt lt) (Nat.le_of_dvd pos h))).symm
  have tc := (cop pp tpos tp).mul_right (cop qp tpos (tp.trans order))
  have sc := (cop pp spos sp).mul_right (cop qp spos (sp.trans order))
  have twoP : p≠2 := by rintro rfl; omega
  have twoQ : q≠2 := by have := pp.two_le; omega
  have twoCop := ((Nat.coprime_primes Nat.prime_two pp).mpr twoP.symm).mul_right
    ((Nat.coprime_primes Nat.prime_two qp).mpr twoQ.symm)
  have small : t^2 < p*q := calc
    t^2 < p^2 := Nat.pow_lt_pow_left tp (by decide)
    _ ≤ p*q := by simpa only [pow_two] using Nat.mul_le_mul_left p order.le
  have n4 : (p*q)%4=1 := by have h := Nat.mod_mod_of_dvd (p*q) (by decide : 4∣12); omega
  have odd : t%4=1 ∨ t%4=3 := by omega
  have t4 : t^2%4=1 := by rw [Nat.pow_mod]; rcases odd with h|h <;> rw [h]
  let g := (p*q-t^2)/4
  have first : t^2+4*g=p*q := by dsimp [g]; omega
  have gpos : 0<g := by omega
  have relation : 9*t^2=4*s^2+p*q := by
    calc
      9*t^2=(3*t)^2 := by ring
      _ = (p+2*s)^2 := by rw [middle]
      _ = 4*s^2+p*q := by rw [← gap]; ring
  have second : s^2+9*g=2*(p*q) := by omega
  have qtimes := congrArg (fun x : ℕ => x*t) upper
  have ptimes := congrArg (fun x : ℕ => x*t) middle
  simp only at qtimes ptimes
  have baseD : 2*(6*g) + t*q = 3*p*q+2*(t*s) := by nlinarith only [first,qtimes]
  have baseS : 2*(t*s+6*g)+p*t=3*p*q := by nlinarith only [first,ptimes]
  have qCap := Nat.mul_le_mul_right q (show t≤3*p by omega)
  have sign : t*s≤6*g := by omega
  have dg : 2*(6*g-t*s)=(3*p-t)*q := by rw [Nat.sub_mul,Nat.mul_sub]; omega
  have sg : 2*(t*s+6*g)=(3*q-t)*p := by
    rw [Nat.sub_mul,Nat.mul_comm t p,show 3*q*p=3*p*q by ring]
    omega
  refine ⟨g,tpos,spos,gpos,tc,sc,first,second,by omega,upper,sign,by ring,?_,?_⟩
  · rw [← Nat.Coprime.gcd_mul_left_cancel _ twoCop,dg,Nat.gcd_mul_right,
      Nat.gcd_mul_right_sub_left (by omega : t≤3*p),(cop pp tpos tp).gcd_eq_one,one_mul]
  · rw [← Nat.Coprime.gcd_mul_left_cancel _ twoCop,sg,Nat.mul_comm p q,Nat.gcd_mul_right,
      Nat.gcd_mul_right_sub_left (by omega : t≤3*q),(cop qp tpos (tp.trans order)).gcd_eq_one,one_mul]

/-- A compatible root does not extend beyond the larger of these two
Chinese remainder factors. The coarse height bound suffices for classifying
all the bounded templates; no irrational endpoints enter the finite check. -/
theorem height_filter {p q a b u v t s : ℕ} (ord : p≤q) (bal : q≤2*p)
    (ap : 0<a) (bp : 0<b) (first : t^2<p*q) (second : s^2<2*(p*q))
    (smaller : u*p≤b*t+a*s) (larger : v*q≤b*t+a*s) :
    2*max u v<3*b+4*a := by
  have prod := Nat.mul_le_mul_left p bal
  have tcap : 2*t<3*p := by
    by_contra! h
    nlinarith only [Nat.pow_le_pow_left h 2,first,prod]
  have scap : s<2*p := by
    by_contra! h
    nlinarith only [Nat.pow_le_pow_left h 2,second,prod]
  have packed : max u v*p ≤ b*t+a*s := by
    rw [max_mul_of_nonneg _ _ (Nat.zero_le p)]
    exact max_le smaller ((Nat.mul_le_mul_left v ord).trans larger)
  apply Nat.lt_of_mul_lt_mul_right (a:=p)
  nlinarith only [packed,Nat.mul_lt_mul_of_pos_left tcap bp,Nat.mul_lt_mul_of_pos_left scap ap]

/-- Three residues determine the integrality of the labels. When b²−2a² is
negative the plus/minus assignment is reversed. -/
def Local (rho a b u v : ℕ) : Prop :=
  if 2*a^2 ≤ b^2 then (u+v*rho)%(2*b)=0 ∧ u%(2*a)=(v*rho)%(2*a)
  else u%(2*b)=(v*rho)%(2*b) ∧ (u+v*rho)%(2*a)=0

/-- Multiplying by the unknown p permutes the residues modulo each divisor of
24, and p is its own inverse there. Thus the sum and difference conditions
for the hidden factors are both equivalent to tests on the public product. -/
theorem product_reduction {p q m : ℕ} (unit : p.Coprime 6) (divisor : m∣24) (u v : ℕ) :
    let rho := p*q%24
    ((u*p+v*q)%m=0 ↔ (u+v*rho)%m=0) ∧ (u*p%m=v*q%m ↔ u%m=v*rho%m) := by
  let rho := p*q%24
  have sq : p^2 ≡ 1 [MOD m] := (square_mod_twentyfour unit).of_dvd divisor
  have residue : rho ≡ p*q [MOD m] := (Nat.mod_modEq (p*q) 24).of_dvd divisor
  have partner : rho*p ≡ q [MOD m] := calc
    rho*p ≡ p*q*p [MOD m] := residue.mul_right p
    _ = p^2*q := by ring
    _ ≡ 1*q [MOD m] := sq.mul_right q
    _ = q := one_mul _
  have cancel (x y : ℕ) : x*p ≡ y*p [MOD m] ↔ x ≡ y [MOD m] := by
    refine ⟨fun h => ?_, fun h => h.mul_right p⟩
    calc
      x = 1*x := (one_mul _).symm
      _ ≡ p^2*x [MOD m] := sq.symm.mul_right x
      _ = x*p*p := by ring
      _ ≡ y*p*p [MOD m] := h.mul_right p
      _ = p^2*y := by ring
      _ ≡ 1*y [MOD m] := sq.mul_right y
      _ = y := one_mul _
  have rhs : v*rho*p ≡ v*q [MOD m] := by simpa only [Nat.mul_assoc] using partner.mul_left v
  have sum : (u+v*rho)*p ≡ u*p+v*q [MOD m] := by rw [Nat.add_mul]; exact rhs.add_left _
  change ((u*p+v*q)%m=0 ↔ (u+v*rho)%m=0) ∧ (u*p%m=v*q%m ↔ u%m=v*rho%m)
  have zero : ∀ x : ℕ, x%m=0 ↔ x≡0 [MOD m] := fun x => by simp only [Nat.ModEq,Nat.zero_mod]
  rw [zero,zero]
  constructor
  · have cc := cancel (u+v*rho) 0
    rw [Nat.zero_mul] at cc
    exact ⟨fun h => cc.mp (sum.trans h),fun h => sum.symm.trans (cc.mpr h)⟩
  · exact ⟨fun h => (cancel u (v*rho)).mp ((show u*p ≡ v*q [MOD m] from h).trans rhs.symm),
      fun h => ((cancel u (v*rho)).mpr h).trans rhs⟩

private noncomputable instance (rho a b u v : ℕ) : Decidable (Local rho a b u v) := by
  unfold Local
  split <;> infer_instance

def magnitude (a b : ℕ) : ℕ := (b^2-2*a^2)+(2*a^2-b^2)

private def scales : List ℕ := [1,2,3,4,6,12]
private def classes : List ℕ := [1,5,7,11,13,17,19,23]

private theorem finite_table : ∀ rho ∈ classes, ∀ a ∈ scales, ∀ b ∈ scales,
    a.Coprime b → a≠b → ∀ u ∈ List.range 43, let v := magnitude a b/u
    u*v=magnitude a b → 2*max u v<3*b+4*a → Local rho a b u v →
    (rho=5 ∨ rho=17) ∧ a=2 ∧ b=3 ∧ u=1 ∧ v=1 := by decide +kernel

/-- Completeness of the finite classification. Both assignments of the
ordered divisors u,v are included. Square multiples and equal magnitudes
are excluded by coprimality and by a≠b. -/
theorem only_template {rho a b u v : ℕ} (res : rho<24) (unit : rho.Coprime 6)
    (ap : 0<a) (bp : 0<b) (da : 2*a∣24) (db : 2*b∣24) (primitive : a.Coprime b) (unequal : a≠b)
    (up : 0<u) (allocation : u*v=magnitude a b) (cap : 2*max u v<3*b+4*a)
    (integral : Local rho a b u v) : (rho=5 ∨ rho=17) ∧ a=2 ∧ b=3 ∧ u=1 ∧ v=1 := by
  have scale_table : ∀ n : Fin 13, 0<n.val → 2*n.val∣24 → n.val∈scales := by decide +kernel
  have class_table : ∀ n : Fin 24, n.val.Coprime 6 → n.val∈classes := by decide +kernel
  have ab := Nat.le_of_dvd (by decide : 0<24) da
  have bb := Nat.le_of_dvd (by decide : 0<24) db
  have h := finite_table rho (class_table ⟨rho,res⟩ unit) a (scale_table ⟨a,by omega⟩ ap da)
    b (scale_table ⟨b,by omega⟩ bp db) primitive unequal u (List.mem_range.mpr (by omega))
  dsimp only at h
  rw [←allocation,Nat.mul_div_cancel_left _ up] at h
  exact h rfl cap integral

/-- Absolute label equations cover the two signs and both orientations of the
ordered allocation. The variable written first always accompanies the smaller
factor p. -/
def Rows (p q a b u v t s : ℕ) : Prop :=
  let U := u*p
  let V := v*q
  let dist := (U-V)+(V-U)
  if 2*a^2≤b^2 then U+V=2*(b*t) ∧ dist=2*(a*s)
  else dist=2*(b*t) ∧ U+V=2*(a*s)

private theorem diff_residue {U V m x : ℕ} (h : (U-V)+(V-U)=m*x) : U%m=V%m := by
  rcases le_total U V with le|le
  · rw [Nat.sub_eq_zero_of_le le,zero_add] at h
    exact (Nat.modEq_iff_dvd' le).mpr ⟨x,h⟩
  · rw [Nat.sub_eq_zero_of_le le,add_zero] at h
    exact ((Nat.modEq_iff_dvd' le).mpr (show m∣U-V from ⟨x,h⟩)).symm

/-- End-to-end necessity for an actual negative pair generated by these
primitive templates, including the finite parameter restrictions. -/
theorem classify_rows {p q a b u v t s : ℕ} (ord : p≤q) (bal : q≤2*p)
    (pc : p.Coprime 6) (nc : (p*q%24).Coprime 6) (ap : 0<a) (bp : 0<b)
    (da : 2*a∣24) (db : 2*b∣24) (primitive : a.Coprime b) (unequal : a≠b)
    (up : 0<u) (allocation : u*v=magnitude a b) (first : t^2<p*q) (second : s^2<2*(p*q))
    (rows : Rows p q a b u v t s) :
    (p*q%24=5 ∨ p*q%24=17) ∧ a=2 ∧ b=3 ∧ u=1 ∧ v=1 := by
  have redA := product_reduction (q:=q) pc da u v
  have redB := product_reduction (q:=q) pc db u v
  dsimp only at redA redB
  unfold Rows at rows
  dsimp only at rows
  have packed : u*p≤b*t+a*s ∧ v*q≤b*t+a*s := by split at rows <;> omega
  apply only_template (Nat.mod_lt _ (by decide)) nc ap bp da db primitive unequal up allocation
    (height_filter ord bal ap bp first second packed.1 packed.2)
  unfold Local
  split <;> rename_i h
  · rw [if_pos h] at rows
    refine ⟨redB.1.mp ?_,redA.2.mp (diff_residue (x:=s) (by simpa [Nat.mul_assoc] using rows.2))⟩
    rw [rows.1,←Nat.mul_assoc,Nat.mul_mod_right]
  · rw [if_neg h] at rows
    refine ⟨redB.2.mp (diff_residue (x:=t) (by simpa [Nat.mul_assoc] using rows.1)),redA.1.mp ?_⟩
    rw [rows.2,←Nat.mul_assoc,Nat.mul_mod_right]

/-- The public raw scan of odd t in the balanced band contains at least
2^1016 distinct positions on every 2048-bit product. This statement counts
a full scan, irrespective of the first hit or any further residue filters. -/
theorem schedule_many {n : ℕ} (size : 2^2047≤n) :
    ∃ base : ℕ, Odd base ∧ ∀ i < 2^1016,
      n ≤ 9*(base+2*i)^2 ∧ 8*(base+2*i)^2 ≤ n := by
  let r := n.sqrt
  have large : 2^1023≤r := Nat.le_sqrt'.mpr ((show ((2:ℕ)^1023)^2≤2^2047 by decide +kernel).trans size)
  refine ⟨2*(r/6)+3,⟨r/6+1,by omega⟩,?_⟩
  intro i hi
  let t := 2*(r/6)+3+2*i
  change n≤9*t^2 ∧ 8*t^2≤n
  have start : r+1 ≤ 3*t := by dsimp [t]; omega
  have last : 20*t ≤ 7*r := by dsimp [t]; omega
  constructor
  · nlinarith only [Nat.pow_le_pow_left start 2,(show n<(r+1)^2 from Nat.lt_succ_sqrt' n)]
  · nlinarith only [Nat.pow_le_pow_left last 2,(show r^2≤n from Nat.sqrt_le' n),Nat.zero_le (r^2)]

end PrimeFactors.MixedNegativeTemplates
