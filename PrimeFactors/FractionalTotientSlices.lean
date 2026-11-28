import PrimeFactors.FractionalPrefixReadout
import Mathlib.Data.Nat.Totient

/-! Exact counts of coprime and noncoprime positions in two partitions of a
semiprime residue period. Endpoints are open on the left and closed on the right. -/

namespace PrimeFactors.FractionalTotientSlices

open Finset FractionalNonunitPrefix

/-- Coprime positions in a half-open interval. -/
noncomputable def units (n a b : ℕ) := (Ioc a b).filter fun z => z.Coprime n
/-- Noncoprime positions in a half-open interval. -/
noncomputable def excluded (n a b : ℕ) := (Ioc a b).filter fun z => ¬z.Coprime n

private theorem split_count (P : ℕ → Prop) [DecidablePred P] {a b : ℕ} (le : a≤b) :
    ((Ioc 0 a).filter P).card+((Ioc a b).filter P).card=((Ioc 0 b).filter P).card := by
  rw [←Ioc_union_Ioc_eq_Ioc (Nat.zero_le a) le, filter_union,card_union_of_disjoint]
  exact disjoint_left.mpr fun z u v =>
    (not_lt.mpr (mem_Ioc.mp (mem_filter.mp u).1).2) (mem_Ioc.mp (mem_filter.mp v).1).1

private theorem full_units (n : ℕ) : (units n 0 n).card=n.totient := by
  have sets : units n 0 n=(Ico 1 (1+n)).filter n.Coprime := by
    ext z
    simp only [units,mem_filter,mem_Ioc,mem_Ico,Nat.coprime_comm (m:=z) (n:=n)]
    omega
  rw [sets,Nat.filter_coprime_Ico_eq_totient]

private theorem phi_id {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (diff : p≠q) :
    (p*q).totient+(p+q)=p*q+1 := by
  rw [Nat.totient_mul ((Nat.coprime_primes hp hq).mpr diff),Nat.totient_prime hp,Nat.totient_prime hq]
  obtain ⟨a,pa⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
  obtain ⟨b,qb⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne_zero
  rw [pa,qb]
  simp only [Nat.succ_eq_add_one,Nat.add_sub_cancel]
  ring

private theorem just_before {x r k m : ℕ} (hm : 0<m) (hr : 0<r) (rs : r≤m) (eqn : x+r=m*k) :
    x/m+1=k := by
  have upper := (Nat.div_lt_iff_lt_mul hm).mpr (by nlinarith only [eqn,hr] : x<k*m)
  cases k with
  | zero => omega
  | succ u =>
    have lower := (Nat.le_div_iff_mul_le hm).mpr (by nlinarith only [eqn,rs] : u*m≤x)
    omega

/-- Positive endpoints are jm'−1 where m'=(N+1)/m. This leaves the first
block one position shorter than each later block. -/
theorem fractional_endpoint {n m j : ℕ} (hm : 0<m) (dvd : m∣n+1) (jp : 0<j) (jm : j≤m) :
    j*n/m+1=j*((n+1)/m) := by
  apply just_before hm jp jm
  have id := Nat.mul_div_cancel' dvd
  calc j*n+j = j*(n+1) := by ring
       _ = j*(m*((n+1)/m)) := congrArg (j*·) id.symm
       _ = m*(j*((n+1)/m)) := by ring

private theorem swap_div (n a b : ℕ) : n/a/b=n/b/a := by
  rw [Nat.div_div_eq_div_mul,Nat.mul_comm a b,←Nat.div_div_eq_div_mul]

private theorem sum_quotients {a b m : ℕ} (hm : 0<m) (div : m∣a+b) (no : ¬m∣a) :
    a/m+b/m+1=(a+b)/m := by
  have rem : a%m+b%m ≠ 0 := by
    have := fun h => no (Nat.dvd_of_mod_eq_zero (show a%m=0 from h))
    omega
  have z : (a%m+b%m)%m=0 := by rw [←Nat.add_mod,Nat.mod_eq_zero_of_dvd div]
  have carry : m≤a%m+b%m := by
    by_contra! small
    exact rem ((Nat.mod_eq_of_lt small).symm.trans z)
  rw [Nat.add_div hm,if_pos carry]

private theorem interior_units {p q m j : ℕ} (hp : p.Prime) (hq : q.Prime) (diff : p≠q)
    (hm : 0<m) (dn : m∣p*q+1) (ds : m∣p+q) (jp : 0<j) (jm : j<m) :
    (units (p*q) 0 (j*(p*q)/m)).card=j*((p*q).totient/m) := by
  let n := p*q
  have short : j*n/m<n := (Nat.div_lt_iff_lt_mul hm).mpr (by
    simpa only [Nat.mul_comm n m] using Nat.mul_lt_mul_of_pos_right jm (Nat.mul_pos hp.pos hq.pos))
  have non := count_to hp hq diff _ short
  have l : j*(p*q)/m/p=j*q/m := by
    rw [swap_div,show j*(p*q)=p*(j*q) by ring,Nat.mul_div_cancel_left _ hp.pos]
  have r : j*(p*q)/m/q=j*p/m := by
    rw [swap_div,show j*(p*q)=(j*p)*q by ring,Nat.mul_div_cancel _ hq.pos]
  change (nonunits n (j*n/m)).card=j*(p*q)/m/p+j*(p*q)/m/q at non
  rw [l,r] at non
  have copN : n.Coprime m := (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right n)).of_dvd_right dn
  have copP : m.Coprime p := (copN.of_dvd_left (dvd_mul_right p q)).symm
  have no : ¬m∣j*p := fun h => (Nat.not_dvd_of_pos_of_lt jp jm) (copP.dvd_mul_right.mp h)
  have carry := sum_quotients (a:=j*p) (b:=j*q) hm (by rw [←Nat.mul_add]; exact dvd_mul_of_dvd_right ds j) no
  rw [←Nat.mul_add,Nat.mul_div_assoc j ds] at carry
  have sizes := filter_card_add_filter_neg_card_eq_card (s:=Ioc 0 (j*n/m)) (fun z => z.Coprime n)
  change (units n 0 (j*n/m)).card+(nonunits n (j*n/m)).card=(Ioc 0 (j*n/m)).card at sizes
  rw [Nat.card_Ioc,Nat.sub_zero] at sizes
  have stop := fractional_endpoint hm dn jp jm.le
  have phi := phi_id hp hq diff
  have block : (n+1)/m=(p*q).totient/m+(p+q)/m := by
    change (p*q+1)/m=_
    rw [←phi]
    nth_rw 1 [←Nat.mul_div_cancel' ds]
    rw [Nat.add_mul_div_left _ _ hm]
  change j*n/m+1=j*((n+1)/m) at stop
  rw [block,Nat.mul_add] at stop
  change (units n 0 (j*n/m)).card=_
  omega

private theorem units_prefix {p q m j : ℕ} (hp : p.Prime) (hq : q.Prime) (diff : p≠q)
    (hm : 0<m) (dn : m∣p*q+1) (ds : m∣p+q) (jm : j≤m) :
    (units (p*q) 0 (j*(p*q)/m)).card=j*((p*q).totient/m) := by
  rcases eq_or_lt_of_le jm with rfl|lt
  · have h := phi_id hp hq diff
    have dv := Nat.dvd_sub dn ds
    rw [←h,Nat.add_sub_cancel] at dv
    rw [Nat.mul_div_cancel_left _ hm,full_units,Nat.mul_div_cancel' dv]
  · by_cases j0 : j=0
    · simp [j0,units]
    · exact interior_units hp hq diff hm dn ds (by omega) lt

/-- Under N≡−1 and p+q≡0 modulo m, all m fractional-width blocks contain
exactly φ(N)/m units, including the final block ending at N. -/
theorem fractional_units {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (diff : p≠q)
    (hm : 0<m) (dn : m∣p*q+1) (ds : m∣p+q) {j : ℕ} (jm : j<m) :
    (units (p*q) (j*(p*q)/m) ((j+1)*(p*q)/m)).card=(p*q).totient/m := by
  have le := Nat.div_le_div_right (Nat.mul_le_mul_right (p*q) (Nat.le_succ j)) (c:=m)
  have split := split_count (fun z => z.Coprime (p*q)) le
  change (units _ 0 _).card+(units _ _ _).card=(units _ 0 _).card at split
  rw [units_prefix hp hq diff hm dn ds jm.le,units_prefix hp hq diff hm dn ds jm,Nat.succ_mul j ((p*q).totient/m)] at split
  exact Nat.add_left_cancel split

/-- The integer lengths of the fractional-width blocks differ only at the
first block, where excluding zero leaves one fewer position. -/
theorem fractional_lengths {n m j : ℕ} (hm : 0<m) (dn : m∣n+1) (jm : j<m) :
    (Ioc (j*n/m) ((j+1)*n/m)).card = if j=0 then (n+1)/m-1 else (n+1)/m := by
  rw [Nat.card_Ioc]
  let K := (n+1)/m
  have hi : (j+1)*n/m+1=j*K+K :=
    (fractional_endpoint hm dn (show 0<j+1 by omega) jm).trans (Nat.succ_mul j K)
  split_ifs with z
  · subst j
    simp only [zero_add,zero_mul,one_mul,Nat.zero_div,Nat.sub_zero] at hi ⊢
    exact Nat.eq_sub_of_add_eq hi
  · have lo : j*n/m+1=j*K := fractional_endpoint hm dn (by omega) jm.le
    have step : (j+1)*n/m+1=(j*n/m+K)+1 := calc
      _ = j*K+K := hi
      _ = (j*n/m+1)+K := congrArg (·+K) lo.symm
      _ = _ := by omega
    rw [Nat.add_right_cancel step,Nat.add_sub_cancel_left]

theorem divisor24_units {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (diff : p≠q)
    (hm : 2≤m) (d24 : m∣24) (dn : m∣p*q+1) {j : ℕ} (jm : j<m) :
    (units (p*q) (j*(p*q)/m) ((j+1)*(p*q)/m)).card=(p*q).totient/m := by
  apply fractional_units hp hq diff (by omega) dn _ jm
  exact ⟨_,FractionalPrefixReadout.sum_eq hp hq diff hm d24 dn⟩

private theorem below_div {p q : ℕ} (pp : 0<p) (qp : 0<q) : (p*q-1)/p=q-1 := by
  have eqn : p*q-1+1=p*q := Nat.sub_add_cancel (Nat.mul_pos pp qp)
  have h := just_before pp (by decide : 0<1) pp eqn
  omega

private theorem linear_div {p q m j : ℕ} (pp : 0<p) (qp : 0<q) (hm : 0<m)
    (dp : m∣p-1) (dq : m∣q-1) (jm : j≤m) :
    (j*((p*q-1)/m))/p=j*((q-1)/m) := by
  let a := (p-1)/m
  let b := (q-1)/m
  have P : m*a+1=p := (congrArg (·+1) (Nat.mul_div_cancel' dp)).trans (Nat.sub_add_cancel pp)
  have Q : m*b+1=q := (congrArg (·+1) (Nat.mul_div_cancel' dq)).trans (Nat.sub_add_cancel qp)
  have product : m*(p*b+a)+1=p*q := calc
    m*(p*b+a)+1 = p*(m*b)+(m*a+1) := by ring
    _ = p*(m*b+1) := by rw [P]; ring
    _ = p*q := by rw [Q]
  have width : (p*q-1)/m=p*b+a := by
    rw [show p*q-1=m*(p*b+a) by omega,Nat.mul_div_cancel_left _ hm]
  have small : j*a<p := (Nat.mul_le_mul_right a jm).trans_lt (by omega)
  rw [width,show j*(p*b+a)=j*a+p*(j*b) by ring,Nat.add_mul_div_left _ _ pp,Nat.div_eq_of_lt small,zero_add]

/-- For m equal integer-length blocks of 1,…,N−1, every block has the same
nonunit count precisely when both primes are 1 modulo m. -/
theorem integer_blocks {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (diff : p≠q)
    (hm : 0<m) (dn : m∣p*q-1) :
    let H := (p*q-1)/m
    (∃ c : ℕ, ∀ j<m, (excluded (p*q) (j*H) ((j+1)*H)).card=c) ↔ m∣p-1 ∧ m∣q-1 := by
  let H := (p*q-1)/m
  have width : m*H=p*q-1 := Nat.mul_div_cancel' dn
  have pos := Nat.mul_pos hp.pos hq.pos
  have short {j : ℕ} (jm : j≤m) : j*H<p*q :=
    (Nat.mul_le_mul_right H jm).trans_lt (by omega)
  have step (j : ℕ) :
      (nonunits (p*q) (j*H)).card+(excluded (p*q) (j*H) ((j+1)*H)).card=
      (nonunits (p*q) ((j+1)*H)).card :=
    split_count (fun z => ¬z.Coprime (p*q)) (Nat.mul_le_mul_right H (Nat.le_succ j))
  have P := below_div hp.pos hq.pos
  have Q : (p*q-1)/q=p-1 := by simpa only [Nat.mul_comm q p] using below_div hq.pos hp.pos
  constructor
  · rintro ⟨c,hc⟩
    have upto (j : ℕ) (jm : j≤m) : (nonunits (p*q) (j*H)).card=j*c := by
      induction j with
      | zero => simp [nonunits]
      | succ j ih =>
        have h := step j
        rw [ih (by omega),hc j (by omega)] at h
        exact h.symm.trans (Nat.succ_mul j c).symm
    have total := upto m le_rfl
    rw [width,count_to hp hq diff _ (by omega),P,Q] at total
    have one := upto 1 hm
    rw [one_mul,one_mul,count_to hp hq diff _ (by simpa using short (j:=1) hm)] at one
    change (p*q-1)/m/p+(p*q-1)/m/q=c at one
    rw [swap_div _ m p,swap_div _ m q,P,Q] at one
    rw [←one,Nat.mul_add] at total
    have rp := Nat.mod_add_div (p-1) m
    have rq := Nat.mod_add_div (q-1) m
    exact ⟨Nat.dvd_of_mod_eq_zero (by omega),Nat.dvd_of_mod_eq_zero (by omega)⟩
  · rintro ⟨dp,dq⟩
    let c := (q-1)/m+(p-1)/m
    have upto (j : ℕ) (jm : j≤m) : (nonunits (p*q) (j*H)).card=j*c := by
      have a := linear_div hp.pos hq.pos hm dp dq jm
      have b : j*((p*q-1)/m)/q=j*((p-1)/m) := by
        simpa only [Nat.mul_comm q p] using linear_div hq.pos hp.pos hm dq dp jm
      change (nonunits (p*q) (j*((p*q-1)/m))).card=_
      rw [count_to hp hq diff _ (short jm),a,b,Nat.mul_add]
    refine ⟨c,?_⟩
    intro j jm
    have total := step j
    rw [upto j jm.le,upto (j+1) jm,Nat.succ_mul j c] at total
    exact Nat.add_left_cancel total

/-- All 24 fractional slices of 2183 have 87 units. In the integer
partition of 1,…,64 into eight blocks, divisibility of the total of 16
nonunits by eight alone is insufficient. The first block’s only nonunit is 5. -/
theorem example_slices :
    (∀ j<24, (units 2183 (j*2183/24) ((j+1)*2183/24)).card=87) ∧
    (excluded 65 0 8)={5} ∧ ¬∃ c : ℕ, ∀ j<8, (excluded 65 (j*8) ((j+1)*8)).card=c := by
  constructor
  · intro j hj
    have h := divisor24_units (p:=37) (q:=59) (m:=24) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hj
    rw [Nat.totient_mul (by decide),Nat.totient_prime (by decide : (37:ℕ).Prime),
      Nat.totient_prime (by decide : (59:ℕ).Prime)] at h
    norm_num at h
    exact h
  · refine ⟨by decide +kernel,?_⟩
    exact (integer_blocks (p:=5) (q:=13) (m:=8) (by decide) (by decide) (by decide)
      (by decide) (by decide)).not.mpr (by decide)

end PrimeFactors.FractionalTotientSlices
