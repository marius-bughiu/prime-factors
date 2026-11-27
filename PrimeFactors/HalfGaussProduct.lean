import Mathlib.NumberTheory.Wilson
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic

/-! The Gauss factorial of the first half of a reduced residue system.
On two distinct odd primes its residues are explicit signed Legendre symbols. -/
namespace PrimeFactors.HalfGaussProduct
open Finset

/-- Product of positive integers up to m which are units modulo n. -/
noncomputable def unitProduct (n m : ℕ) : ℕ :=
  ∏ i ∈ range m, if (i+1).Coprime n then i+1 else 1

noncomputable def half (n : ℕ) : ℕ := unitProduct n (n/2)

/-- A product with only the multiples of p omitted, on a progression. -/
private def run (p a m : ℕ) : ZMod p :=
  ∏ i ∈ range m, if p ∣ a*(i+1) then 1 else ((a*(i+1):ℕ):ZMod p)

private theorem step (p a m : ℕ) : run p a (m+1) =
    run p a m * (if p ∣ a*(m+1) then 1 else ((a*(m+1):ℕ):ZMod p)) :=
  prod_range_succ _ _

private theorem separate {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (m : ℕ) :
    run p 1 m = ((unitProduct (p*q) m : ℕ):ZMod p)*run p q (m/q) := by
  induction m with
  | zero => simp [run,unitProduct]
  | succ m ih =>
    rw [step,one_mul,show unitProduct (p*q) (m+1) = unitProduct (p*q) m *
      (if (m+1).Coprime (p*q) then m+1 else 1) from prod_range_succ _ _]
    have unit : (m+1).Coprime (p*q) ↔ ¬ p∣m+1 ∧ ¬ q∣m+1 := by
      rw [Nat.coprime_mul_iff_right]
      exact and_congr (Nat.coprime_comm.trans pp.coprime_iff_not_dvd) (Nat.coprime_comm.trans qp.coprime_iff_not_dvd)
    by_cases hq : q∣m+1
    · have exactMultiple : q*(m/q+1)=m+1 := by
        rw [← Nat.succ_div_of_dvd hq, Nat.mul_div_cancel' hq]
      have neg : ¬(m+1).Coprime (p*q) := fun c => (unit.mp c).2 hq
      rw [Nat.succ_div_of_dvd hq,step,exactMultiple,if_neg neg,mul_one,ih,mul_assoc]
    · rw [Nat.succ_div_of_not_dvd hq,ih]
      by_cases hp : p∣m+1 <;> simp [hp,hq,unit,mul_comm,mul_assoc,mul_left_comm]

private theorem partial_run {p a t : ℕ} (pp : p.Prime) (ha : ¬p∣a) (small : t<p) :
    run p a t = (a:ZMod p)^t * (t.factorial:ZMod p) := by
  rw [run,← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod]
  calc
    _ = ∏ i∈range t, (a:ZMod p)*((i+1:ℕ):ZMod p) := by
      apply prod_congr rfl
      intro i hi
      have ni : ¬p∣i+1 := by
        intro d
        have := Nat.le_of_dvd (Nat.zero_lt_succ i) d
        have := mem_range.mp hi
        omega
      rw [if_neg (fun h => (pp.dvd_mul.mp h).elim ha ni),Nat.cast_mul]
    _ = _ := by rw [prod_mul_distrib]; simp

private theorem block {p : ℕ} [Fact p.Prime] : run p 1 p = -1 := by
  have pp := Fact.out (p:=p.Prime)
  have positive := pp.pos
  have eq : p-1+1=p := by omega
  conv_lhs => arg 3; rw [←eq]
  rw [step,eq,one_mul,if_pos dvd_rfl,mul_one,partial_run pp (by simpa using pp.ne_one) (by omega),
    Nat.cast_one,one_pow,one_mul,ZMod.wilsons_lemma]

private theorem repeat_block {p : ℕ} [Fact p.Prime] (b t : ℕ) :
    run p 1 (b*p+t)=(-1:ZMod p)^b * run p 1 t := by
  induction b with
  | zero => simp
  | succ b ih =>
    have size : (b+1)*p+t=p+(b*p+t) := by ring
    rw [size,run,prod_range_add]
    change run p 1 p * _ = _
    rw [block,pow_succ,mul_comm ((-1:ZMod p)^b) (-1),mul_assoc]
    congr 1
    rw [← ih,run]
    apply prod_congr rfl
    intro i _
    simp only [one_mul, Nat.cast_add, ZMod.natCast_self, zero_add]
    simp only [add_assoc, Nat.dvd_add_right dvd_rfl]

/-- Modulo either prime, the long product collapses to one Legendre symbol
and the parity of the other prime's half. -/
theorem local_value {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (oddq : q%2=1) (distinct : p≠q) :
    (half (p*q):ZMod p) = (((-1:ℤ)^(q/2)*legendreSym p q : ℤ):ZMod p) := by
  have pp := Fact.out (p:=p.Prime)
  have qp := Fact.out (p:=q.Prime)
  have nd : ¬p∣q := fun h => distinct ((Nat.prime_dvd_prime_iff_eq pp qp).mp h)
  have small : p/2<p := Nat.div_lt_self pp.pos (by decide)
  have decomp : (p*q)/2=(q/2)*p+p/2 := by
    have eq : q=2*(q/2)+1 := by omega
    have prod : p*q=2*((q/2)*p)+p := calc
      _ = p*(2*(q/2)+1) := congrArg (p*·) eq
      _ = _ := by ring
    omega
  have bins : (p*q/2)/q=p/2 := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_div_mul_right _ _ qp.pos]
  have separate' := separate pp qp (p*q/2)
  change run p 1 (p*q/2)=(half (p*q):ZMod p)*run p q (p*q/2/q) at separate'
  rw [decomp,repeat_block,partial_run pp (by simpa using pp.ne_one) small,Nat.cast_one,one_pow,one_mul] at separate'
  rw [← decomp,bins,partial_run pp nd small,←mul_assoc] at separate'
  have fac : (↑(p/2).factorial:ZMod p) ≠ 0 :=
    fun h => (not_le_of_gt small) (pp.dvd_factorial.mp ((ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp h))
  have cancelled := mul_right_cancel₀ fac separate'
  have nq : ((q:ℤ):ZMod p)≠0 := by simpa using (show (q:ZMod p)≠0 from fun h => nd ((ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp h))
  have sq := congrArg (fun z : ℤ => (z:ZMod p)) (legendreSym.sq_one p nq)
  push_cast at sq
  have euler := legendreSym.eq_pow p (q:ℤ)
  push_cast at euler
  rw [←euler] at cancelled
  push_cast
  linear_combination (norm := ring_nf) -(legendreSym p q:ZMod p)*cancelled - (half (p*q):ZMod p)*sq

/-- Canonical public residue in the range [0,n). -/
noncomputable def residue (n : ℕ) : ℕ := half n % n

private def localSign (p q : ℕ) [Fact p.Prime] : ℤ := (-1)^(q/2)*legendreSym p q

private theorem sign_formula {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (oq : q%2=1) (ne : p≠q) :
    (residue (p*q):ZMod p)=(localSign p q : ZMod p) := by
  refine Eq.trans ?_ (local_value oq ne)
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
  exact (Nat.mod_modEq _ _).of_dvd (dvd_mul_right p q)

private theorem signs {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (op : p%2=1) (oq : q%2=1) :
    localSign q p = (if p%4=1 ∧ q%4=1 then 1 else -1) * localSign p q := by
  have hp : p%4=1 ∨ p%4=3 := by omega
  have hq : q%4=1 ∨ q%4=3 := by omega
  rcases hp with hp|hp <;> rcases hq with hq|hq
  · rw [localSign,localSign,ZMod.neg_one_pow_div_two_of_one_mod_four hp,
      ZMod.neg_one_pow_div_two_of_one_mod_four hq,
      legendreSym.quadratic_reciprocity_one_mod_four hp (by omega : q≠2)]
    simp [hp,hq]
  · rw [localSign,localSign,ZMod.neg_one_pow_div_two_of_one_mod_four hp,
      ZMod.neg_one_pow_div_two_of_three_mod_four hq,
      legendreSym.quadratic_reciprocity_one_mod_four hp (by omega : q≠2)]
    simp [hq]
  · rw [localSign,localSign,ZMod.neg_one_pow_div_two_of_three_mod_four hp,
      ZMod.neg_one_pow_div_two_of_one_mod_four hq,
      legendreSym.quadratic_reciprocity_one_mod_four hq (by omega : p≠2)]
    simp [hp]
  · rw [localSign,localSign,ZMod.neg_one_pow_div_two_of_three_mod_four hp,
      ZMod.neg_one_pow_div_two_of_three_mod_four hq,
      legendreSym.quadratic_reciprocity_three_mod_four hp hq]
    simp [hp]

private theorem sign_unit {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (ne : p≠q) :
    localSign p q=1 ∨ localSign p q= -1 := by
  have pp := Fact.out (p:=p.Prime)
  have qp := Fact.out (p:=q.Prime)
  have nq : ((q:ℤ):ZMod p)≠0 := by
    intro zero
    have h : (q:ZMod p)=0 := by simpa using zero
    exact ne ((Nat.prime_dvd_prime_iff_eq pp qp).mp ((ZMod.natCast_zmod_eq_zero_iff_dvd q p).mp h))
  have square : (localSign p q)^2=1 := by
    rw [localSign,mul_pow,legendreSym.sq_one p nq,mul_one,←pow_mul,Nat.mul_comm,pow_mul]
    norm_num
  exact sq_eq_one_iff.mp square

private theorem mixed_gcd {h p q : ℕ} [Fact q.Prime] (oq : q%2=1)
    (pl : (h:ZMod p)= -1) (qr : (h:ZMod q)=1) : (p*q).gcd (h+1)=p := by
  have qp := Fact.out (p:=q.Prime)
  have dp : p∣h+1 := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp (by push_cast; rw [pl]; ring)
  have nq : ¬q∣h+1 := by
    intro hd
    have z := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr hd
    have two : (2:ZMod q)=0 := by
      push_cast at z
      rw [qr] at z
      convert z using 1
      ring
    have bad := (ZMod.natCast_zmod_eq_zero_iff_dvd 2 q).mp (by exact_mod_cast two)
    rcases (Nat.dvd_prime Nat.prime_two).mp bad with h|h <;> have := qp.two_le <;> omega
  rw [Nat.mul_comm p q]
  exact Nat.gcd_mul_of_coprime_of_dvd (qp.coprime_iff_not_dvd.mpr nq) dp

/-- One gcd splits the product whenever at least one prime is 3 modulo 4. -/
theorem recover {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (op : p%2=1)
    (oq : q%2=1) (ne : p≠q) (mixed : p%4=3 ∨ q%4=3) :
    (p*q).gcd (residue (p*q)+1)=p ∨ (p*q).gcd (residue (p*q)+1)=q := by
  have left := sign_formula oq ne
  have right := sign_formula op ne.symm
  rw [Nat.mul_comm q p] at right
  have rel := signs op oq
  simp only [if_neg (show ¬(p%4=1 ∧ q%4=1) by omega),neg_one_mul] at rel
  rw [rel] at right
  rcases sign_unit ne with plus|minus
  · simp only [plus,Int.cast_one,Int.cast_neg] at left right
    exact Or.inr (by simpa only [Nat.mul_comm q p] using mixed_gcd op right left)
  · simp only [minus,Int.cast_one,Int.cast_neg,neg_neg] at left right
    exact Or.inl (mixed_gcd oq left right)

/-- For two primes equal to 1 modulo 4 the only possible outputs are the
two global signs. -/
theorem trivial_residue {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp : p%4=1)
    (hq : q%4=1) (ne : p≠q) :
    (residue (p*q):ZMod (p*q))=1 ∨ (residue (p*q):ZMod (p*q))= -1 := by
  have pp := Fact.out (p:=p.Prime)
  have qp := Fact.out (p:=q.Prime)
  have cop := (Nat.coprime_primes pp qp).mpr ne
  have op : p%2=1 := by omega
  have oq : q%2=1 := by omega
  have left := sign_formula oq ne
  have right := sign_formula op ne.symm
  rw [Nat.mul_comm q p, signs op oq,if_pos ⟨hp,hq⟩,one_mul] at right
  let r := residue (p*q)
  have crt : (↑(r:ℕ):ZMod (p*q))=(localSign p q:ZMod (p*q)) := by
    apply sub_eq_zero.mp
    have dz (v : ℕ) (h : (r:ZMod v)=(localSign p q:ZMod v)) : (v:ℤ) ∣ (r:ℤ)-localSign p q := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      exact sub_eq_zero.mpr h
    have both := Int.isCoprime_iff_gcd_eq_one.mpr (by exact cop : Int.gcd (p:ℤ) (q:ℤ)=1)
    have d := both.mul_dvd (dz p left) (dz q right)
    have z := (ZMod.intCast_zmod_eq_zero_iff_dvd ((r:ℤ)-localSign p q) (p*q)).mpr (by exact_mod_cast d)
    simpa using z
  rcases sign_unit ne with h|h
  · exact Or.inl (by simpa [h] using crt)
  · exact Or.inr (by simpa [h] using crt)

private theorem signs_on_range {R : Type*} [CommRing R] (f : ℕ → R)
    (choose : ℕ → Prop) [DecidablePred choose] (m : ℕ) :
    (∏ i ∈ range m, if choose i then -f i else f i) = ∏ i ∈ range m, f i ∨
    (∏ i ∈ range m, if choose i then -f i else f i) = -(∏ i ∈ range m, f i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [prod_range_succ]
    by_cases pick : choose m <;> rcases ih with plus|minus <;> simp_all

/-- Switch any chosen positive unit to its negative representative. Even a
choice depending on the whole input can change only the overall sign. -/
theorem signed_representatives (n : ℕ) (flip : ℕ → Bool) :
    let chosen : ZMod n := ∏ i ∈ range (n/2),
      if (i+1).Coprime n then (if flip (i+1) then -((i+1:ℕ):ZMod n) else ((i+1:ℕ):ZMod n)) else 1
    chosen=(residue n:ZMod n) ∨ chosen= -(residue n:ZMod n) := by
  let f (i : ℕ) : ZMod n := if (i+1).Coprime n then ((i+1:ℕ):ZMod n) else 1
  have base : (residue n:ZMod n)=∏ i ∈ range (n/2), f i := by
    simp [residue,half,unitProduct,f,Nat.cast_prod]
  dsimp only
  rw [base]
  convert signs_on_range f (fun i => (i+1).Coprime n ∧ flip (i+1)=true) (n/2) using 2 <;>
    apply prod_congr rfl <;> intro i _ <;> dsimp only [f] <;> split_ifs <;> simp_all

/-- H differs by one from a multiple of the designated prime q, with
coefficient prime to p. Thus an approximation to H is also an approximation
to a proper multiple of the larger prime when p < q. -/
theorem near_multiple {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (op : p%2=1)
    (oq : q%2=1) (ne : p≠q) (mixed : p%4=3 ∨ q%4=3) :
    ∃ k : ℤ, ¬(p:ℤ)∣k ∧ |(q:ℤ)*k-residue (p*q)|=1 := by
  let r := residue (p*q)
  let s := localSign p q
  have pl : (r:ZMod p)=(s:ZMod p) := sign_formula oq ne
  have qr := sign_formula op ne.symm
  rw [Nat.mul_comm q p,signs op oq,if_neg (show ¬(p%4=1 ∧ q%4=1) by omega),neg_one_mul,Int.cast_neg] at qr
  have divide : (q:ℤ) ∣ (r:ℤ)+s := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    change (residue (p*q):ZMod q)+(localSign p q:ZMod q)=0
    rw [qr,neg_add_cancel]
  have exclude : ¬(p:ℤ) ∣ (r:ℤ)+s := by
    intro h
    have zero := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    push_cast at zero
    rw [pl] at zero
    have two : (2:ZMod p)=0 := by
      rcases (show s=1 ∨ s= -1 from sign_unit ne) with plus|minus
      · rw [plus,Int.cast_one] at zero
        linear_combination zero
      · rw [minus,Int.cast_neg,Int.cast_one] at zero
        linear_combination -zero
    have pd := (ZMod.natCast_zmod_eq_zero_iff_dvd 2 p).mp (by exact_mod_cast two)
    have low := (Fact.out (p:=p.Prime)).two_le
    rcases (Nat.dvd_prime Nat.prime_two).mp pd with h|h <;> omega
  obtain ⟨k,hk⟩ := divide
  use k
  constructor
  · exact fun pk => exclude (hk ▸ dvd_mul_of_dvd_right pk _)
  · change |(q:ℤ)*k-r|=1
    rw [←hk,add_sub_cancel_left]
    rcases (show s=1 ∨ s= -1 from sign_unit ne) with h|h <;> norm_num [h]

/-- Numerical slack for the published approximation-to-a-multiple theorem
with threshold 2·N^(1/4), at all full-size inputs. -/
theorem full_width_slack {n : ℕ} (bits : 2^2047≤n) : (2^512+1:ℕ)^4 < 16*n := by
  exact lt_of_lt_of_le (by decide +kernel : (2^512+1:ℕ)^4 < 16*2^2047) (Nat.mul_le_mul_left 16 bits)

theorem examples : residue 15=11 ∧ residue 65=64 ∧ residue 77=34 ∧ residue 91=27 := by decide +kernel

end PrimeFactors.HalfGaussProduct
