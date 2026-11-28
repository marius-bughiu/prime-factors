import PrimeFactors.FractionalRoughMatchedPairs
import Mathlib.Tactic.NormNum.Prime

/-! A short public arithmetic progression of moduli in a fixed relative
interval. All estimates use the symbolic primorial upper bound. -/
namespace PrimeFactors.FractionalSelectedProgression

open Finset

/-- Shift a prescribed residue to the half-open interval of one full period
beginning at x. -/
theorem representative {A : ℕ} (pos : 0<A) (x t : ℕ) :
    ∃ m : ℕ, x≤m ∧ m<x+A ∧ m≡t [MOD A] := by
  let z := t+(A-x%A)
  refine ⟨x+z%A,Nat.le_add_right ..,Nat.add_lt_add_left (Nat.mod_lt z pos) _,?_⟩
  have move : x+z=t+A*(x/A+1) := by
    dsimp [z]
    rw [Nat.mul_add,Nat.mul_one]
    have h := Nat.mod_add_div x A
    have room := Nat.mod_lt x pos
    omega
  apply ((Nat.mod_modEq z A).add_left x).trans
  rw [move]
  simp [Nat.ModEq]

theorem aux_coprime : (primorial 1000).Coprime 1009 := by
  have prime : Nat.Prime 1009 := by norm_num
  apply (prime.coprime_iff_not_dvd.mpr _).symm
  intro dv
  unfold primorial at dv
  obtain ⟨s,hs,st⟩ := (prime.prime.dvd_finset_prod_iff _).mp dv
  obtain ⟨limit,sp⟩ := mem_filter.mp hs
  have small := mem_range.mp limit
  have big := Nat.le_of_dvd sp.pos st
  omega

private theorem block (n P : ℕ) (period_pos : 0<P) (cop : P.Coprime 1009)
    (slack : 7992000*(3*(P*1009)) ≤ n) :
    let A := P*1009
    ∃ m : ℕ, ∀ i : ℕ, i<3 → 7992*(m+i*A)≤n ∧ n≤8000*(m+i*A) ∧
      (m+i*A)≡n [MOD P] ∧ 2*(m+i*A)≡n [MOD 1009] := by
  let A := P*1009
  change ∃ m : ℕ, ∀ i : ℕ, i<3 → 7992*(m+i*A)≤n ∧ n≤8000*(m+i*A) ∧
    (m+i*A)≡n [MOD P] ∧ 2*(m+i*A)≡n [MOD 1009]
  change 7992000*(3*A)≤n at slack
  have ap : 0<A := Nat.mul_pos period_pos (by decide)
  obtain ⟨t,first,second⟩ := Nat.chineseRemainder cop n (505*n)
  obtain ⟨m,lo,hi,same⟩ := representative ap (n/8000+1) t
  have inv : 2*505 ≡ 1 [MOD 1009] := by decide
  have doubled : 2*t ≡ n [MOD 1009] := (second.mul_left 2).trans
    (by simpa only [Nat.mul_assoc,one_mul] using inv.mul_right n)
  have quotient := Nat.mul_div_le n 8000
  have next_lt := Nat.lt_mul_div_succ n (by decide : 0<8000)
  refine ⟨m,fun i small => ?_⟩
  have scale := Nat.mul_le_mul_right A (by omega : i≤2)
  have stay : m+i*A ≡ t [MOD A] :=
    (show m+i*A ≡ m [MOD A] by simp [Nat.ModEq]).trans same
  have p1 := (stay.of_dvd (dvd_mul_right P 1009)).trans first
  have p2 := (stay.of_dvd (dvd_mul_left 1009 P)).mul_left 2
  exact ⟨by omega,by omega,p1,p2.trans doubled⟩

private theorem slack_2048 : 7992000*(3*(primorial 1000*1009)) ≤ 2^2047 := by
  have grow : primorial 1000≤4^1000 := primorial_le_4_pow 1000
  have mult1 := Nat.mul_le_mul_right 1009 grow
  have mult2 := Nat.mul_le_mul_left 3 mult1
  have mult3 := Nat.mul_le_mul_left 7992000 mult2
  have numeric : 7992000*(3*(4^1000*1009)) ≤ (2:ℕ)^2047 := by decide +kernel
  exact mult3.trans numeric

/-- Every input above the full-width threshold admits three consecutive CRT
representatives in the interval, separated by the public CRT period. -/
theorem three_moduli (n : ℕ) (full : 2^2047≤n) :
    let A := primorial 1000*1009
    ∃ m : ℕ, ∀ i : ℕ, i<3 →
      7992*(m+i*A)≤n ∧ n≤8000*(m+i*A) ∧
      (m+i*A)≡n [MOD primorial 1000] ∧ 2*(m+i*A)≡n [MOD 1009] := by
  exact block n (primorial 1000) (primorial_pos 1000) aux_coprime (slack_2048.trans full)

private theorem take_first {n P A : ℕ}
    (h : ∃ m : ℕ, ∀ i : ℕ, i<3 →
      7992*(m+i*A)≤n ∧ n≤8000*(m+i*A) ∧ (m+i*A)≡n [MOD P] ∧ 2*(m+i*A)≡n [MOD 1009]) :
    ∃ m : ℕ, 7992*m≤n ∧ n≤8000*m ∧ m≡n [MOD P] ∧ 2*m≡n [MOD 1009] := by
  obtain ⟨m,steps⟩ := h
  exact ⟨m,by simpa only [zero_mul,add_zero] using steps 0 (by decide)⟩

theorem exists_modulus (n : ℕ) (full : 2^2047≤n) :
    ∃ m : ℕ, 7992*m≤n ∧ n≤8000*m ∧ m≡n [MOD primorial 1000] ∧ 2*m≡n [MOD 1009] :=
  take_first (P:=primorial 1000) (A:=primorial 1000*1009) (three_moduli n full)

private theorem one_per_prime {r A : ℕ} (prime : r.Prime) (large : 2<r) (step : r.Coprime A) (t : ℕ) :
    (r∣t → ¬r∣t+A) ∧ (r∣t → ¬r∣t+2*A) ∧ (r∣t+A → ¬r∣t+2*A) := by
  have no := prime.coprime_iff_not_dvd.mp step
  have adjacent (v : ℕ) (hit : r∣v) (nextHit : r∣v+A) : False :=
    no ((Nat.dvd_add_right hit).mp nextHit)
  refine ⟨adjacent t,?_,?_⟩
  · intro hit hit2
    have twice := (Nat.dvd_add_right hit).mp hit2
    exact (prime.dvd_mul.mp twice).elim (Nat.not_dvd_of_pos_of_lt (by decide) large) no
  · intro hit hit2
    exact adjacent (t+A) hit (by simpa only [two_mul,Nat.add_assoc] using hit2)

/-- With an invertible step, two odd primes can exclude at most two of
three successive terms. The primes may even be equal. -/
theorem coprime_of_three {p q A : ℕ} (hp : p.Prime) (hq : q.Prime) (pl : 2<p) (ql : 2<q)
    (step : (p*q).Coprime A) (t : ℕ) : ∃ i : ℕ, i<3 ∧ (p*q).Coprime (t+i*A) := by
  obtain ⟨pa,qa⟩ := Nat.coprime_mul_iff_left.mp step
  obtain ⟨p01,p02,p12⟩ := one_per_prime hp pl pa t
  obtain ⟨q01,q02,q12⟩ := one_per_prime hq ql qa t
  have choice : (¬p∣t ∧ ¬q∣t) ∨ (¬p∣t+A ∧ ¬q∣t+A) ∨ (¬p∣t+2*A ∧ ¬q∣t+2*A) := by
    tauto
  have combine {v : ℕ} (h : (¬p∣v) ∧ ¬q∣v) : (p*q).Coprime v :=
    Nat.coprime_mul_iff_left.mpr ⟨hp.coprime_iff_not_dvd.mpr h.1,hq.coprime_iff_not_dvd.mpr h.2⟩
  rcases choice with a|b|c
  · exact ⟨0,by decide,by simpa only [zero_mul,add_zero] using combine a⟩
  · exact ⟨1,by decide,by simpa only [one_mul] using combine b⟩
  · exact ⟨2,by decide,combine c⟩

private theorem coprime_step {r : ℕ} (prime : r.Prime) (large : 1009<r) :
    r.Coprime (primorial 1000*1009) := by
  apply prime.coprime_iff_not_dvd.mpr
  intro dv
  rcases prime.dvd_mul.mp dv with small | aux
  · unfold primorial at small
    obtain ⟨s,hs,dvd⟩ := (prime.prime.dvd_finset_prod_iff _).mp small
    obtain ⟨limit,sp⟩ := mem_filter.mp hs
    have top := mem_range.mp limit
    have low := Nat.le_of_dvd sp.pos dvd
    omega
  · exact Nat.not_dvd_of_pos_of_lt (by decide) large aux

/-- Check the first two representatives for coprimality with the product.
The third is the fallback whenever the first two checks both fail. -/
def select (n t A : ℕ) : ℕ :=
  if n.Coprime t then t else if n.Coprime (t+A) then t+A else t+2*A

/-- The two tests pick a coprime member whenever one of the three is coprime. -/
theorem select_spec {n t A : ℕ} (hit : ∃ i : ℕ, i<3 ∧ n.Coprime (t+i*A)) :
    ∃ i : ℕ, i<3 ∧ select n t A = t+i*A ∧ n.Coprime (select n t A) := by
  unfold select
  split_ifs with first second
  · exact ⟨0,by decide,by simp,first⟩
  · exact ⟨1,by decide,by simp,second⟩
  · obtain ⟨i,small,unit⟩ := hit
    have choices : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases choices with rfl | rfl | rfl
    · simp only [zero_mul,add_zero] at unit
      contradiction
    · simp only [one_mul] at unit
      contradiction
    · exact ⟨2,by decide,rfl,unit⟩

/-- For a full-width semiprime whose two primes exceed 1009, a candidate
in the interval is a unit modulo the product as well as satisfying both
specified CRT conditions. -/
theorem exists_unit_modulus {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (pl : 1009<p) (ql : 1009<q) (full : 2^2047≤p*q) :
    ∃ m : ℕ, 7992*m≤p*q ∧ p*q≤8000*m ∧ m≡p*q [MOD primorial 1000] ∧
      2*m≡p*q [MOD 1009] ∧ (p*q).Coprime m := by
  let A := primorial 1000*1009
  have step : (p*q).Coprime A :=
    Nat.coprime_mul_iff_left.mpr ⟨coprime_step hp pl,coprime_step hq ql⟩
  obtain ⟨t,progression⟩ := three_moduli (p*q) full
  obtain ⟨i,small,eqn,unit⟩ := select_spec (coprime_of_three hp hq (by omega) (by omega) step t)
  obtain ⟨lo,hi,a,b⟩ := progression i small
  refine ⟨select (p*q) t A, ?_⟩
  rw [eqn] at unit ⊢
  exact ⟨lo,hi,a,b,unit⟩

/-- A balanced full-width product puts both primes above every wheel prime. -/
private theorem smaller_large {p q : ℕ} (balance : q<2*p) (full : 2^2047≤p*q) : 8000<p := by
  by_contra! small
  have bound := Nat.mul_le_mul small (by omega : q≤16000)
  exact (not_le_of_gt (by decide +kernel : (8000*16000 : ℕ)<2^2047)) (full.trans bound)

private theorem singleton_with_wheel {p q m H r P : ℕ} (identity : primorial (H+1)=P)
    (hp : p.Prime) (hq : q.Prime) (order : p≤q) (balance : q<2*p) (wide : q<m)
    (scale : p*q≤8*(H+1)*m) (pos : 1≤H) (prime : r.Prime)
    (wheel : m≡p*q [MOD P]) (extra : 2*m≡p*q [MOD r]) (rough : (p*q).Coprime (P*r)) :
    ((FractionalBalancedLifts.pairs (p*q) m).filter fun z => (z.1*z.2).Coprime (P*r)) = {(p,q)} := by
  subst P
  apply FractionalRoughMatchedPairs.singleton hp hq order balance wide scale pos prime
    (Int.natCast_modEq_iff.mpr wheel) _ rough
  exact_mod_cast Int.natCast_modEq_iff.mpr extra

/-- Any modulus satisfying these product-only congruences and scale bound
admits exactly the true pair among matched pairs coprime to the public wheel. -/
theorem singleton_for_modulus {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (order : p≤q)
    (balance : q<2*p) (full : 2^2047≤p*q) (hi : p*q≤8000*m)
    (wheel : m≡p*q [MOD primorial 1000]) (extra : 2*m≡p*q [MOD 1009]) :
    ((FractionalBalancedLifts.pairs (p*q) m).filter fun z =>
      (z.1*z.2).Coprime (primorial 1000*1009)) = {(p,q)} := by
  have large := smaller_large balance full
  have wide : q<m := Nat.lt_of_mul_lt_mul_left
    ((Nat.mul_lt_mul_of_pos_right large hq.pos).trans_le hi)
  have rough : (p*q).Coprime (primorial 1000*1009) := Nat.coprime_mul_iff_left.mpr
    ⟨coprime_step hp (by omega),coprime_step hq (by omega)⟩
  exact singleton_with_wheel (H:=999) (P:=primorial 1000) (r:=1009)
    (congrArg primorial (by decide)) hp hq order balance wide hi (by decide) (by norm_num)
    wheel extra rough

/-- Every full-width balanced prime product admits a coprime modulus in
[N/8000,N/7992]. The two public congruences and the small-prime check
isolate the factor pair in the finite set of matched candidates. -/
theorem full_width {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (order : p≤q)
    (balance : q<2*p) (full : 2^2047≤p*q) :
    ∃ m : ℕ, 7992*m≤p*q ∧ p*q≤8000*m ∧ (p*q).Coprime m ∧
      m≡p*q [MOD primorial 1000] ∧ 2*m≡p*q [MOD 1009] ∧
      ((FractionalBalancedLifts.pairs (p*q) m).filter fun z =>
        (z.1*z.2).Coprime (primorial 1000*1009)) = {(p,q)} := by
  have large := smaller_large balance full
  obtain ⟨m,lo,hi,w,e,unit⟩ := exists_unit_modulus hp hq (by omega) (by omega) full
  exact ⟨m,lo,hi,unit,w,e,singleton_for_modulus hp hq order balance full hi w e⟩

end PrimeFactors.FractionalSelectedProgression
