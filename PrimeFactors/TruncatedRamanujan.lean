import PrimeFactors.FourierAccess
import Mathlib.Tactic

/-! Truncating the principal-character sum at the public integer square
root isolates the smaller prime of a balanced semiprime. -/
namespace PrimeFactors.TruncatedRamanujan
open Finset Real

private theorem square_root_window {p q : ℕ} (pp : p.Prime) (pq : p<q) (balance : q≤2*p) :
    p≤(p*q).sqrt ∧ (p*q).sqrt<q ∧ (p*q).sqrt<2*p := by
  have lo : p≤(p*q).sqrt := Nat.le_sqrt'.mpr (by simpa [sq] using Nat.mul_le_mul_left p pq.le)
  have hi : (p*q).sqrt<q := Nat.sqrt_lt'.mpr
    (by simpa [sq] using Nat.mul_lt_mul_of_pos_right pq (pp.pos.trans pq))
  exact ⟨lo,hi,hi.trans_le balance⟩

/-- In [1,⌊√N⌋], exactly one input to the principal character is zero. -/
theorem puncture {p q x : ℕ} (pp : p.Prime) (qp : q.Prime) (pq : p<q) (balance : q≤2*p)
    (hx : x∈Icc 1 (p*q).sqrt) : (p*q).Coprime x ↔ x≠p := by
  obtain ⟨lo,hi⟩ := mem_Icc.mp hx
  obtain ⟨_,ql,two⟩ := square_root_window pp pq balance
  have qn : ¬q∣x := fun d => (not_le_of_gt (hi.trans_lt ql)) (Nat.le_of_dvd lo d)
  rw [Nat.coprime_mul_iff_left,pp.coprime_iff_not_dvd,qp.coprime_iff_not_dvd,and_iff_left qn]
  constructor
  · rintro n rfl; exact n (dvd_refl _)
  · rintro ne ⟨m,rfl⟩
    have lt : p*m<2*p := hi.trans_lt two
    have msmall : m<2 := by
      by_contra! ge
      have := Nat.mul_le_mul_left p ge
      omega
    have mp : 0<m := by by_contra! hm; interval_cases m; simp at lo
    have eq : m=1 := by omega
    exact ne (by simp [eq])

/-- A public weighted sum minus its principal-character truncation equals
the single missing weight. No separability of the weights is assumed. -/
theorem missing_weight {T : Type*} [AddCommGroup T] {p q : ℕ} (pp : p.Prime) (qp : q.Prime)
    (pq : p<q) (balance : q≤2*p) (w : ℕ→T) :
    (∑ x∈Icc 1 (p*q).sqrt, w x) -
      (∑ x∈Icc 1 (p*q).sqrt, if (p*q).Coprime x then w x else 0) = w p := by
  have mem : p∈Icc 1 (p*q).sqrt := mem_Icc.mpr ⟨pp.pos,(square_root_window pp pq balance).1⟩
  rw [←sum_sub_distrib]
  calc
    _ = ∑ x∈Icc 1 (p*q).sqrt, if x=p then w p else 0 := by
      apply sum_congr rfl
      intro x hx
      simp only [puncture pp qp pq balance hx]
      by_cases e : x=p <;> simp [e]
    _ = _ := by simp [mem]

noncomputable def phase (n k x : ℕ) : ℂ :=
  Complex.exp (((2*π*(k:ℝ)*x/n : ℝ):ℂ)*Complex.I)

/-- The known first sum is a geometric series at any nonzero unit frequency. -/
noncomputable def residual (n k : ℕ) : ℂ :=
  (∑ x∈Icc 1 n.sqrt, phase n k x) -
    ∑ x∈Icc 1 n.sqrt, if n.Coprime x then phase n k x else 0

theorem exact_phase {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (pq : p<q) (balance : q≤2*p)
    (k : ℕ) : residual (p*q) k=phase (p*q) k p := missing_weight pp qp pq balance _

/-- Rotate the complex reading by a known phase and take its real part. -/
noncomputable def rotated (r m : ℕ) (value : ℂ) : ℝ :=
  (value * Complex.exp (((-(2*π*(r:ℝ)/m) : ℝ):ℂ)*Complex.I)).re

private theorem real_reading {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (pq : p<q)
    (balance : q≤2*p) (k r m : ℕ) :
    rotated r m (residual (p*q) k)=Real.cos (2*π*((k:ℝ)*p/(p*q)-(r:ℝ)/m)) := by
  rw [exact_phase pp qp pq balance]; unfold rotated phase
  rw [←Complex.exp_add]
  have eq : (((2*π*(k:ℝ)*p/(p*q:ℕ):ℝ):ℂ)*Complex.I) +
      (((-(2*π*(r:ℝ)/m):ℝ):ℂ)*Complex.I) =
      ((2*π*((k:ℝ)*p/(p*q)-r/m):ℝ):ℂ)*Complex.I := by
    push_cast; ring
  rw [eq,Complex.exp_ofReal_mul_I_re]

private theorem rotated_error (r m : ℕ) (x y : ℂ) :
    |rotated r m x-rotated r m y|≤‖x-y‖ := by
  let u := Complex.exp (((-(2*π*(r:ℝ)/m):ℝ):ℂ)*Complex.I)
  have one : ‖u‖=1 := Complex.norm_exp_ofReal_mul_I _
  calc
    _ = |((x-y)*u).re| := by rw [sub_mul,Complex.sub_re]; rfl
    _ ≤ ‖(x-y)*u‖ := Complex.abs_re_le_norm _
    _ = _ := by rw [norm_mul,one,mul_one]

/-- After the residue modulo w is known, a public floor frequency gives the
next binary digit. The modulus need not divide N. -/
theorem bit_reading {p q w : ℕ} (pp : p.Prime) (qp : q.Prime) (pq : p<q) (balance : q≤2*p)
    (large : 6≤q) (wp : 0<w) {value : ℂ}
    (err : ‖value-residual (p*q) ((p*q)/(2*w))‖ < 1/2) :
    0<rotated (p%w) (2*w) value ↔ (p/w)%2=0 := by
  let m := 2*w
  let k := (p*q)/m
  let rem := (p*q)%m
  let r := p%w
  let t := p/w
  let ε : ℝ := rem/((m:ℝ)*q)
  have mp : 0<m := Nat.mul_pos (by decide) wp
  have mz : (m:ℝ)=2*w := by dsimp [m]; push_cast; rfl
  have eqK : (m:ℝ)*k+rem=(r+(w:ℝ)*t)*q := by
    exact_mod_cast (show m*k+rem=(r+w*t)*q by rw [Nat.div_add_mod,Nat.mod_add_div])
  have pn : (0:ℝ)<p := by exact_mod_cast pp.pos
  have qn : (0:ℝ)<q := by exact_mod_cast qp.pos
  have wn : (0:ℝ)<w := by exact_mod_cast wp
  have mn : (0:ℝ)<m := by exact_mod_cast mp
  have eq : (k:ℝ)*p/(p*q)-r/m=t/2-ε := by
    rw [show (k:ℝ)*p/(p*q)=k/q by field_simp; ring]
    dsimp only [ε]
    rw [mz] at eqK ⊢
    field_simp
    linear_combination 4*(w:ℝ)*q*eqK
  have e0 : 0≤ε := by dsimp [ε]; positivity
  have ec : ε≤1/6 := by
    dsimp only [ε]
    apply (div_le_iff₀ (mul_pos mn qn)).mpr
    have small : (rem:ℝ)≤m := by exact_mod_cast (Nat.mod_lt (p*q) mp).le
    have six : (6:ℝ)≤q := by exact_mod_cast large
    nlinarith only [mul_le_mul_of_nonneg_left six mn.le, mul_le_mul_of_nonneg_left small (by norm_num : (0:ℝ)≤6)]
  have amp : 1/2≤Real.cos (-(2*π*ε)) := by
    rw [Real.cos_neg,←Real.cos_pi_div_three]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
    nlinarith only [mul_le_mul_of_nonneg_left ec Real.pi_pos.le]
  have obs := (rotated_error r m value (residual (p*q) k)).trans_lt err
  rw [real_reading pp qp pq balance,eq] at obs
  change 0<rotated r m value ↔ t%2=0
  by_cases even : t%2=0
  · have e : (t:ℝ)=2*(t/2:ℕ) := by exact_mod_cast (show t=2*(t/2) by omega)
    have re : 2*π*((t:ℝ)/2-ε)=-(2*π*ε)+(t/2:ℕ)*(2*π) := by rw [e]; ring
    rw [re,Real.cos_add_nat_mul_two_pi] at obs
    exact ⟨fun _ => even,fun _ => by linarith only [(abs_lt.mp obs).1,amp]⟩
  · have e : (t:ℝ)=2*(t/2:ℕ)+1 := by exact_mod_cast (show t=2*(t/2)+1 by omega)
    have re : 2*π*((t:ℝ)/2-ε)=(-(2*π*ε)+π)+(t/2:ℕ)*(2*π) := by rw [e]; ring
    rw [re,Real.cos_add_nat_mul_two_pi,Real.cos_add_pi] at obs
    exact ⟨fun pos => by linarith only [(abs_lt.mp obs).2,amp,pos], fun h => (even h).elim⟩

/-- Frequencies for all queried digits are fixed in advance. The signed
rotation uses only the low digits decoded so far. -/
noncomputable def decode (n : ℕ) (read : ℕ→ℂ) : ℕ→ℕ
  | 0 => 0
  | j+1 =>
    let w := 2^j
    let r := decode n read j
    if 0<rotated r (2*w) (read (n/(2*w))) then r else r+w

theorem decode_mod {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (pq : p<q) (balance : q≤2*p)
    (large : 6≤q) (read : ℕ→ℂ) (J : ℕ)
    (accurate : ∀ j<J, let k := (p*q)/(2*2^j); ‖read k-residual (p*q) k‖<1/2) :
    decode (p*q) read J=p%(2^J) := by
  induction J with
  | zero => simp only [decode,pow_zero,Nat.mod_one]
  | succ j ih =>
    have prev := ih (fun i hi => accurate i (hi.trans (Nat.lt_succ_self j)))
    have bit := bit_reading pp qp pq balance large (show (0:ℕ)<2^j by positivity)
      (accurate j (Nat.lt_succ_self j))
    rw [decode,prev,pow_succ,Nat.mod_mul]
    split_ifs with sign
    · rw [bit.mp sign]; simp
    · have odd : (p/2^j)%2=1 := by
        have := mt bit.mpr sign
        omega
      rw [odd]; simp

/-- At one reading per bit, the recovered integer is the smaller factor. -/
theorem recover {p q J : ℕ} (pp : p.Prime) (qp : q.Prime) (pq : p<q) (balance : q≤2*p)
    (large : 6≤q) (bits : p<2^J) (read : ℕ→ℂ)
    (accurate : ∀ j<J, let k := (p*q)/(2*2^j); ‖read k-residual (p*q) k‖<1/2) :
    decode (p*q) read J=p := by rw [decode_mod pp qp pq balance large read J accurate,Nat.mod_eq_of_lt bits]

private theorem phase_pow (n k x : ℕ) : phase n k x = (phase n k 1)^x := by
  unfold phase
  rw [←Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The public contribution can be computed by a single geometric sum.
At ratio one, its value is just the length. -/
theorem geometric (n k L : ℕ) :
    (∑ x∈Icc 1 L, phase n k x)*(phase n k 1-1) =
      phase n k 1*((phase n k 1)^L-1) := by
  induction L with
  | zero => simp
  | succ L ih =>
    have window : Icc 1 (L+1) = insert (L+1) (Icc 1 L) := by
      ext v
      simp only [mem_Icc,mem_insert]
      omega
    have fresh : L+1∉Icc 1 L := fun h => (Nat.not_succ_le_self _) (mem_Icc.mp h).2
    rw [window,sum_insert fresh,add_mul,ih,phase_pow n k (L+1)]
    ring

/-- Under m independent uniform draws, these many ordered transcripts all
miss the one informative position. All other summands in the residual vanish. -/
theorem missed_transcripts {L : ℕ} (h : Fin L) (m : ℕ) :
    ((Finset.univ : Finset (Fin m→Fin L)).filter (fun f => ∀ j, f j≠h)).card=(L-1)^m := by
  classical
  let good := (Finset.univ : Finset (Fin m→Fin L)).filter (fun f => ∀ j, f j≠h)
  let others := (Finset.univ : Finset (Fin L)).erase h
  let E : (↥good) ≃ (Fin m→↥others) :=
    { toFun := fun f j => ⟨f.val j, mem_erase.mpr ⟨(mem_filter.mp f.property).2 j,mem_univ _⟩⟩
      invFun := fun f => ⟨fun j => (f j).val,mem_filter.mpr ⟨mem_univ _,fun j => (mem_erase.mp (f j).property).1⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have cnt : others.card=L-1 := by simp [others]
  change good.card=_
  rw [←Fintype.card_coe,Fintype.card_congr E,Fintype.card_fun,Fintype.card_coe,Fintype.card_fin,cnt]

/-- Union bound for the exact counts, with denominators cleared. -/
theorem hit_bound {L : ℕ} (lp : 0<L) (m : ℕ) :
    L*(L^m-(L-1)^m) ≤ m*L^m := by
  have one : L-1+1=L := by omega
  have tiny (k : ℕ) : (L-1)^k≤L^k := Nat.pow_le_pow_left (by omega) k
  induction m with
  | zero => simp
  | succ m ih =>
    have ld := Nat.sub_add_cancel (tiny m)
    have nx := Nat.sub_add_cancel (tiny (m+1))
    have rec : L^(m+1)-(L-1)^(m+1)=L*(L^m-(L-1)^m)+(L-1)^m := by
      rw [pow_succ,pow_succ] at nx ⊢
      nlinarith only [nx,congrArg (fun z : ℕ => z*L) ld,
        congrArg (fun z : ℕ => (L-1)^m*z) one]
    rw [rec,pow_succ,Nat.succ_mul]
    nlinarith only [Nat.mul_le_mul_left L ih,Nat.mul_le_mul_left L (tiny m)]

/-- Squared errors over all L one-sample outcomes sum to L(L-1).
Dividing by L gives mean squared error L-1 for the unbiased estimate
which scales a sampled summand by L. -/
theorem sample_mse_total {L : ℕ} (h : Fin L) {z : ℂ} (hz : ‖z‖=1) :
    (∑ x : Fin L, ‖(if x=h then (L:ℂ)*z else 0)-z‖^2) = (L:ℝ)*(L-1) := by
  classical
  have lp : 1≤L := (Nat.zero_le h.val).trans_lt h.isLt
  have one : (1:ℝ)≤L := by exact_mod_cast lp
  have atHole : ‖(L:ℂ)*z-z‖ = (L:ℝ)-1 := by
    rw [←sub_one_mul,norm_mul,hz,mul_one]
    change ‖((L:ℝ):ℂ) - (1:ℝ)‖ = _
    rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
  rw [←Finset.sum_erase_add _ _ (mem_univ h)]
  have others : (∑ x∈(univ : Finset (Fin L)).erase h,
      ‖(if x=h then (L:ℂ)*z else 0)-z‖^2) = (L:ℝ)-1 := by
    calc
      _ = ∑ _x∈(univ : Finset (Fin L)).erase h, (1:ℝ) := by
        apply sum_congr rfl; intro x hx
        simp [(mem_erase.mp hx).1,hz]
      _ = _ := by simp [Nat.cast_sub lp]
  rw [others,if_pos rfl,atHole]; ring

set_option exponentiation.threshold 4096 in
/-- Even 2^40 independent uniform summand probes have chance at most
2^-983 of touching the exceptional summand on the target population.
The inequality compares exact integer transcript counts. -/
theorem uniform_full {p q m : ℕ} (pp : p.Prime) (pq : p<q) (balanced : q≤2*p)
    (width : 2^1023≤p) (budget : m≤2^40) :
    let L := (p*q).sqrt
    2^983*(L^m-(L-1)^m) ≤ L^m := by
  let L := (p*q).sqrt
  have lo : 2^1023≤L := width.trans (square_root_window pp pq balanced).1
  have enough : 2^983*m≤L := (Nat.mul_le_mul_left (2^983) budget).trans
    ((show (2:ℕ)^983*2^40=2^1023 by decide +kernel) ▸ lo)
  have lp : 0<L := (by decide +kernel : 0<(2:ℕ)^1023).trans_le lo
  have h := Nat.mul_le_mul_left (2^983) (hit_bound lp m)
  calc
    _ ≤ (2^983*(L*(L^m-(L-1)^m)))/L := by
      rw [←mul_assoc,mul_assoc (2^983) L _,mul_left_comm (2^983) L,Nat.mul_div_cancel_left _ lp]
    _ ≤ (2^983*(m*L^m))/L := Nat.div_le_div_right h
    _ ≤ L^m := by
      rw [←mul_assoc]
      calc
        _ ≤ (L*L^m)/L := Nat.div_le_div_right (Nat.mul_le_mul_right _ enough)
        _ = _ := Nat.mul_div_cancel_left _ lp

/-- At every public query used for two odd primes of the same bit width the
complete principal transform equals one. The information in the decoder
enters specifically through the truncation. -/
theorem complete_at_queries {p q K j : ℕ} (pp : p.Prime) (qp : q.Prime) (pq : p<q)
    (odd : 2<p) (low : 2^K≤p) (high : q<2^(K+1)) (index : j≤K) [NeZero (p*q)] :
    ZMod.dft (fun x => (1 : DirichletCharacter ℂ (p*q)) x)
      (((p*q)/(2*2^j):ℕ):ZMod (p*q)) = 1 := by
  let m := 2*2^j
  let n := p*q
  have positive : 0<m := by dsimp [m]; positivity
  have oddN : Odd n := (pp.odd_of_ne_two odd.ne').mul (qp.odd_of_ne_two (odd.trans pq).ne')
  have remainder : 0<n%m := by
    by_contra! hz
    exact oddN.not_two_dvd_nat (dvd_trans (show 2∣m from ⟨2^j,rfl⟩)
      (Nat.dvd_of_mod_eq_zero (Nat.eq_zero_of_le_zero hz)))
  have nondiv (x : ℕ) (dx : x∣n) (mx : m≤x) : ¬x∣n/m := by
    intro d
    have dr : x∣n%m := Nat.mod_eq_sub_mul_div ▸ Nat.dvd_sub dx (dvd_mul_of_dvd_right d m)
    exact (Nat.not_lt_of_ge mx) ((Nat.le_of_dvd remainder dr).trans_lt (Nat.mod_lt _ positive))
  have both : ¬p∣n/m ∧ ¬q∣n/m := by
    by_cases below : j<K
    · have small : m≤p := by
        change 2*2^j≤p
        rw [mul_comm,←pow_succ]
        exact (Nat.pow_le_pow_right (by decide) below).trans low
      exact ⟨nondiv p (dvd_mul_right p q) small,nondiv q (dvd_mul_left q p) (small.trans pq.le)⟩
    · have same : K=j := by omega
      have above : q<m := by simpa only [same,pow_succ,m,Nat.mul_comm] using high
      have fits : m≤n := by
        dsimp [m,n]
        rw [same] at low
        exact (Nat.mul_le_mul_left 2 low).trans (by simpa only [Nat.mul_comm 2 p] using Nat.mul_le_mul_left p qp.two_le)
      have kp := Nat.div_pos fits positive
      have kpLow : n/m<p := (Nat.div_lt_iff_lt_mul positive).mpr (Nat.mul_lt_mul_of_pos_left above pp.pos)
      exact ⟨fun h => (Nat.not_le_of_gt kpLow) (Nat.le_of_dvd kp h),
        fun h => (Nat.not_le_of_gt (kpLow.trans pq)) (Nat.le_of_dvd kp h)⟩
  rw [principal_dft_at_nat pp qp pq.ne,if_neg both.1,if_neg both.2]
  norm_num

end PrimeFactors.TruncatedRamanujan
