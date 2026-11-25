import PrimeFactors.FourierAccess

namespace PrimeFactors.DivisorWindowSignal
open Finset

/-- Each integer in the H-term window ending at x is a unit modulo n. -/
def EmptyWindow (n H : ℕ) (x : ZMod n) : Prop :=
  ∀ h∈range H, IsUnit (x-(h:ZMod n))

private noncomputable def offsets (n H : ℕ) : Finset (ZMod n) :=
  (range H).image fun h : ℕ => (h:ZMod n)

private theorem offsets_card {n H : ℕ} [NeZero n] (bound : H≤n) :
    (offsets n H).card=H := by
  unfold offsets
  rw [Finset.card_image_of_injOn,Finset.card_range]
  intro a ha b hb eq
  have lowA := (Finset.mem_range.mp ha).trans_le bound
  have lowB := (Finset.mem_range.mp hb).trans_le bound
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt lowA, Nat.mod_eq_of_lt lowB] using congrArg ZMod.val eq

/-- An exact count of empty windows over all cyclic translations. It uses
public unit tests on the left and exposes the factor sum on the right. -/
theorem empty_count {p q H : ℕ} (pp : p.Prime) (qp : q.Prime) (different : p≠q)
    (hp : H≤p) (hq : H≤q) :
    Nat.card {x : ZMod (p*q) // EmptyWindow (p*q) H x} = (p-H)*(q-H) := by
  classical
  letI : Fact p.Prime := ⟨pp⟩
  letI : Fact q.Prime := ⟨qp⟩
  let e := ZMod.chineseRemainder ((Nat.coprime_primes pp qp).mpr different)
  have unit (x : ZMod (p*q)) (h : ℕ) :
      IsUnit (x-(h:ZMod (p*q))) ↔ (e x).1≠(h:ZMod p) ∧ (e x).2≠(h:ZMod q) := by
    rw [←isUnit_map_iff e, Prod.isUnit_iff, isUnit_iff_ne_zero, isUnit_iff_ne_zero]
    simp [sub_eq_zero]
  have good (x : ZMod (p*q)) : EmptyWindow (p*q) H x ↔
      (e x).1 ∉ offsets p H ∧ (e x).2 ∉ offsets q H := by
    simp only [EmptyWindow, offsets, Finset.mem_image]
    constructor
    · intro ok
      constructor
      · rintro ⟨h,hh,eq⟩
        exact ((unit x h).mp (ok h hh)).1 eq.symm
      · rintro ⟨h,hh,eq⟩
        exact ((unit x h).mp (ok h hh)).2 eq.symm
    · rintro ⟨a,b⟩ h hh
      exact (unit x h).mpr ⟨fun eq => a ⟨h,hh,eq.symm⟩,fun eq => b ⟨h,hh,eq.symm⟩⟩
  let E : {x // EmptyWindow (p*q) H x} ≃
      ({a : ZMod p // a∉offsets p H} × {b : ZMod q // b∉offsets q H}) :=
    { toFun := fun x => (⟨(e x.val).1,((good _).mp x.property).1⟩,
                          ⟨(e x.val).2,((good _).mp x.property).2⟩)
      invFun := fun v => ⟨e.symm (v.1.val,v.2.val),(good _).mpr (by simp [v.1.property,v.2.property])⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro x; ext <;> simp }
  rw [Nat.card_congr E,Nat.card_eq_fintype_card,Fintype.card_prod]
  simp only [Fintype.card_subtype_compl, Fintype.card_coe, ZMod.card,offsets_card hp,offsets_card hq]

/-- Any pair of odd factors consistent with an empty-window count at absolute
error less than H has the same sum; the product then determines both factors. -/
theorem unique_sum {n H s t observed : ℤ} (oe : Even s) (oe' : Even t)
    (positive : 0<H) (one : |observed-(n-H*s+H^2)|<H)
    (two : |observed-(n-H*t+H^2)|<H) : s=t := by
  obtain ⟨a,ha⟩ := oe
  obtain ⟨b,hb⟩ := oe'
  obtain ⟨a₁,a₂⟩ := abs_lt.mp one
  obtain ⟨b₁,b₂⟩ := abs_lt.mp two
  by_contra notEqual
  rcases lt_or_gt_of_ne notEqual with lt|gt
  · have gap : s+2≤t := by omega
    nlinarith only [a₁,b₂,mul_le_mul_of_nonneg_left gap positive.le]
  · have gap : t+2≤s := by omega
    nlinarith only [b₁,a₂,mul_le_mul_of_nonneg_left gap positive.le]

/-- Count a double hit at zero twice to remove its public Fourier impulse. -/
noncomputable def mask (N : ℕ) [NeZero N] (x : ZMod N) : ℂ :=
  1-(1 : DirichletCharacter ℂ N) x + if x=0 then 1 else 0

noncomputable def window (N H : ℕ) [NeZero N] (x : ZMod N) : ℂ :=
  ∑ h∈range H, mask N (x-(h:ZMod N))

private theorem const_dft {N : ℕ} [NeZero N] {k : ZMod N} (non : k≠0) :
    ZMod.dft (fun _ : ZMod N => (1 : ℂ)) k=0 := by
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul,mul_one]
  simpa only [AddChar.mulShift_apply,neg_mul,mul_comm k] using
    AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N (neg_ne_zero.mpr non))

theorem mask_dft {p q : ℕ} [NeZero (p*q)] (pp : p.Prime) (qp : q.Prime) (different : p≠q)
    (k : ℕ) (pos : 0<k) (low : k<p*q) :
    ZMod.dft (mask (p*q)) (k : ZMod (p*q)) =
       (if p∣k then (p:ℂ) else 0)+(if q∣k then (q:ℂ) else 0) := by
  classical
  have nz : (k:ZMod (p*q))≠0 := by
    intro h
    exact (Nat.not_dvd_of_pos_of_lt pos low) ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp h)
  have both (pdiv : p∣k) (qdiv : q∣k) : False :=
    (Nat.not_dvd_of_pos_of_lt pos low) (((Nat.coprime_primes pp qp).mpr different).mul_dvd_of_dvd_of_dvd pdiv qdiv)
  rw [ZMod.dft_apply]
  simp only [mask,smul_eq_mul,mul_add,mul_sub,mul_one, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have vanish := const_dft nz
  rw [ZMod.dft_apply] at vanish
  simp only [smul_eq_mul,mul_one] at vanish
  have ram := principal_dft_at_nat pp qp different k
  rw [ZMod.dft_apply] at ram
  simp only [smul_eq_mul] at ram
  rw [vanish,ram]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true,
    zero_mul,neg_zero,AddChar.map_zero_eq_one]
  split_ifs with a b b <;> first | exact (both a b).elim | ring

private theorem translate {N : ℕ} [NeZero N] (f : ZMod N → ℂ) (h k : ZMod N) :
    ZMod.dft (fun x => f (x-h)) k =
      ZMod.stdAddChar (-(h*k))*ZMod.dft f k := by
  rw [ZMod.dft_apply,ZMod.dft_apply,Finset.mul_sum]
  simp only [smul_eq_mul]
  apply Fintype.sum_equiv (Equiv.subRight h)
  intro x
  simp only [Equiv.subRight_apply]
  rw [←mul_assoc,←AddChar.map_add_eq_mul]
  congr 2
  ring

/-- Each interval harmonic is a geometric progression times a full-modulus
harmonic. Every nonzero term in the nonconstant spectrum is a factor witness. -/
theorem window_dft {p q : ℕ} [NeZero (p*q)] (pp : p.Prime) (qp : q.Prime) (different : p≠q)
    (H k : ℕ) (pos : 0<k) (low : k<p*q) :
    ZMod.dft (window (p*q) H) (k:ZMod (p*q)) =
    (∑ h∈range H,ZMod.stdAddChar (-((h:ZMod (p*q))*(k:ZMod (p*q))))) *
      ((if p∣k then (p:ℂ) else 0)+(if q∣k then (q:ℂ) else 0)) := by
  classical
  calc
    _ = ∑ h∈range H,ZMod.dft (fun x => mask (p*q) (x-(h:ZMod (p*q)))) (k:ZMod (p*q)) := by
        simp only [ZMod.dft_apply,window,smul_eq_mul,Finset.mul_sum]
        rw [Finset.sum_comm]
    _ = _ := by simp only [translate,mask_dft pp qp different k pos low,Finset.sum_mul]

theorem nonzero_mode_gives_factor {p q : ℕ} [NeZero (p*q)] (pp : p.Prime)
    (qp : q.Prime) (different : p≠q) (H k : ℕ) (pos : 0<k) (low : k<p*q)
    (signal : ZMod.dft (window (p*q) H) (k:ZMod (p*q))≠0) :
    1<Nat.gcd k (p*q) ∧ Nat.gcd k (p*q)<p*q := by
  have divides : p∣k ∨ q∣k := by
    by_contra! absent
    exact signal (by simp [window_dft pp qp different H k pos low,absent.1,absent.2])
  refine ⟨?_,(Nat.gcd_le_left _ pos).trans_lt low⟩
  rcases divides with pd|qd
  · exact pp.one_lt.trans_le <| Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ pos)
      (Nat.dvd_gcd pd (dvd_mul_right p q))
  · exact qp.one_lt.trans_le <| Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ pos)
      (Nat.dvd_gcd qd (dvd_mul_left q p))

private noncomputable def bit (n H : ℕ) (x : ZMod n) : ℂ :=
  ∑ h∈range H, if x=(h:ZMod n) then (1:ℂ) else 0

private theorem bit_sum (n H : ℕ) [NeZero n] : (∑ x : ZMod n,bit n H x)=(H:ℂ) := by
  unfold bit
  rw [Finset.sum_comm]
  simp

private theorem bit_square {n H : ℕ} [NeZero n] (hH : H≤n) (x : ZMod n) :
    bit n H x ^ 2 = bit n H x := by
  have value : bit n H x = if x.val<H then 1 else 0 := by
    unfold bit
    calc
      _ = ∑ h∈range H, if x.val=h then (1:ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro h hh
        have eq : x=(h:ZMod n) ↔ x.val=h := by
          have low := (mem_range.mp hh).trans_le hH
          constructor
          · intro e
            simpa [ZMod.val_natCast,Nat.mod_eq_of_lt low] using congrArg ZMod.val e
          · intro e
            rw [←e,ZMod.natCast_zmod_val]
        simp [eq]
      _ = _ := by simp
  rw [value]
  split <;> norm_num

private theorem window_crt {p q : ℕ} [NeZero (p*q)] (pp : p.Prime) (qp : q.Prime)
    (different : p≠q) (H : ℕ) (x : ZMod (p*q)) :
    let e:=ZMod.chineseRemainder ((Nat.coprime_primes pp qp).mpr different)
    window (p*q) H x = bit p H (e x).1 + bit q H (e x).2 := by
  letI : Fact p.Prime := ⟨pp⟩
  letI : Fact q.Prime := ⟨qp⟩
  intro e
  have mark (y : ZMod (p*q)) : mask (p*q) y =
      (if (e y).1=0 then 1 else 0)+(if (e y).2=0 then 1 else 0) := by
    have units : IsUnit y ↔ (e y).1≠0 ∧ (e y).2≠0 := by
      rw [←isUnit_map_iff e,Prod.isUnit_iff,isUnit_iff_ne_zero,isUnit_iff_ne_zero]
    have yz : y=0 ↔ (e y).1=0 ∧ (e y).2=0 := by
      constructor
      · rintro rfl; simp
      · rintro ⟨a,b⟩; apply e.injective; ext <;> simp [a,b]
    unfold mask
    by_cases a : (e y).1=0
    · have no : ¬IsUnit y := fun h => (units.mp h).1 a
      by_cases b : (e y).2=0 <;> simp [a,b,yz,MulChar.map_nonunit _ no]
    · by_cases b : (e y).2=0
      · have no : ¬IsUnit y := fun h => (units.mp h).2 b
        simp [a,b,yz,MulChar.map_nonunit _ no]
      · simp [a,b,yz,MulChar.one_apply (units.mpr ⟨a,b⟩)]
  simp only [window,bit,mark,map_sub,map_natCast,Prod.fst_sub,Prod.snd_sub,Prod.fst_natCast,
    Prod.snd_natCast,sub_eq_zero,Finset.sum_add_distrib]

/-- The actual first and second moments of the public translated-window sum.
The extra term in the second moment counts the H² starts covering both marks. -/
theorem moments {p q H : ℕ} [NeZero (p*q)] (pp : p.Prime) (qp : q.Prime) (neq : p≠q)
    (hp : H≤p) (hq : H≤q) :
    (∑ x : ZMod (p*q),window (p*q) H x) = (H:ℂ)*(p+q) ∧
    (∑ x : ZMod (p*q),window (p*q) H x^2) = (H:ℂ)*(p+q)+2*H^2 := by
  letI : Fact p.Prime := ⟨pp⟩
  letI : Fact q.Prime := ⟨qp⟩
  let e:=ZMod.chineseRemainder ((Nat.coprime_primes pp qp).mpr neq)
  have term (x : ZMod (p*q)) := window_crt pp qp neq H x
  constructor
  · rw [Fintype.sum_equiv e.toEquiv _ (fun y => bit p H y.1+bit q H y.2) term,Fintype.sum_prod_type]
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul,
      bit_sum,←Finset.mul_sum]
    ring
  · rw [Fintype.sum_equiv e.toEquiv _ (fun y => (bit p H y.1+bit q H y.2)^2)
        (fun x => congrArg (fun v : ℂ => v^2) (term x)),Fintype.sum_prod_type]
    simp only [add_sq,bit_square hp,bit_square hq,Finset.sum_add_distrib,Finset.sum_const,
      Finset.card_univ,ZMod.card,nsmul_eq_mul,bit_sum,←Finset.mul_sum,←Finset.sum_mul]
    ring

/-- Sum of the squared magnitudes in the positive band and its negative copy.
For the real signal these are conjugate frequencies. -/
noncomputable def bandEnergy (N H K : ℕ) [NeZero N] : ℝ :=
  2*∑ k∈Ioc 0 K, ‖ZMod.dft (window N H) (k : ZMod N)‖^2

/-- The variance across all translations, multiplied by (pq)², as obtained
from two independent Bernoulli variables of means H/p and H/q. -/
noncomputable def scaledVariance (p q H : ℕ) : ℝ :=
  H*(p:ℝ)^2*((q:ℝ)-H) + H*(q:ℝ)^2*((p:ℝ)-H)

theorem scaledVariance_moments {p q H : ℕ} [NeZero (p*q)] (pp : p.Prime) (qp : q.Prime)
    (different : p≠q) (hp : H≤p) (hq : H≤q) :
    (p:ℂ)*q*(∑ x : ZMod (p*q),window (p*q) H x^2) -
      (∑ x : ZMod (p*q),window (p*q) H x)^2=(scaledVariance p q H : ℂ) := by
  obtain ⟨one,two⟩ := moments pp qp different hp hq
  rw [one,two,scaledVariance]
  push_cast
  ring

theorem harmonic_bound {p q : ℕ} [NeZero (p*q)] (pp : p.Prime) (qp : q.Prime) (neq : p≠q)
    (H k : ℕ) (pos : 0<k) (low : k<p*q) :
    ‖ZMod.dft (window (p*q) H) (k:ZMod (p*q))‖^2 ≤
      (if p∣k then ((H:ℝ)*p)^2 else 0)+(if q∣k then ((H:ℝ)*q)^2 else 0) := by
  rw [window_dft pp qp neq H k pos low,norm_mul]
  have bound : ‖∑ h∈range H,ZMod.stdAddChar (-((h:ZMod (p*q))*(k:ZMod (p*q))))‖ ≤ (H:ℝ) :=
    (norm_sum_le ..).trans_eq (by simp [ZMod.stdAddChar_apply])
  have both (pd : p∣k) (qd : q∣k) : False := (Nat.not_dvd_of_pos_of_lt pos low)
    (((Nat.coprime_primes pp qp).mpr neq).mul_dvd_of_dvd_of_dvd pd qd)
  by_cases pd : p∣k <;> by_cases qd : q∣k
  · exact (both pd qd).elim
  · simp [pd,qd]
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right bound (by positivity)) 2
  · simp [pd,qd]
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right bound (by positivity)) 2
  · simp [pd,qd]

theorem band_price {p q : ℕ} [NeZero (p*q)] (pp : p.Prime) (qp : q.Prime)
    (neq : p≠q) (H K : ℕ) (low : K<p*q) :
    bandEnergy (p*q) H K ≤ 2*((K/p:ℕ)*((H:ℝ)*p)^2+(K/q:ℕ)*((H:ℝ)*q)^2) := by
  unfold bandEnergy
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ∑ k∈Ioc 0 K, ((if p∣k then ((H:ℝ)*p)^2 else 0)+(if q∣k then ((H:ℝ)*q)^2 else 0)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact harmonic_bound pp qp neq H k (mem_Ioc.mp hk).1 ((mem_Ioc.mp hk).2.trans_lt low)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [←Finset.sum_filter, Finset.sum_const,Nat.Ioc_filter_dvd_card_eq_div,nsmul_eq_mul]

/-- Normalized low-frequency energy relative to the variance scale. -/
theorem energy_fraction {p q : ℕ} [NeZero (p*q)] (pp : p.Prime) (qp : q.Prime)
    (neq : p≠q) (H K : ℕ) (low : K<p*q) (hw : 2*H≤p) (hw' : 2*H≤q) :
    ((p:ℝ)*q)*bandEnergy (p*q) H K ≤ 4*K*H*scaledVariance p q H := by
  have pd : ((K/p:ℕ):ℝ)*p ≤ K := by exact_mod_cast Nat.div_mul_le_self K p
  have qd : ((K/q:ℕ):ℝ)*q ≤ K := by exact_mod_cast Nat.div_mul_le_self K q
  have hp : 2*(H:ℝ)≤p := by exact_mod_cast hw
  have hq : 2*(H:ℝ)≤q := by exact_mod_cast hw'
  have gross : bandEnergy (p*q) H K ≤ 2*K*(H:ℝ)^2*(p+q) := by
    apply (band_price pp qp neq H K low).trans
    nlinarith only [mul_le_mul_of_nonneg_right pd (show 0≤(H:ℝ)^2*p by positivity),
      mul_le_mul_of_nonneg_right qd (show 0≤(H:ℝ)^2*q by positivity)]
  apply (mul_le_mul_of_nonneg_left gross (show 0≤(p:ℝ)*q by positivity)).trans
  dsimp only [scaledVariance]
  nlinarith only [mul_le_mul_of_nonneg_right hp (show 0≤(K:ℝ)*H^2*q^2 by positivity),
    mul_le_mul_of_nonneg_right hq (show 0≤(K:ℝ)*H^2*p^2 by positivity)]

theorem half_band_price {p q : ℕ} [NeZero (p*q)] (pp : p.Prime) (qp : q.Prime)
    (neq : p≠q) (H K : ℕ) (positive : 0<H) (low : K<p*q) (hp : 2*H≤p) (hq : 2*H≤q)
    (half : scaledVariance p q H ≤ 2*bandEnergy (p*q) H K) : p*q≤8*K*H := by
  have posH : (0:ℝ)<H := by exact_mod_cast positive
  have posP : (0:ℝ)<p := by exact_mod_cast pp.pos
  have posQ : (0:ℝ)<q := by exact_mod_cast qp.pos
  have left : (0:ℝ)<(p:ℝ)-H := sub_pos.mpr (by exact_mod_cast (show H<p by omega))
  have right : (0:ℝ)<(q:ℝ)-H := sub_pos.mpr (by exact_mod_cast (show H<q by omega))
  have posV : 0<scaledVariance p q H := by unfold scaledVariance; positivity
  have bound : ((p:ℝ)*q)*scaledVariance p q H ≤ (8*K*H)*scaledVariance p q H := by
    nlinarith only [mul_le_mul_of_nonneg_left half (show 0≤(p:ℝ)*q by positivity),
      energy_fraction pp qp neq H K low hp hq]
  exact_mod_cast (mul_le_mul_iff_of_pos_right posV).mp bound

/-- A sparse selection, at any heights, needs at least p/(4H) individual
nonconstant frequencies to represent half the centered translation variance. -/
theorem sparse_price {p q : ℕ} [NeZero (p*q)] (pp : p.Prime) (qp : q.Prime) (neq : p≠q)
    (H : ℕ) (positive : 0<H) (hp : 2*H≤p) (order : p≤q) (modes : Finset ℕ)
    (eligible : ∀ k∈modes, 0<k ∧ k<p*q)
    (half : scaledVariance p q H ≤ 2*∑ k∈modes, ‖ZMod.dft (window (p*q) H) (k:ZMod (p*q))‖^2) :
    p≤4*H*modes.card := by
  have prices (k : ℕ) (hk : k∈modes) : ‖ZMod.dft (window (p*q) H) (k:ZMod (p*q))‖^2 ≤ ((H:ℝ)*q)^2 := by
    have member := eligible k hk
    apply (harmonic_bound pp qp neq H k member.1 member.2).trans
    by_cases pd : p∣k <;> by_cases qd : q∣k
    · exact False.elim ((Nat.not_dvd_of_pos_of_lt member.1 member.2)
        (((Nat.coprime_primes pp qp).mpr neq).mul_dvd_of_dvd_of_dvd pd qd))
    · simp only [pd,qd,if_true,if_false,add_zero]
      exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (by exact_mod_cast order) (by positivity)) 2
    · simp [pd,qd]
    · simp only [pd,qd,if_false,add_zero]; positivity
  have upper := half.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum prices) (by norm_num))
  simp only [Finset.sum_const,nsmul_eq_mul] at upper
  have hP : 2*(H:ℝ)≤p := by exact_mod_cast hp
  have hQ : (H:ℝ)≤q := by exact_mod_cast (show H≤q by omega)
  have posH : (0:ℝ)<H := by exact_mod_cast positive
  have posQ : (0:ℝ)<q := by exact_mod_cast qp.pos
  dsimp only [scaledVariance] at upper
  have aux : (p:ℝ)*(H*q^2) ≤ (4*H*modes.card)*(H*q^2) := by
    nlinarith only [upper,mul_le_mul_of_nonneg_right hP (show 0≤(H:ℝ)*q^2 by positivity),
      mul_le_mul_of_nonneg_right hQ (show 0≤(H:ℝ)*p^2 by positivity)]
  have sol := (mul_le_mul_iff_of_pos_right (show (0:ℝ)<H*q^2 by positivity)).mp aux
  exact_mod_cast sol

set_option maxRecDepth 4000 in
theorem sample_empty :
    Nat.card {x : ZMod (137*251) // EmptyWindow (137*251) 13 x}=29512 := by
  rw [empty_count (by decide) (by decide) (by decide) (by decide) (by decide)]

set_option maxRecDepth 4000 in
theorem sample_energy : 25*bandEnergy (137*251) 13 185 < scaledVariance 137 251 13 := by
  have ub := band_price (p:=137) (q:=251) (by decide) (by decide) (by decide) 13 185 (by decide)
  norm_num [scaledVariance] at ub ⊢
  linarith only [ub]

theorem target_scales {p q K M : ℕ} (width : 2^2047≤p*q) (smaller : 2^1023≤p)
    (band : p*q≤8*K*2^512) (sparse : p≤4*2^512*M) : 2^1532≤K ∧ 2^509≤M := by
  constructor
  · apply Nat.le_of_mul_le_mul_left (c:=8*2^512) _ (by positivity)
    calc (8*2^512)*2^1532 = 2^2047 := by decide +kernel
         _ ≤ _ := width
         _ ≤ _ := band.trans_eq (by ring)
  · apply Nat.le_of_mul_le_mul_left (c:=4*2^512) _ (by positivity)
    calc (4*2^512)*2^509 = 2^1023 := by decide +kernel
         _ ≤ _ := smaller
         _ ≤ _ := sparse

end PrimeFactors.DivisorWindowSignal
