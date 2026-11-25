import PrimeFactors.LocalMidpointLanes
import PrimeFactors.PrimePowerCount
import PrimeFactors.SieveInterval
import PrimeFactors.Isolation
import PrimeFactors.Fermat
import Mathlib.Data.ZMod.QuotientRing

set_option maxRecDepth 8192
set_option exponentiation.threshold 4096

namespace PrimeFactors.PersistentLocalSurvivors

/-- A root of the unit modulo eight gives a root at any dyadic precision. -/
theorem dyadic_unit_square (t : ℤ) (e : ℕ) :
    IsSquare ((1+8*t : ℤ) : ZMod (2^e)) := by
  have eight : (8:ℤ) ∣ (1+8*t)-1 := ⟨t, by ring⟩
  obtain ⟨x,hx⟩ := LocalMidpointLanes.square_unit (D:=1+8*t) e
    ((pow_dvd_pow (2:ℤ) (min_le_right e 3)).trans eight)
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (1+8*t-x^2) (2^e)).mpr (by simpa using hx)
  push_cast at h
  exact ⟨x,by simpa [pow_two] using sub_eq_zero.mp h⟩

def dyadicGood (d : ℤ) : Bool :=
  d%8 == 1 || d%32 == 4 || d%128 == 16

def triadicGood (d : ℤ) : Bool :=
  d%3 == 1 || d%27 == 9

theorem dyadic_lifts {d : ℤ} (good : dyadicGood d) (e : ℕ) :
    IsSquare (d : ZMod (2^e)) := by
  simp [dyadicGood] at good
  rcases good with (h|h)|h
  · have eq : d=1+8*(d/8) := by omega
    rw [eq]; exact dyadic_unit_square _ _
  · have eq : d=2^2*(1+8*(d/32)) := by omega
    rw [eq]
    push_cast
    exact (show IsSquare (4 : ZMod (2^e)) from ⟨2,by norm_num⟩).mul (by simpa using dyadic_unit_square (d/32) e)
  · have eq : d=4^2*(1+8*(d/128)) := by omega
    rw [eq]
    push_cast
    exact (show IsSquare (16 : ZMod (2^e)) from ⟨4,by norm_num⟩).mul (by simpa using dyadic_unit_square (d/128) e)

private theorem triadic_unit_square (t : ℤ) (e : ℕ) :
    IsSquare ((1+3*t : ℤ) : ZMod (3^e)) := by
  cases e with
  | zero => rw [pow_zero]; exact ⟨0,Subsingleton.elim _ _⟩
  | succ k =>
    have one : ((1+3*t : ℤ) : ZMod 3) = 1 := by push_cast; ring_nf; rfl
    apply (isSquare_primePow_iff_of_unit (ℓ:=3) (by decide) (1+3*t) (by rw [one]; decide) k).mpr
    rw [one]
    exact ⟨1,by simp⟩

theorem triadic_lifts {d : ℤ} (good : triadicGood d) (e : ℕ) :
    IsSquare (d : ZMod (3^e)) := by
  simp [triadicGood] at good
  rcases good with h|h
  · have eq : d=1+3*(d/3) := by omega
    rw [eq]; exact triadic_unit_square _ _
  · have eq : d=3^2*(1+3*(d/27)) := by omega
    rw [eq]
    push_cast
    exact (show IsSquare (9 : ZMod (3^e)) from ⟨3,by norm_num⟩).mul (by simpa using triadic_unit_square (d/27) e)

set_option maxHeartbeats 4000000 in
/-- A finite check of all possible low digits of the product and midpoint. -/
theorem small_prime_counts :
    (∀ n : Fin 128, n.val%2=1 → 4 ≤ ((Finset.univ : Finset (ZMod 128)).filter
      (fun h => dyadicGood ((h.val:ℤ)^2-n.val))).card) ∧
    (∀ n : Fin 27, n.val%3≠0 → 2 ≤ ((Finset.univ : Finset (ZMod 27)).filter
      (fun h => triadicGood ((h.val:ℤ)^2-n.val))).card) := by decide +kernel

noncomputable def regularLanes (p : ℕ) [Fact p.Prime] (n : ZMod p) : Finset (ZMod p) :=
  ((factorSumResidues p n) \ ((squareRootsMod p n).image (fun h => 2*h))).image (fun s => s/2)

theorem regular_lane_count {p : ℕ} [Fact p.Prime] (odd : p ≠ 2) (n : ZMod p) (unit : n ≠ 0) :
    (p-3)/2 ≤ (regularLanes p n).card := by
  have two : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  rw [regularLanes, Finset.card_image_of_injective _ (fun _ _ h => (div_left_inj' two).mp h)]
  have bound := Finset.card_le_card_sdiff_add_card (s:=factorSumResidues p n)
    (t:=(squareRootsMod p n).image (fun h => 2*h))
  rw [Finset.card_image_of_injective _ (fun _ _ h => mul_left_cancel₀ two h)] at bound
  by_cases sq : IsSquare n
  · rw [card_factorSumResidues_of_square p odd n unit sq, card_squareRootsMod_of_square p odd n unit sq] at bound
    omega
  · rw [card_factorSumResidues_of_nonsquare p n unit sq, card_squareRootsMod_of_nonsquare p n sq] at bound
    omega

theorem regular_lane_lifts {p : ℕ} [Fact p.Prime] (odd : p ≠ 2) (n h : ℤ)
    (unit : (n : ZMod p) ≠ 0) (lane : (h : ZMod p) ∈ regularLanes p (n : ZMod p)) (e : ℕ) :
    IsSquare ((h^2-n : ℤ) : ZMod (p^e)) := by
  have two : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  obtain ⟨s,hs,eq⟩ := Finset.mem_image.mp lane
  have sum : s=2*(h : ZMod p) := by simpa [mul_comm] using (div_eq_iff two).mp eq
  obtain ⟨yes,no⟩ := Finset.mem_sdiff.mp hs
  obtain ⟨x,y,prod,trace⟩ := (mem_factorSumResidues_iff p unit).mp yes
  have regular : ((h^2-n : ℤ) : ZMod p) ≠ 0 := by
    push_cast
    intro zero
    have hsq := sub_eq_zero.mp zero
    have hn : (h : ZMod p) ≠ 0 := by intro z; simp [z,unit.symm] at hsq
    exact no (Finset.mem_image.mpr ⟨(h : ZMod p), Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨hn,Finset.mem_univ _⟩,hsq⟩,sum.symm⟩)
  cases e with
  | zero => rw [pow_zero]; exact ⟨0,Subsingleton.elim _ _⟩
  | succ k =>
    apply (isSquare_primePow_iff_of_unit odd _ regular k).mpr
    refine ⟨(x-y)/2,?_⟩
    push_cast
    have H : (h : ZMod p) = (x+y)/2 := by apply (eq_div_iff two).mpr; rw [mul_comm,←sum,trace]
    rw [H,←prod]; field_simp; ring

/-- The balanced midpoint interval includes this many consecutive integers,
even at the bottom of the 2,048-bit input range. -/
theorem balanced_subinterval {N w : ℕ} (large : (18*w)^2 ≤ N) {i : ℕ} (offset : i<w) :
    let h := N.sqrt+1+i
    N ≤ h^2 ∧ 8*h^2 ≤ 9*N := by
  dsimp only
  have wide : 18*w ≤ N.sqrt := Nat.le_sqrt.mpr (by simpa [pow_two] using large)
  have h1 := Nat.mul_le_mul_right N.sqrt wide
  have h2 := Nat.mul_le_mul_right w wide
  have hi : N.sqrt+1+i ≤ N.sqrt+w := by change i<w at offset; omega
  have above := Nat.lt_succ_sqrt N
  have below := Nat.sqrt_le N
  constructor
  · nlinarith [Nat.pow_le_pow_left (show N.sqrt+1 ≤ N.sqrt+1+i by omega) 2]
  · have hsq := Nat.pow_le_pow_left hi 2
    nlinarith

noncomputable def smallPrimes (cutoff : ℕ) : Finset ℕ := (Finset.range (cutoff+1)).filter Nat.Prime

def laneMod (p : ℕ) : ℕ := if p=2 then 128 else if p=3 then 27 else p

def minLanes (p : ℕ) : ℕ := if p=2 then 4 else if p=3 then 2 else (p-3)/2

noncomputable def period (cutoff : ℕ) : ℕ := ∏ p ∈ smallPrimes cutoff, laneMod p

noncomputable def minPerPeriod (cutoff : ℕ) : ℕ := ∏ p ∈ smallPrimes cutoff, minLanes p

/-- Removing one genuine midpoint still leaves both strict lower bounds. -/
theorem numerical_bounds :
    (18*2^1019 : ℕ)^2 ≤ 2^2047 ∧
    2^880+1 < (2^1019 / period 700)*minPerPeriod 700 ∧
    2^874+1 < (2^1019 / period 733)*minPerPeriod 733 := by decide +kernel


theorem full_period_product {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (pos : ∀ i, 0<m i) (cop : Pairwise (fun i j => (m i).Coprime (m j)))
    (A : (i : ι) → Finset (ZMod (m i))) (start W : ℕ) :
    W/(∏ i, m i) * (∏ i, (A i).card) ≤
    Nat.card {k : Fin W // ∀ i, ((start+k.val : ℕ) : ZMod (m i)) ∈ A i} := by
  classical
  let e := ZMod.prodEquivPi m cop
  let P := fun r : ZMod (∏ i, m i) => ∀ i, e r i ∈ A i
  have posM := Finset.prod_pos (fun i (_ : i ∈ (Finset.univ : Finset ι)) => pos i)
  have bound := periodic_interval_lower_bound posM P start W
  let f : {r // P r} ≃ ((i : ι) → A i) := {
    toFun := fun r i => ⟨e r.val i,r.property i⟩
    invFun := fun a => ⟨e.symm (fun i => (a i).val),fun i => by simp [(a i).property]⟩
    left_inv := fun r => Subtype.ext (e.symm_apply_apply _)
    right_inv := fun a => funext (fun i => Subtype.ext (congrFun (e.apply_symm_apply _) i))
  }
  rw [Nat.card_congr f, Nat.card_pi] at bound
  have count (i : ι) : Nat.card (A i) = (A i).card := by simp [Nat.card_eq_fintype_card]
  simp only [count] at bound
  simpa only [P, map_natCast, Pi.natCast_apply] using bound

private theorem reduced_delta (m h N : ℕ) :
    (↑(h%m)^2 - ↑(N%m) : ℤ) ≡ (h:ℤ)^2-N [ZMOD (m:ℤ)] :=
  ((Int.natCast_modEq_iff.mpr (Nat.mod_modEq h m)).pow 2).sub
    (Int.natCast_modEq_iff.mpr (Nat.mod_modEq N m))

private theorem local_lanes {p : ℕ} (prime : p.Prime) (N : ℕ) (unit : ¬ p ∣ N) :
    ∃ A : Finset (ZMod (laneMod p)), minLanes p ≤ A.card ∧
      ∀ h : ℕ, (h : ZMod (laneMod p)) ∈ A → ∀ e : ℕ,
      IsSquare (((h:ℤ)^2-N : ℤ) : ZMod (p^e)) := by
  letI : Fact p.Prime := ⟨prime⟩
  by_cases two : p=2
  · subst p
    let A := (Finset.univ : Finset (ZMod 128)).filter (fun h => dyadicGood ((h.val:ℤ)^2-(N%128:ℕ)))
    refine ⟨A, small_prime_counts.1 ⟨N%128,Nat.mod_lt _ (by decide)⟩ (by
      have := Nat.dvd_iff_mod_eq_zero.mpr.mt unit; dsimp; omega),?_⟩
    intro h hh e
    have good := (Finset.mem_filter.mp (show (h : ZMod 128) ∈ A from hh)).2
    rw [ZMod.val_natCast] at good
    have d := reduced_delta 128 h N
    have d8 := d.of_dvd (by decide : (8:ℤ) ∣ (128:ℕ))
    have d32 := d.of_dvd (by decide : (32:ℤ) ∣ (128:ℕ))
    apply dyadic_lifts
    unfold Int.ModEq at d8 d32 d
    norm_num only [Nat.cast_ofNat] at d
    simpa only [dyadicGood, d8, d32, d] using good
  by_cases three : p=3
  · subst p
    let A := (Finset.univ : Finset (ZMod 27)).filter (fun h => triadicGood ((h.val:ℤ)^2-(N%27:ℕ)))
    refine ⟨A, small_prime_counts.2 ⟨N%27,Nat.mod_lt _ (by decide)⟩ (by
      have := Nat.dvd_iff_mod_eq_zero.mpr.mt unit; dsimp; omega),?_⟩
    intro h hh e
    have good := (Finset.mem_filter.mp (show (h : ZMod 27) ∈ A from hh)).2
    rw [ZMod.val_natCast] at good
    have d := reduced_delta 27 h N
    have d3 := d.of_dvd (by decide : (3:ℤ) ∣ (27:ℕ))
    apply triadic_lifts
    unfold Int.ModEq at d3 d
    norm_num only [Nat.cast_ofNat] at d
    simpa only [triadicGood, d3, d] using good
  rw [show laneMod p = p by simp [laneMod,two,three],show minLanes p = (p-3)/2 by simp [minLanes,two,three]]
  have hn : (N : ZMod p) ≠ 0 := (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp.mt unit
  exact ⟨regularLanes p N,regular_lane_count two _ hn,fun h hh e =>
    regular_lane_lifts two N h (by exact_mod_cast hn) (by exact_mod_cast hh) e⟩

private theorem laneMod_pow (p : ℕ) : ∃ e : ℕ, laneMod p = p^e := by
  by_cases h : p=2
  · subst p; exact ⟨7,rfl⟩
  by_cases k : p=3
  · subst p; exact ⟨3,rfl⟩
  exact ⟨1,by simp [laneMod,h,k]⟩

/-- Counts candidates which pass at all positive powers of every listed prime.
The bound remains valid for a dynamically chosen number of digits at each prime. -/
theorem persistent_interval (C start W N : ℕ) (unit : ∀ p ∈ smallPrimes C, ¬ p ∣ N) :
    W/period C*minPerPeriod C ≤ Nat.card {k : Fin W // ∀ p ∈ smallPrimes C, ∀ e : ℕ,
      IsSquare ((((start+k.val : ℕ):ℤ)^2-N : ℤ) : ZMod (p^e))} := by
  classical
  let I := {p // p ∈ smallPrimes C}
  have hp (i : I) : i.val.Prime := (Finset.mem_filter.mp i.property).2
  choose A count good using (fun i : I => local_lanes (hp i) N (unit i.val i.property))
  have cp : Pairwise (fun i j : I => (laneMod i.val).Coprime (laneMod j.val)) := by
    intro i j ne
    obtain ⟨a,ha⟩ := laneMod_pow i.val
    obtain ⟨b,hb⟩ := laneMod_pow j.val
    rw [ha,hb]
    exact (((Nat.coprime_primes (hp i) (hp j)).mpr (fun eq => ne (Subtype.ext eq))).pow_left a).pow_right b
  have pos (i : I) : 0<laneMod i.val := by obtain ⟨e,rw⟩ := laneMod_pow i.val; simp [rw,(hp i).pos]
  have countAll := full_period_product (fun i : I => laneMod i.val) pos cp A start W
  have per : (∏ i : I, laneMod i.val) = period C := (Finset.prod_subtype _ (by simp) _).symm
  have lanes : (∏ i : I, minLanes i.val) = minPerPeriod C := (Finset.prod_subtype _ (by simp) _).symm
  rw [per] at countAll
  rw [← lanes]
  refine (Nat.mul_le_mul_left _ (Finset.prod_le_prod' (fun i _ => count i))).trans (countAll.trans ?_)
  apply Nat.card_le_card_of_injective (fun k => ⟨k.val,fun p mem e => good ⟨p,mem⟩ _ (k.property ⟨p,mem⟩) e⟩)
  intro x y eq
  exact Subtype.ext (Subtype.mk.inj eq)

private theorem discard_midpoint {W : ℕ} (P : Fin W → Prop) (start s : ℕ) :
    Nat.card {k // P k} ≤ Nat.card {k // P k ∧ 2*(start+k.val)≠s}+1 := by
  classical
  let A := {k // P k}
  let F := {k // P k ∧ 2*(start+k.val)≠s}
  let f (k : A) : Option F := if h : 2*(start+k.val.val)≠s then some ⟨k.val,k.property,h⟩ else none
  have inj : Function.Injective f := by
    intro x y eq
    by_cases hx : 2*(start+x.val.val)≠s <;> by_cases hy : 2*(start+y.val.val)≠s
    · simp [f,hx,hy] at eq
      exact Subtype.ext (Subtype.mk.inj eq)
    · simp [f,hx,hy] at eq
    · simp [f,hx,hy] at eq
    · exact Subtype.ext (Fin.ext (by omega))
  have h := Nat.card_le_card_of_injective _ inj
  simpa only [Nat.card_eq_fintype_card,Fintype.card_option] using h

/-- The count uses offsets in an explicitly contained subinterval of the full
balanced midpoint range. The true factor midpoint is removed by its sum. -/
def WrongOffsets (C start W p q : ℕ) := {k : Fin W //
  (∀ s ∈ smallPrimes C, ∀ e : ℕ, IsSquare
    ((((start+k.val : ℕ):ℤ)^2-(p*q:ℕ) : ℤ) : ZMod (s^e))) ∧
  2*(start+k.val)≠p+q}

theorem false_midpoints_2048 {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (sp : 733<p) (sq : 733<q) (large : 2^2047≤p*q) :
    let a := (p*q).sqrt+1
    (∀ i : Fin (2^1019), p*q ≤ (a+i.val)^2 ∧ 8*(a+i.val)^2 ≤ 9*(p*q)) ∧
    2^880 < Nat.card (WrongOffsets 700 a (2^1019) p q) ∧
    2^874 < Nat.card (WrongOffsets 733 a (2^1019) p q) := by
  dsimp only
  refine ⟨fun i => balanced_subinterval (numerical_bounds.1.trans large) i.isLt,?_⟩
  let a := (p*q).sqrt+1
  have count (C : ℕ) (small : C≤733) :
      (2^1019 / period C)*minPerPeriod C ≤ Nat.card (WrongOffsets C a (2^1019) p q)+1 := by
    have un (s : ℕ) (mem : s ∈ smallPrimes C) : ¬ s ∣ p*q := by
      obtain ⟨lim,prime⟩ := Finset.mem_filter.mp mem
      have left := Finset.mem_range.mp lim
      intro d
      rcases prime.dvd_mul.mp d with l|r
      · have := (Nat.prime_dvd_prime_iff_eq prime hp).mp l; omega
      · have := (Nat.prime_dvd_prime_iff_eq prime hq).mp r; omega
    exact (persistent_interval C a (2^1019) (p*q) un).trans
      (discard_midpoint _ a (p+q))
  exact ⟨Nat.lt_of_succ_lt_succ (numerical_bounds.2.1.trans_le (count 700 (by decide))),
         Nat.lt_of_succ_lt_succ (numerical_bounds.2.2.trans_le (count 733 (by decide)))⟩

end PrimeFactors.PersistentLocalSurvivors
