import PrimeFactors.GeometricMatchMoments
import PrimeFactors.GeometricMatchRank

/-! Decoding an exponent that occurs with equal multiplicity in the two
local geometric progressions. The input to the decoder consists of the
highest coefficients of a directional polynomial over the public modulus. -/

namespace PrimeFactors.GeometricMultiplicityReadout
open Finset Polynomial GeometricMatchMoments

set_option exponentiation.threshold 4096

/-- The order-r coefficient in the perturbation variable is a polynomial in
its public direction. Ring homomorphisms preserve this construction. -/
noncomputable def signal {R : Type*} [CommRing R] (W : ℕ) (y g : R) (r : ℕ) : R[X] :=
  (∏ i ∈ range (W+1), directionalFactor (C y) (C g) (X : R[X]) i).coeff r

theorem map_signal {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T) (W : ℕ)
    (y g : R) (r : ℕ) : (signal W y g r).map f = signal W (f y) (f g) r := by
  unfold signal
  change (mapRingHom f) _ = _
  rw [← Polynomial.coeff_map, Polynomial.map_prod]
  simp only [directionalFactor, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_C,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
    coe_mapRingHom, Polynomial.map_C, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]

/-- This length formula includes both endpoint residues and needs no divisibility
assumption on W. -/
private theorem range_bounds {W j d r : ℕ} (sj : j ≤ W) (dp : 0 < d)
    (count : r = j/d+(W-j)/d+1) :
    (∀ i < r, j%d+i*d ≤ W) ∧ W < (r+1)*d := by
  have a := Nat.mod_add_div j d
  have b := Nat.mod_add_div (W-j) d
  have c := Nat.mod_lt j dp
  have e := Nat.mod_lt (W-j) dp
  rw [mul_comm d] at a b
  constructor
  · intro i hi
    have bound := Nat.mul_le_mul_right d (show i ≤ j/d+(W-j)/d by omega)
    rw [Nat.add_mul] at bound
    omega
  · rw [count, Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.one_mul]
    omega

/-- Every local prime with exactly r matching indices has predecessor cofactor
strictly below 16(r+1) on the public 2048-bit interval. -/
theorem cofactor_bound {n p W j r : ℕ} (bits : 2^2047 ≤ n)
    (width : W = (9*n/2).sqrt-ceilSqrt (4*n)) (hp : p.Prime) (size : p < 2^1024)
    (g : (ZMod p)ˣ) (sj : j ≤ W)
    (count : ((range (W+1)).filter (fun i => g^i=g^j)).card = r) :
    W < (r+1)*orderOf g ∧ ∃ k, 0 < k ∧ k < 16*(r+1) ∧ k*orderOf g+1 = p := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [GeometricMatchRank.power_count g sj] at count
  have narrow := (range_bounds sj (orderOf_pos g) count.symm).2
  have divides : orderOf g ∣ p-1 := (Nat.prime_iff_card_units p).mp hp ▸ orderOf_dvd_card
  obtain ⟨k, hk⟩ := divides
  have eq : k*orderOf g+1 = p := by rw [mul_comm, ← hk]; have := hp.one_le; omega
  have minW : 2^1020 ≤ W := width ▸ GeometricDoubleMatch.width_at_2048 bits
  have hi : p ≤ 16*W := size.le.trans ((by decide +kernel : 2^1024=16*2^1020) ▸
    Nat.mul_le_mul_left 16 minW)
  refine ⟨narrow, k, ?_, ?_, eq⟩
  · by_contra! bad
    rw [show k=0 by omega, zero_mul, zero_add] at eq
    exact hp.ne_one eq.symm
  · by_contra! bad
    have high := Nat.mul_le_mul_right (orderOf g) bad
    rw [Nat.mul_assoc] at high
    omega

/-- Division-free measured variance and the scalar by which it is normalized. -/
def spread {R : Type*} [CommRing R] (r A B C₂ : R) := 12*((r-1)*B^2-2*r*A*C₂)
def scale {R : Type*} [CommRing R] (r A : R) := r^2*(r^2-1)*A^2

/-- The public probe vanishes at exactly the two signs of the order cofactor
when the variance has a nonzero normalization in the residue field. -/
theorem probe {K : Type*} [Field K] {r A B C₂ d k h : K} (nz : scale r A ≠ 0)
    (observed : spread r A B C₂ = scale r A*d^2) (cofactor : h*d = -1) :
    k^2*spread r A B C₂-scale r A = 0 ↔ k = h ∨ k = -h := by
  rw [observed, show k^2*(scale r A*d^2)-scale r A = scale r A*(k^2*d^2-1) by ring,
    mul_eq_zero, or_iff_right nz]
  simpa using (GeometricDoubleMatch.probe_zero (a:=1) (k:=k) one_ne_zero cofactor)

/-- An actual local geometric progression supplies both coefficient identities
from the public construction at its exact multiplicity. -/
theorem local_moments {p W j m : ℕ} [Fact p.Prime] (g : (ZMod p)ˣ) (sj : j≤W)
    (count : ((range (W+1)).filter (fun i => g^i=g^j)).card = m+2) :
    let r := m+2
    let d := orderOf g
    let F := signal W ((g:ZMod p)^j) (g:ZMod p) r
    let A := F.coeff r
    let B := F.coeff (m+1)
    let C₂ := F.coeff m
    (-2*B = (r:ZMod p)*A*(2*((j%d:ℕ):ZMod p)+((r:ZMod p)-1)*d)) ∧
      spread (r:ZMod p) A B C₂ = scale (r:ZMod p) A*(d:ZMod p)^2 := by
  let d := orderOf g
  have h := count
  rw [GeometricMatchRank.power_count g sj] at h
  obtain ⟨bounds, _⟩ := range_bounds sj (orderOf_pos g) h.symm
  have power (i : ℕ) : g^(j%d+i*d) = g^j := by
    apply pow_eq_pow_iff_modEq.mpr
    change (j%d+i*d)%d = j%d
    simp [Nat.add_mul_mod_self_right]
  have occ (i : ℕ) (_ : i<m+2) : (g:ZMod p)^(j%d+i*d) = (g:ZMod p)^j := by
    simpa only [Units.val_pow_eq_pow_val] using congrArg Units.val (power i)
  let H := (range (m+2)).image (fun i => j%d+i*d)
  let u := (∏ i ∈ range (W+1) \ H, ((g:ZMod p)^j-(g:ZMod p)^i)) * ((g:ZMod p)^j)^(m+2)
  have eq : signal W ((g:ZMod p)^j) (g:ZMod p) (m+2) =
      C u * rootPolynomial (fun i => ((j%d:ℕ):ZMod p)+(i:ZMod p)*(d:ZMod p)) (m+2) :=
    progression_reading (orderOf_pos g) _ _ (fun i hi => mem_range.mpr (Nat.lt_succ_of_le (bounds i hi))) occ
  dsimp only
  rw [eq]
  exact (readout u ((j%d:ℕ):ZMod p) (d:ZMod p) m).2

/-- The positive cofactor times the local period is −1 in its prime field. -/
private theorem normalized {p d k : ℕ} (h : k*d+1=p) : (k:ZMod p)*d = -1 := by
  apply eq_neg_of_add_eq_zero_left
  rw [← Nat.cast_mul, ← Nat.cast_one (R:=ZMod p), ← Nat.cast_add, h, ZMod.natCast_self]

/-- Project the public coefficients to one prime. This uses the true base's
multiplicative order solely to state the hypothesis and characterize the result. -/
theorem projected_mean {R : Type*} [CommRing R] {p W j m : ℕ} [Fact p.Prime]
    (f : R →+* ZMod p) (g : Rˣ) (sj : j≤W) :
    let b := Units.map f.toMonoidHom g
    let d := orderOf b
    let F := signal W ((g:R)^j) (g:R) (m+2)
    ((range (W+1)).filter (fun i => b^i=b^j)).card = m+2 →
      -2*f (F.coeff (m+1)) = ((m+2:ℕ):ZMod p)*f (F.coeff (m+2))*
        (2*((j%d:ℕ):ZMod p)+(((m+2:ℕ):ZMod p)-1)*d) := by
  let b := Units.map f.toMonoidHom g
  intro Fbase d F count
  have eq : (signal W ((g:R)^j) (g:R) (m+2)).map f = signal W ((b:ZMod p)^j) (b:ZMod p) (m+2) := by
    rw [map_signal, map_pow]
    rfl
  change -2*f ((signal W ((g:R)^j) (g:R) (m+2)).coeff (m+1)) = _
  have proj (i : ℕ) : f (F.coeff i) = (signal W ((b:ZMod p)^j) (b:ZMod p) (m+2)).coeff i := by
    rw [← coeff_map]; exact congrArg (fun P : (ZMod p)[X] => P.coeff i) eq
  change -2*f (F.coeff (m+1)) = _
  rw [proj, proj]
  exact (local_moments b sj count).1

private theorem label_equation {p r j d k : ℕ} {A B : ZMod p} (cofactor : k*d+1=p)
    (mean : -2*B = (r:ZMod p)*A*(2*((j%d:ℕ):ZMod p)+((r:ZMod p)-1)*d)) :
    -2*(k:ZMod p)*B+(r:ZMod p)*A*((r:ZMod p)-1-2*((j/d:ℕ):ZMod p)) = 2*k*r*A*j := by
  have decomposition : (j:ZMod p) = ((j%d:ℕ):ZMod p)+((j/d:ℕ):ZMod p)*(d:ZMod p) := by
    rw [← Nat.cast_mul, ← Nat.cast_add, Nat.mul_comm (j/d) d, Nat.mod_add_div]
  exact GeometricMatchRank.eliminate_period (at_rank mean decomposition) (normalized cofactor)

/-- Enumerate these `r` public candidates once a common predecessor cofactor
has been selected. The inverse normalizes all ranks at once. -/
def candidate {R : Type*} [CommRing R] (r k t : ℕ) (A B inv : R) : R :=
  (-2*(k:R)*B+(r:R)*A*((r:R)-1-2*(t:R)))*inv

/-- The real index occurs among the r candidates from public coefficients.
The two local means may use different periods. Equal multiplicities in the
same complete interval force the true rank t to agree. -/
theorem decode_from_means {p q W j r dp dq k : ℕ} (cop : p.Coprime q)
    (A B inv : ZMod (p*q)) (sj : j≤W) (cap : W<p*q) (dp_pos : 0<dp) (dq_pos : 0<dq)
    (pc : j/dp+(W-j)/dp+1=r) (qc : j/dq+(W-j)/dq+1=r)
    (pk : k*dp+1=p) (qk : k*dq+1=q)
    (pm : -2*(ZMod.chineseRemainder cop B).1 = (r:ZMod p)*(ZMod.chineseRemainder cop A).1*
      (2*((j%dp:ℕ):ZMod p)+((r:ZMod p)-1)*dp))
    (qm : -2*(ZMod.chineseRemainder cop B).2 = (r:ZMod q)*(ZMod.chineseRemainder cop A).2*
      (2*((j%dq:ℕ):ZMod q)+((r:ZMod q)-1)*dq)) (unit : 2*k*r*A*inv=1) :
    ∃ t < r, (candidate r k t A B inv).val=j := by
  let e := ZMod.chineseRemainder cop
  have rank := (GeometricMatchRank.equal_rank dp_pos dq_pos (by omega : j/dp+(W-j)/dp=j/dq+(W-j)/dq)).1
  have pe := label_equation pk pm
  have qe := label_equation qk qm
  rw [← rank] at qe
  have two : e 2=2 := by simpa only [Nat.cast_ofNat] using map_natCast e 2
  have full : -2*(k:ZMod (p*q))*B+(r:ZMod (p*q))*A*((r:ZMod (p*q))-1-2*((j/dp:ℕ):ZMod (p*q)))=
      2*k*r*A*j := by
    apply e.injective
    apply Prod.ext
    · simpa [e, two] using pe
    · simpa [e, two] using qe
  refine ⟨j/dp, pc ▸ Nat.lt_succ_of_le (Nat.le_add_right ..), ?_⟩
  rw [candidate, full, show (2:ZMod (p*q))*k*r*A*j*inv=j*(2*k*r*A*inv) by ring, unit,
    mul_one, ZMod.val_natCast_of_lt (sj.trans_lt cap)]

/-- Squared-period test stated for the actual top three measured coefficients.
For positive bounded cofactor guesses, `k+h<p` avoids sign collisions in a
prime field. -/
theorem probe_from_signal {p W j m h k : ℕ} [Fact p.Prime]
    (g : (ZMod p)ˣ) (sj : j≤W)
    (count : ((range (W+1)).filter (fun i => g^i=g^j)).card = m+2)
    (cofactor : h*orderOf g+1=p) (small : k+h<p) :
    let r := m+2
    let F := signal W ((g:ZMod p)^j) (g:ZMod p) r
    let A := F.coeff r
    let B := F.coeff (m+1)
    let C₂ := F.coeff m
    scale (r:ZMod p) A ≠ 0 →
    ((k:ZMod p)^2*spread (r:ZMod p) A B C₂-scale (r:ZMod p) A = 0 ↔ k=h) := by
  intro r F A B C₂ nz
  rw [probe nz (local_moments g sj count).2 (normalized cofactor)]
  constructor
  · rintro (same|opp)
    · have e := (ZMod.natCast_eq_natCast_iff' ..).mp same
      simpa only [Nat.mod_eq_of_lt (by omega : k<p), Nat.mod_eq_of_lt (by omega : h<p)] using e
    · have sum : ((k+h:ℕ):ZMod p)=0 := by push_cast; rw [opp, neg_add_cancel]
      have dv := (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp sum
      rcases Nat.eq_zero_or_pos (k+h) with z|pos
      · omega
      · exact False.elim (Nat.not_le_of_lt small (Nat.le_of_dvd pos dv))
  · rintro rfl; exact Or.inl rfl

/-- End-to-end equal-multiplicity decoding from the public directional
polynomial over the product. Each local cofactor is `k`, and the common
unknown exponent lies in `[0,W]`. The returned rank lies in `[0,r)`. -/
theorem from_signal {p q W j m k : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (g : (ZMod (p*q))ˣ) (y inv : ZMod (p*q))
    (target : (g:ZMod (p*q))^j=y) (sj : j≤W) (cap : W<p*q) :
    let e := ZMod.chineseRemainder cop
    let f := (RingHom.fst (ZMod p) (ZMod q)).comp e.toRingHom
    let h := (RingHom.snd (ZMod p) (ZMod q)).comp e.toRingHom
    let gp := Units.map f.toMonoidHom g
    let gq := Units.map h.toMonoidHom g
    let r := m+2
    let F := signal W y (g:ZMod (p*q)) r
    ((range (W+1)).filter (fun i => gp^i=gp^j)).card = r →
    ((range (W+1)).filter (fun i => gq^i=gq^j)).card = r →
    k*orderOf gp+1=p → k*orderOf gq+1=q → 2*k*r*F.coeff r*inv=1 →
    ∃ t < r, (candidate r k t (F.coeff r) (F.coeff (m+1)) inv).val=j := by
  subst y
  intro e f h gp gq r F pc qc pk qk unit
  have pm := projected_mean f g sj pc
  have qm := projected_mean h g sj qc
  rw [GeometricMatchRank.power_count gp sj] at pc
  rw [GeometricMatchRank.power_count gq sj] at qc
  exact decode_from_means cop _ _ inv sj cap (orderOf_pos gp) (orderOf_pos gq) pc qc pk qk pm qm unit

/-- At the exact local multiplicity, the top coefficient is a product of units.
Every coefficient at a lower perturbation order vanishes. The statement also
covers multiplicity one, and puts no limit on the number of matches. -/
theorem leading_status {p W j : ℕ} [Fact p.Prime] (g : (ZMod p)ˣ) :
    let H := (range (W+1)).filter (fun i => g^i=g^j)
    let y := (g:ZMod p)^j
    (signal W y (g:ZMod p) H.card).coeff H.card ≠ 0 ∧
      ∀ r < H.card, signal W y (g:ZMod p) r = 0 := by
  classical
  let S := range (W+1)
  let H := S.filter (fun i => g^i=g^j)
  let y := (g:ZMod p)^j
  have sub : H ⊆ S := filter_subset _ _
  have hits (i : ℕ) (hi : i∈H) : (g:ZMod p)^i = y := by
    simpa only [y, Units.val_pow_eq_pow_val] using congrArg Units.val (mem_filter.mp hi).2
  have other (i : ℕ) (hi : i∈S \ H) : y-(g:ZMod p)^i ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have eq : g^i=g^j := Units.ext (by simpa only [Units.val_pow_eq_pow_val] using h.symm)
    exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨(mem_sdiff.mp hi).1, eq⟩)
  let u := (∏ i ∈ S \ H, (y-(g:ZMod p)^i)) * y^H.card
  have nz : u≠0 := mul_ne_zero (prod_ne_zero_iff.mpr other) (pow_ne_zero _ (pow_ne_zero _ g.ne_zero))
  let P : (ZMod p)[X] := ∏ i ∈ H, (X-C (i:ZMod p))
  have occupied (i : ℕ) (hi : i∈H) : (C (g:ZMod p))^i=C y := by rw [← map_pow, hits i hi]
  have reading : signal W y (g:ZMod p) H.card = C u * P := by
    have eq := directional_reading sub (C y) (C (g:ZMod p)) (X:(ZMod p)[X]) occupied
    simpa only [signal, S, P, u, map_mul, map_prod, map_sub, map_pow, map_natCast] using eq
  have monic : P.Monic := monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)
  have degree : P.natDegree = H.card := natDegree_finset_prod_X_sub_C_eq_card _ _
  have top : P.coeff H.card = 1 := degree ▸ monic
  constructor
  · change (signal W y (g:ZMod p) H.card).coeff H.card ≠ 0
    rwa [reading, coeff_C_mul, top, mul_one]
  · intro r hr
    apply (first_product_coefficient sub
      (fun i => directionalFactor (C y) (C (g:ZMod p)) (X:(ZMod p)[X]) i) _).1 r hr
    intro i hi
    rw [coeff_zero_eq_eval_zero]
    simp [directionalFactor, occupied i hi]

private theorem small_cast_ne_zero {p n : ℕ} [NeZero p] (pos : 0<n) (small : n<p) :
    (n:ZMod p) ≠ 0 := by
  intro h
  have eq := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt small, ZMod.val_zero] at eq
  omega

/-- In a 1024-bit prime field the measured variance scale cannot vanish for
multiplicities from two through 2^64. -/
theorem scale_target {p W j r : ℕ} [Fact p.Prime] (large : 2^1023≤p)
    (lo : 2≤r) (cap : r≤2^64) (g : (ZMod p)ˣ)
    (count : ((range (W+1)).filter (fun i => g^i=g^j)).card=r) :
    scale (r:ZMod p) ((signal W ((g:ZMod p)^j) (g:ZMod p) r).coeff r) ≠ 0 := by
  have big : (2:ℕ)^64 < 2^1023 := by decide +kernel
  have high := cap.trans_lt (big.trans_le large)
  have n0 : (r:ZMod p) ≠ 0 := small_cast_ne_zero (by omega) high
  have nh : r^2<p := (Nat.pow_le_pow_left cap 2).trans_lt
    ((by decide +kernel : ((2:ℕ)^64)^2 < 2^1023).trans_le large)
  have n1 : (r:ZMod p)^2-1 ≠ 0 := by
    intro eq
    have e := congrArg ZMod.val (sub_eq_zero.mp eq)
    rw [← Nat.cast_pow, ZMod.val_natCast_of_lt nh, ZMod.val_one] at e
    have h := Nat.pow_le_pow_left lo 2
    omega
  have A := (leading_status g (W:=W) (j:=j)).1
  rw [count] at A
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ n0) n1) (pow_ne_zero _ A)

/-- Each bounded probe now tests precisely the true local order cofactor,
including the nonvanishing and sign conditions proved from the input scale. -/
theorem target_probe {n p W j m : ℕ} [hp : Fact p.Prime] (bits : 2^2047≤n)
    (width : W=(9*n/2).sqrt-ceilSqrt (4*n)) (lo : 2^1023≤p) (hi : p<2^1024)
    (g : (ZMod p)ˣ) (sj : j≤W) (cap : m+2≤2^64)
    (count : ((range (W+1)).filter (fun i => g^i=g^j)).card=m+2) :
    let r := m+2
    let F := signal W ((g:ZMod p)^j) (g:ZMod p) r
    let A := F.coeff r
    ∃ h, 0<h ∧ h<16*(r+1) ∧ h*orderOf g+1=p ∧ ∀ k < 16*(r+1),
      (k:ZMod p)^2*spread (r:ZMod p) A (F.coeff (m+1)) (F.coeff m)-scale (r:ZMod p) A=0 ↔ k=h := by
  obtain ⟨_, h, hpos, hhi, eq⟩ := cofactor_bound bits width hp.out hi g sj count
  intro r F A
  refine ⟨h, hpos, hhi, eq, ?_⟩
  intro k hk
  have small : k+h < p := by
    have c : 32*((2:ℕ)^64+1) < 2^1023 := by decide +kernel
    dsimp [r] at hk
    omega
  exact probe_from_signal g sj count eq small (scale_target lo (by omega) cap g count)

private theorem projected_coefficient {R : Type*} [CommRing R] {p : ℕ}
    (f : R →+* ZMod p) (g : Rˣ) (W j r i : ℕ) :
    let b := Units.map f.toMonoidHom g
    f ((signal W ((g:R)^j) (g:R) r).coeff i) =
      (signal W ((b:ZMod p)^j) (b:ZMod p) r).coeff i := by
  rw [← coeff_map, map_signal, map_pow]
  rfl

private theorem factor_of_projections {p q : ℕ} [hp : Fact p.Prime] [Fact q.Prime]
    (x : ZMod (p*q)) (f : ZMod (p*q) →+* ZMod p) (h : ZMod (p*q) →+* ZMod q)
    (nonzero : f x ≠ 0) (zero : h x = 0) : (p*q).gcd x.val = q := by
  have P : (x.val:ZMod p) = f x := by rw [← map_natCast f, ZMod.natCast_zmod_val]
  have Q : (x.val:ZMod q) = h x := by rw [← map_natCast h, ZMod.natCast_zmod_val]
  apply Nat.gcd_mul_of_coprime_of_dvd
  · apply hp.out.coprime_iff_not_dvd.mpr
    intro divides
    exact nonzero (P.symm.trans ((ZMod.natCast_zmod_eq_zero_iff_dvd ..).mpr divides))
  · exact (ZMod.natCast_zmod_eq_zero_iff_dvd ..).mp (Q.trans zero)

/-- At the smaller of two unequal true multiplicities, a single public
coefficient has gcd exactly the prime with larger multiplicity. The order of
the local primes in this statement may be chosen freely. -/
theorem unequal_counts {p q W j : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (g : (ZMod (p*q))ˣ) (y : ZMod (p*q)) (target : (g:ZMod (p*q))^j=y) :
    let e := ZMod.chineseRemainder cop
    let f := (RingHom.fst (ZMod p) (ZMod q)).comp e.toRingHom
    let h := (RingHom.snd (ZMod p) (ZMod q)).comp e.toRingHom
    let gp := Units.map f.toMonoidHom g
    let gq := Units.map h.toMonoidHom g
    let rp := ((range (W+1)).filter (fun i => gp^i=gp^j)).card
    let rq := ((range (W+1)).filter (fun i => gq^i=gq^j)).card
    rp < rq → (p*q).gcd ((signal W y (g:ZMod (p*q)) rp).coeff rp).val = q := by
  subst y
  intro e f h gp gq rp rq lt
  apply factor_of_projections _ f h
  · rw [projected_coefficient]
    exact (leading_status gp (W:=W) (j:=j)).1
  · rw [projected_coefficient, (leading_status gq (W:=W) (j:=j)).2 rp lt, coeff_zero]

private theorem normalization_at_prime {p W j r k : ℕ} [Fact p.Prime]
    (large : 2^1023≤p) (rpos : 0<r) (cap : r≤2^64) (kp : 0<k) (small : k<16*(r+1))
    (g : (ZMod p)ˣ) (count : ((range (W+1)).filter (fun i => g^i=g^j)).card=r) :
    (2:ZMod p)*k*r*(signal W ((g:ZMod p)^j) (g:ZMod p) r).coeff r ≠ 0 := by
  have c : 32*((2:ℕ)^64+1) < 2^1023 := by decide +kernel
  have two := small_cast_ne_zero (p:=p) (by decide : 0<2) (by omega)
  have kr := small_cast_ne_zero kp (by omega : k<p)
  have rr := small_cast_ne_zero rpos (by omega : r<p)
  have A := (leading_status g (W:=W) (j:=j)).1
  rw [count] at A
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero two kr) rr) A

/-- In the capped equal-multiplicity case, the linear decoder's inverse also
exists across the full product for every positive cofactor on the menu. -/
theorem normalization_target {p q W j r k : ℕ} [Fact p.Prime] [Fact q.Prime]
    (cop : p.Coprime q) (pl : 2^1023≤p) (ql : 2^1023≤q) (rpos : 0<r) (cap : r≤2^64)
    (kp : 0<k) (bound : k<16*(r+1)) (g : (ZMod (p*q))ˣ) (y : ZMod (p*q))
    (target : (g:ZMod (p*q))^j=y) :
    let e := ZMod.chineseRemainder cop
    let f := (RingHom.fst (ZMod p) (ZMod q)).comp e.toRingHom
    let h := (RingHom.snd (ZMod p) (ZMod q)).comp e.toRingHom
    let gp := Units.map f.toMonoidHom g
    let gq := Units.map h.toMonoidHom g
    let A := (signal W y (g:ZMod (p*q)) r).coeff r
    ((range (W+1)).filter (fun i => gp^i=gp^j)).card=r →
    ((range (W+1)).filter (fun i => gq^i=gq^j)).card=r →
    (2*k*r*A)*(2*k*r*A)⁻¹=1 := by
  subst y
  intro e f h gp gq A pc qc
  apply ZMod.mul_inv_of_unit
  apply (isUnit_map_iff e _).mp
  apply Prod.isUnit_iff.mpr
  change IsUnit (f (2*k*r*A)) ∧ IsUnit (h (2*k*r*A))
  constructor
  · apply isUnit_iff_ne_zero.mpr
    simp only [map_mul, map_ofNat, map_natCast, A, projected_coefficient]
    exact normalization_at_prime pl rpos cap kp bound gp pc
  · apply isUnit_iff_ne_zero.mpr
    simp only [map_mul, map_ofNat, map_natCast, A, projected_coefficient]
    exact normalization_at_prime ql rpos cap kp bound gq qc

end PrimeFactors.GeometricMultiplicityReadout
