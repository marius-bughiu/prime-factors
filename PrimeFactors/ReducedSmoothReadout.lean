import PrimeFactors.ReducedSlopes
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.Log

/-! A bounded prime-power sweep after the publicly visible exponent N-1. -/

namespace PrimeFactors.ReducedSmoothReadout

/-- Return the last value before the first global identity, or the final value
if the scan never reaches that identity. -/
def readout {G : Type*} [Monoid G] [DecidableEq G] (x : G) : List ℕ → G
  | [] => x
  | m :: ms => if x^m = 1 then x else readout (x^m) ms

/-- Each numerical checkpoint can be proved independently before combining the scan. -/
theorem live_step {G : Type*} [Monoid G] [DecidableEq G] {x y : G} {m : ℕ}
    (ms : List ℕ) (step : x^m = y) (live : y ≠ 1) :
    readout x (m :: ms) = readout y ms := by simp only [readout,step,if_neg live]

theorem identity_step {G : Type*} [Monoid G] [DecidableEq G] {x : G} {m : ℕ}
    (ms : List ℕ) (step : x^m = 1) : readout x (m :: ms) = x := by
  simp only [readout,if_pos step]

/-- The two coordinates differ in whether they are the multiplicative identity. -/
def separated {G H : Type*} [One G] [One H] (w : G × H) : Prop :=
  (w.1 = 1 ∧ w.2 ≠ 1) ∨ (w.1 ≠ 1 ∧ w.2 = 1)

private theorem separated_of_one {G H : Type*} [One G] [One H] {z : G × H}
    (nz : z ≠ 1) (h : z.1 = 1 ∨ z.2 = 1) : separated z := by
  rcases h with h | h
  · exact Or.inl ⟨h, fun h' => nz (Prod.ext h h')⟩
  · exact Or.inr ⟨fun h' => nz (Prod.ext h' h), h⟩

/-- Coprime local orders cannot both be nontrivial divisors of a prime power. -/
theorem before_saturation {G H : Type*} [Group G] [Group H] {x : G} {y : H} {m : ℕ}
    (cp : (orderOf x).Coprime (orderOf y)) (nz : (x,y) ≠ 1)
    (primepow : IsPrimePow m) (hit : (x,y)^m = 1) : separated (x,y) := by
  obtain ⟨r,k,hr,_,rfl⟩ := (isPrimePow_nat_iff _).mp primepow
  have xp : x^(r^k) = 1 := congrArg Prod.fst hit
  have yp : y^(r^k) = 1 := congrArg Prod.snd hit
  obtain ⟨a,_,ha⟩ := (Nat.dvd_prime_pow hr).mp (orderOf_dvd_of_pow_eq_one xp)
  obtain ⟨b,_,hb⟩ := (Nat.dvd_prime_pow hr).mp (orderOf_dvd_of_pow_eq_one yp)
  apply separated_of_one nz
  by_cases az : a = 0
  · exact Or.inl (orderOf_eq_one_iff.mp (by simpa [az] using ha))
  by_cases bz : b = 0
  · exact Or.inr (orderOf_eq_one_iff.mp (by simpa [bz] using hb))
  have dr : r ∣ (orderOf x).gcd (orderOf y) :=
    Nat.dvd_gcd (ha ▸ dvd_pow_self r az) (hb ▸ dvd_pow_self r bz)
  rw [cp.gcd_eq_one] at dr
  exact (hr.ne_one (Nat.dvd_one.mp dr)).elim

/-- The one final readout separates whenever either local order divides the
entire scheduled exponent. This holds for every accepted base. -/
theorem readout_separates {G H : Type*} [Group G] [Group H] [DecidableEq G] [DecidableEq H]
    (blocks : List ℕ) (powers : ∀ m ∈ blocks, IsPrimePow m) (x : G) (y : H)
    (cp : (orderOf x).Coprime (orderOf y)) (nz : (x,y) ≠ 1)
    (covered : orderOf x ∣ blocks.prod ∨ orderOf y ∣ blocks.prod) :
    separated (readout (x,y) blocks) := by
  induction blocks generalizing x y with
  | nil =>
    apply separated_of_one nz
    rcases covered with h | h
    · exact Or.inl (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h))
    · exact Or.inr (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h))
  | cons m ms ih =>
    simp only [readout]
    split_ifs with hit
    · exact before_saturation cp nz (powers _ (by simp)) hit
    · apply ih (fun a ha => powers a (by simp [ha])) (x^m) (y^m)
        (cp.of_dvd (orderOf_pow_dvd _) (orderOf_pow_dvd _)) hit
      rcases covered with h | h
      · exact Or.inl (orderOf_dvd_of_pow_eq_one (by
          rw [← pow_mul]; exact orderOf_dvd_iff_pow_eq_one.mp h))
      · exact Or.inr (orderOf_dvd_of_pow_eq_one (by
          rw [← pow_mul]; exact orderOf_dvd_iff_pow_eq_one.mp h))

/-- Conversely, a separated readout implies that some local order divides
the full scheduled exponent, even if the scan stopped early. -/
theorem covered_of_readout {G H : Type*} [Group G] [Group H] [DecidableEq G] [DecidableEq H]
    (blocks : List ℕ) (x : G) (y : H) (split : separated (readout (x,y) blocks)) :
    orderOf x ∣ blocks.prod ∨ orderOf y ∣ blocks.prod := by
  induction blocks generalizing x y with
  | nil =>
    rcases split with h | h
    · exact Or.inl (orderOf_dvd_of_pow_eq_one (by simpa using h.1))
    · exact Or.inr (orderOf_dvd_of_pow_eq_one (by simpa using h.2))
  | cons m ms ih =>
    by_cases stop : (x,y)^m = 1
    · exact Or.inl ((orderOf_dvd_of_pow_eq_one (show x^m = 1 from congrArg Prod.fst stop)).trans
        (dvd_mul_right _ _))
    · rw [readout, if_neg stop] at split
      rcases ih (x^m) (y^m) split with h | h
      · exact Or.inl (orderOf_dvd_of_pow_eq_one (by
          rw [List.prod_cons, pow_mul]; exact orderOf_dvd_iff_pow_eq_one.mp h))
      · exact Or.inr (orderOf_dvd_of_pow_eq_one (by
          rw [List.prod_cons, pow_mul]; exact orderOf_dvd_iff_pow_eq_one.mp h))

/-- Specialization to the hidden prime-field unit groups. The common part of
the two predecessors need not divide the scheduled exponent. -/
theorem reduced_readout {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (x : (ZMod p)ˣ) (y : (ZMod q)ˣ) (blocks : List ℕ)
    (powers : ∀ m ∈ blocks, IsPrimePow m)
    (nz : (x^(p*q-1),y^(p*q-1)) ≠ 1)
    (covered : (p-1)/(p-1).gcd (q-1) ∣ blocks.prod ∨
      (q-1)/(p-1).gcd (q-1) ∣ blocks.prod) :
    separated (readout (x^(p*q-1), y^(p*q-1)) blocks) := by
  apply readout_separates blocks powers _ _ (reduced_periods_coprime hp hq x y) nz
  rcases covered with h | h
  · exact Or.inl ((order_product_predecessor_dvd hp hq.pos x).trans h)
  · apply Or.inr
    have oq := order_product_predecessor_dvd hq hp.pos y
    rw [Nat.mul_comm q p, Nat.gcd_comm (q-1) (p-1)] at oq
    exact oq.trans h

private theorem equiv_readout {G H : Type*} [Monoid G] [Monoid H] [DecidableEq G] [DecidableEq H]
    (e : G ≃* H) (x : G) (blocks : List ℕ) :
    e (readout x blocks) = readout (e x) blocks := by
  induction blocks generalizing x with
  | nil => rfl
  | cons m ms ih =>
    simp only [readout, ← map_pow, ← map_one e, e.injective.eq_iff]
    split_ifs <;> simp_all

/-- Checking identity and updating powers may be done on the underlying modular
residue; the public algorithm never needs the unit's inverse. -/
theorem value_readout {G : Type*} [Monoid G] [DecidableEq G] (u : Gˣ) (blocks : List ℕ) :
    ((readout u blocks : Gˣ) : G) = readout (u : G) blocks := by
  induction blocks generalizing u with
  | nil => rfl
  | cons e es ih =>
    simp only [readout]
    by_cases hu : u^e = 1
    · have hv : (u : G)^e = 1 := congrArg Units.val hu
      simp [hu, hv]
    · have hv : (u : G)^e ≠ 1 := fun h => hu (Units.ext h)
      simpa [hu,hv] using ih (u^e)

private theorem one_gcd {p q v : ℕ} (hq : q.Prime) (pos : 0 < v)
    (atp : (v : ZMod p) = 1) (atq : (v : ZMod q) ≠ 1) :
    (v-1).gcd (p*q) = p := by
  have hp : Nat.ModEq p 1 v := (ZMod.natCast_eq_natCast_iff _ _ _).1 (by simpa using atp.symm)
  have dp := (Nat.modEq_iff_dvd' pos).1 hp
  have dq : ¬q ∣ v-1 := by
    intro h
    apply atq
    simpa using ((ZMod.natCast_eq_natCast_iff _ _ _).2 ((Nat.modEq_iff_dvd' pos).2 h).symm)
  rw [Nat.gcd_comm, Nat.mul_comm p q]
  exact Nat.gcd_mul_of_coprime_of_dvd (hq.coprime_iff_not_dvd.mpr dq) dp

/-- Actual one-gcd result in the public product ring for any accepted seed. -/
theorem public_gcd {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (different : p ≠ q)
    [NeZero (p*q)] (seed : (ZMod (p*q))ˣ) (blocks : List ℕ)
    (powers : ∀ m ∈ blocks, IsPrimePow m) (accepted : seed^(p*q-1) ≠ 1)
    (covered : (p-1)/(p-1).gcd (q-1) ∣ blocks.prod ∨
      (q-1)/(p-1).gcd (q-1) ∣ blocks.prod) :
    let u := readout (seed^(p*q-1)) blocks
    ((u : ZMod (p*q)).val-1).gcd (p*q) = p ∨ ((u : ZMod (p*q)).val-1).gcd (p*q) = q := by
  classical
  let iso : (ZMod (p*q))ˣ ≃* (ZMod p)ˣ × (ZMod q)ˣ :=
    (Units.mapEquiv (ZMod.chineseRemainder ((Nat.coprime_primes hp hq).mpr different)).toMulEquiv).trans
      MulEquiv.prodUnits
  let x := seed^(p*q-1)
  let u := readout x blocks
  let v := (u : ZMod (p*q)).val
  change (v-1).gcd (p*q) = p ∨ (v-1).gcd (p*q) = q
  have pos : 0 < v := by
    by_contra! h
    have hc := ZMod.val_coe_unit_coprime u
    change v.Coprime (p*q) at hc
    rw [show v = 0 by omega, Nat.coprime_zero_left] at hc
    have := hp.one_lt
    have := hq.one_lt
    nlinarith
  have neq : ((iso seed).1^(p*q-1), (iso seed).2^(p*q-1)) ≠ 1 := by
    change iso seed ^ (p*q-1) ≠ 1
    rw [← map_pow, ← map_one iso, iso.injective.ne_iff]
    exact accepted
  have sep := reduced_readout hp hq (iso seed).1 (iso seed).2 blocks powers neq covered
  have hmap := equiv_readout iso x blocks
  change iso u = readout (iso (seed^(p*q-1))) blocks at hmap
  rw [map_pow] at hmap
  change separated (readout (iso seed^(p*q-1)) blocks) at sep
  rw [← hmap] at sep
  have cp : ((iso u).1 : ZMod p) = (v : ZMod p) := by
    change (ZMod.chineseRemainder ((Nat.coprime_primes hp hq).mpr different) (u : ZMod (p*q))).1 = (v : ZMod p)
    rw [← show (v : ZMod (p*q)) = (u : ZMod (p*q)) from ZMod.natCast_zmod_val _, map_natCast]
    rfl
  have cq : ((iso u).2 : ZMod q) = (v : ZMod q) := by
    change (ZMod.chineseRemainder ((Nat.coprime_primes hp hq).mpr different) (u : ZMod (p*q))).2 = (v : ZMod q)
    rw [← show (v : ZMod (p*q)) = (u : ZMod (p*q)) from ZMod.natCast_zmod_val _, map_natCast]
    rfl
  rcases sep with ⟨hp',hq'⟩ | ⟨hp',hq'⟩
  · apply Or.inl
    exact one_gcd hq pos (cp.symm.trans (congrArg Units.val hp')) (fun e => hq' (Units.ext (cq.trans e)))
  · apply Or.inr
    rw [Nat.mul_comm p q]
    exact one_gcd hp pos (cq.symm.trans (congrArg Units.val hq')) (fun e => hp' (Units.ext (cp.trans e)))

/-- Ascending primes up to the budget, each raised to its largest power
at most the public cap. -/
noncomputable def schedule (bound cap : ℕ) : List ℕ :=
  ((List.range (bound+1)).filter (fun r => decide (r.Prime ∧ r ≤ cap))).map (fun r => r^Nat.log r cap)

theorem schedule_powers (bound cap : ℕ) : ∀ m ∈ schedule bound cap, IsPrimePow m := by
  intro m hm
  obtain ⟨r, h, rfl⟩ := List.mem_map.mp hm
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at h
  exact (isPrimePow_nat_iff _).mpr ⟨r,_,h.2.1,Nat.log_pos h.2.1.one_lt h.2.2,rfl⟩

/-- All bounded smooth integers divide the full scheduled exponent. -/
theorem smooth_dvd_schedule {r bound cap : ℕ} (hr : 0 < r) (fits : r ≤ cap)
    (smooth : ∀ l, l.Prime → l ∣ r → l ≤ bound) : r ∣ (schedule bound cap).prod := by
  by_cases hz : (schedule bound cap).prod = 0
  · simp [hz]
  apply (Nat.factorization_le_iff_dvd hr.ne' hz).mp
  intro l
  by_cases p : l.Prime
  · by_cases d : l ∣ r
    · have le := (Nat.le_of_dvd hr d).trans fits
      have member : l^Nat.log l cap ∈ schedule bound cap := by
        apply List.mem_map.mpr
        refine ⟨l, ?_, rfl⟩
        simp [p,le,Nat.lt_succ_of_le (smooth l p d)]
      apply (p.pow_dvd_iff_le_factorization hz).mp
      apply Dvd.dvd.trans _ (List.dvd_prod member)
      apply pow_dvd_pow
      exact Nat.le_log_of_pow_le p.one_lt ((Nat.le_of_dvd hr (Nat.ordProj_dvd r l)).trans fits)
    · simp [Nat.factorization_eq_zero_of_not_dvd d]
  · simp [Nat.factorization_eq_zero_of_non_prime _ p]

/-- A single failed gcd excludes smoothness at both reduced predecessors. -/
theorem exhaustion {p q bound cap : ℕ} (hp : p.Prime) (hq : q.Prime) (different : p ≠ q)
    [NeZero (p*q)] (seed : (ZMod (p*q))ˣ) (accepted : seed^(p*q-1) ≠ 1)
    (pfit : p-1 ≤ cap) (qfit : q-1 ≤ cap)
    (failed : let u := readout (seed^(p*q-1)) (schedule bound cap)
              ((u : ZMod (p*q)).val-1).gcd (p*q) = 1) :
    (∃ l : ℕ, l.Prime ∧ l ∣ (p-1)/(p-1).gcd (q-1) ∧ bound < l) ∧
    (∃ l : ℕ, l.Prime ∧ l ∣ (q-1)/(p-1).gcd (q-1) ∧ bound < l) := by
  have a := Nat.sub_pos_of_lt hp.one_lt
  have b := Nat.sub_pos_of_lt hq.one_lt
  have gp := Nat.gcd_pos_of_pos_left (q-1) a
  have rp := Nat.div_pos (Nat.gcd_le_left _ a) gp
  have rq := Nat.div_pos (Nat.gcd_le_right _ b) gp
  have nope := fun h => public_gcd hp hq different seed (schedule bound cap)
    (schedule_powers bound cap) accepted h
  constructor
  · by_contra! h
    have d := smooth_dvd_schedule rp ((Nat.div_le_self _ _).trans pfit) h
    simpa [failed, Ne.symm hp.ne_one, Ne.symm hq.ne_one] using nope (Or.inl d)
  · by_contra! h
    have d := smooth_dvd_schedule rq ((Nat.div_le_self _ _).trans qfit) h
    simpa [failed, Ne.symm hp.ne_one, Ne.symm hq.ne_one] using nope (Or.inr d)

/-- The finite conclusion of the GRH least-prime-outside-subgroup theorem
supplies a small base whose acceptance can be checked from the product. -/
theorem exists_accepted_base {p q bound : ℕ} (hp : p.Prime) (hq : q.Prime) (lt : p < q)
    (outside : SmallPrimeOutside (p*q) bound) :
    ∃ a : ℕ, a.Prime ∧ a ≤ bound ∧ ∃ ha : a.Coprime (p*q),
      (ZMod.unitOfCoprime a ha)^(p*q-1) ≠ 1 := by
  classical
  letI : NeZero (p*q) := ⟨mul_ne_zero hp.ne_zero hq.ne_zero⟩
  let f : (ZMod (p*q))ˣ →* (ZMod (p*q))ˣ := powMonoidHom (p*q-1)
  have proper : f.ker ≠ ⊤ := by
    intro h
    have all : (Finset.univ.filter (fun x : (ZMod (p*q))ˣ => x^(p*q-1) = 1)) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro x _
      have hx : x ∈ f.ker := h ▸ Subgroup.mem_top x
      exact hx
    have count := count_product_predecessor_identity hp hq lt.ne
    rw [all, Finset.card_univ, ZMod.card_units_eq_totient, Nat.totient_mul
      ((Nat.coprime_primes hp hq).mpr lt.ne), Nat.totient_prime hp, Nat.totient_prime hq] at count
    have hpos : 0 < p-1 := Nat.sub_pos_of_lt hp.one_lt
    have small := Nat.gcd_le_left (q-1) hpos
    have big : (p-1).gcd (q-1) < q-1 := by omega
    nlinarith [Nat.mul_le_mul small small, Nat.mul_lt_mul_of_pos_left (show p-1 < q-1 by omega) hpos]
  obtain ⟨a, hpr, hle, ha, hnot⟩ := outside f.ker proper
  exact ⟨a,hpr,hle,ha,hnot⟩

end PrimeFactors.ReducedSmoothReadout
