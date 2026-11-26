import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring

/-! An ordinary product gcd on arbitrary labels identifies which prime has
a match. On consecutive labels, two shared hit positions reveal the exact
common local order and hence a second-order congruence for the hidden sum. -/

namespace PrimeFactors.GeometricOrderReadout

open Finset

/-- The public product, represented by any congruent integer in the oracle. -/
noncomputable def sample (I : Finset ℕ) (g : ℤ) (E : ℕ) : ℤ :=
  ∏ i∈I, (g^E-g^i)

def localHit (I : Finset ℕ) (g : ℤ) (p E : ℕ) : Prop :=
  ∃ i∈I, (g:ZMod p)^i=(g:ZMod p)^E

private theorem local_hit_iff {p : ℕ} (hp : p.Prime) (g v : ℤ) (E : ℕ) (I : Finset ℕ)
    (rep : v ≡ sample I g E [ZMOD (p:ℤ)]) :
    p∣v.natAbs ↔ localHit I g p E := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [←Int.natCast_dvd,←ZMod.intCast_zmod_eq_zero_iff_dvd,
    (ZMod.intCast_eq_intCast_iff _ _ p).mpr rep]
  simp only [sample,Int.cast_prod,Int.cast_sub,Int.cast_pow,prod_eq_zero_iff,
    sub_eq_zero,localHit,eq_comm (a:=((g:ZMod p)^E))]

/-- A single representative distinguishes all four possibilities. In particular
a proper gcd is the prime with a match in the queried set. -/
theorem oracle {p q E : ℕ} (hp : p.Prime) (hq : q.Prime) (ne : p≠q)
    (g v : ℤ) (I : Finset ℕ) (rep : v ≡ sample I g E [ZMOD (p:ℤ)*q]) :
    let P := localHit I g p E
    let Q := localHit I g q E
    (¬P → ¬Q → (p*q).gcd v.natAbs=1) ∧
    (P → ¬Q → (p*q).gcd v.natAbs=p) ∧
    (¬P → Q → (p*q).gcd v.natAbs=q) ∧
    (P → Q → (p*q).gcd v.natAbs=p*q) := by
  let cop := (Nat.coprime_primes hp hq).mpr ne
  have lp := local_hit_iff hp g v E I (rep.of_dvd (dvd_mul_right ..))
  have lq := local_hit_iff hq g v E I (rep.of_dvd (dvd_mul_left ..))
  refine ⟨fun a b => (Nat.coprime_mul_iff_left.mpr ⟨hp.coprime_iff_not_dvd.mpr (mt lp.mp a),
    hq.coprime_iff_not_dvd.mpr (mt lq.mp b)⟩).gcd_eq_one,?_,?_,?_⟩
  · intro a b
    rw [Nat.mul_comm p q]
    exact Nat.gcd_mul_of_coprime_of_dvd (hq.coprime_iff_not_dvd.mpr (mt lq.mp b)) (lp.mpr a)
  · intro a b
    exact Nat.gcd_mul_of_coprime_of_dvd (hp.coprime_iff_not_dvd.mpr (mt lp.mp a)) (lq.mpr b)
  · intro a b
    exact Nat.gcd_eq_left (cop.mul_dvd_of_dvd_of_dvd (lp.mpr a) (lq.mpr b))

/-- A dense query from zero changes from empty to occupied at a single public
index determined here in terms of the unknown order. -/
theorem prefix_threshold {G : Type*} [Group G] (g : G) (E u : ℕ) :
    (∃ i≤u, g^i=g^E) ↔ E%orderOf g≤u := by
  constructor
  · rintro ⟨i,hi,eq⟩
    have same : i%orderOf g=E%orderOf g := pow_eq_pow_iff_modEq.mp eq
    exact same ▸ (Nat.mod_le i _).trans hi
  · intro bound
    exact ⟨_,bound,pow_eq_pow_iff_modEq.mpr (Nat.mod_mod ..)⟩

/-- Once a hit a is shared, querying a+1 through u detects the next hit
of a given prime precisely when u reaches a plus its order. -/
theorem suffix_threshold {G : Type*} [Group G] [Finite G] (g : G) {a E u : ℕ}
    (hit : g^a=g^E) :
    (∃ i, a < i ∧ i≤u ∧ g^i=g^E) ↔ a+orderOf g≤u := by
  constructor
  · rintro ⟨i,gt,le,eq⟩
    have dvd : orderOf g ∣ i-a := orderOf_dvd_of_pow_eq_one (x:=g) (by
      apply mul_left_cancel (a:=g^a)
      rw [←pow_add,Nat.add_sub_of_le gt.le,eq,hit,mul_one])
    have step := Nat.le_of_dvd (by omega : 0 < i-a) dvd
    omega
  · intro le
    exact ⟨_,by have := orderOf_pos g; omega,le,by simp [pow_add,hit,pow_orderOf_eq_one]⟩

/-- A binary search for any hit in a prefix has this single threshold. -/
theorem union_prefix {G H : Type*} [Group G] [Group H] (g : G) (h : H) (E u : ℕ) :
    ((∃ i≤u, g^i=g^E) ∨ (∃ i≤u, h^i=h^E)) ↔ min (E%orderOf g) (E%orderOf h)≤u := by
  rw [prefix_threshold,prefix_threshold,min_le_iff]

/-- When the first hit is shared, the first occupied suffix endpoint is at the
smaller of the two local periods after it. -/
theorem union_suffix {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (g : G) (h : H) {a E u : ℕ} (ga : g^a=g^E) (ha : h^a=h^E) :
    ((∃ i, a < i ∧ i≤u ∧ g^i=g^E) ∨ (∃ i, a < i ∧ i≤u ∧ h^i=h^E)) ↔
      a+min (orderOf g) (orderOf h)≤u := by
  rw [suffix_threshold g ga,suffix_threshold h ha]
  omega

/-- Two consecutive local hits in a dense interval measure the exact period,
regardless of the number of other hits before or after them. -/
theorem consecutive_order {G : Type*} [Group G] [Finite G] (g : G) {a b E : ℕ}
    (lt : a < b) (first : g^a=g^E) (second : g^b=g^E)
    (gap : ∀ i, a < i → i < b → g^i≠g^E) : orderOf g=b-a := by
  have lower := (suffix_threshold g first (u:=b)).mp ⟨b,lt,le_rfl,second⟩
  have eq : g^(a+orderOf g)=g^E := by simp [pow_add,pow_orderOf_eq_one,first]
  have pos := orderOf_pos g
  by_contra bad
  exact gap (a+orderOf g) (by omega) (by omega) eq

/-- Least sum at or above L congruent to N+1 modulo d², assuming L≤N+1. -/
def roundedSum (N L d : ℕ) : ℕ := L+(N+1-L)%(d^2)

/-- A common divisor of both prime predecessors is enough. Its square divides
the totient (pq+1)−(p+q), whether or not the base has precisely that order. -/
theorem sum_residue {p q d : ℕ} (pp : 0 < p) (qp : 0 < q) (dp : d∣p-1) (dq : d∣q-1) :
    ∃ t, p*q+1=p+q+d^2*t := by
  obtain ⟨u,hu⟩ := dp
  obtain ⟨v,hv⟩ := dq
  have eqp : p=d*u+1 := by omega
  have eqq : q=d*v+1 := by omega
  exact ⟨u*v,by rw [eqp,eqq]; ring⟩

theorem rounded_sum_eq {p q L W d : ℕ} (pp : 0 < p) (qp : 0 < q)
    (dp : d∣p-1) (dq : d∣q-1) (lo : L≤p+q) (hi : p+q≤L+W) (short : W < d^2) :
    roundedSum (p*q) L d=p+q := by
  obtain ⟨t,eq⟩ := sum_residue pp qp dp dq
  have shift : p*q+1-L=(p+q-L)+d^2*t := by omega
  have index : p+q-L < d^2 := by omega
  unfold roundedSum
  rw [shift,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt index]
  omega

/-- If the first two hits are shared, the common spacing determines both local
orders. A sufficiently large spacing gives the exact sum by one rounding. -/
theorem two_shared {p q E a b L W : ℕ} (hp : p.Prime) (hq : q.Prime)
    (gp : (ZMod p)ˣ) (gq : (ZMod q)ˣ) (lt : a < b)
    (ap : gp^a=gp^E) (aq : gq^a=gq^E) (bp : gp^b=gp^E) (bq : gq^b=gq^E)
    (np : ∀ i, a < i → i < b → gp^i≠gp^E) (nq : ∀ i, a < i → i < b → gq^i≠gq^E)
    (lo : L≤p+q) (hi : p+q≤L+W) :
    orderOf gp=b-a ∧ orderOf gq=b-a ∧ (W < (b-a)^2 → roundedSum (p*q) L (b-a)=p+q) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  have op := consecutive_order gp lt ap bp np
  have oq := consecutive_order gq lt aq bq nq
  have dp : b-a∣p-1 := by rw [←op,←(Nat.prime_iff_card_units p).mp hp]; exact orderOf_dvd_card
  have dq : b-a∣q-1 := by rw [←oq,←(Nat.prime_iff_card_units q).mp hq]; exact orderOf_dvd_card
  exact ⟨op,oq,rounded_sum_eq hp.pos hq.pos dp dq lo hi⟩


/-- A unit-side witness is the same event as the prime-side product test. -/
theorem unit_hit_iff {p E : ℕ} (u : (ZMod p)ˣ) (g : ℤ) (value : (u:ZMod p)=(g:ZMod p))
    (I : Finset ℕ) : (∃ i∈I, u^i=u^E) ↔ localHit I g p E := by
  constructor
  · rintro ⟨i,hi,e⟩
    exact ⟨i,hi,by simpa only [Units.val_pow_eq_pow_val,value] using congrArg Units.val e⟩
  · rintro ⟨i,hi,e⟩
    exact ⟨i,hi,Units.ext (by simpa only [Units.val_pow_eq_pow_val,value] using e)⟩

/-- If the first shared hit has no local successor before the upper endpoint,
the true index is exactly that first hit. Only one side is needed here. -/
theorem singleton_index {G : Type*} [Group G] [Finite G] (g : G) {E W a j : ℕ}
    (first : a=E%orderOf g) (inside : j≤W) (trueHit : g^j=g^E)
    (noNext : W < a+orderOf g) : j=a := by
  have early : a≤j := first ▸ (prefix_threshold g E j).mp ⟨j,le_rfl,trueHit⟩
  have ah : g^a=g^E := by rw [first]; exact pow_eq_pow_iff_modEq.mpr (Nat.mod_mod ..)
  by_contra bad
  have := (suffix_threshold g ah (u:=W)).mp ⟨j,by omega,inside,trueHit⟩
  omega

/-- The true index hits at either prime for any local unit. -/
theorem true_index {p q L j : ℕ} (hp : p.Prime) (qp : 0 < q)
    (g : (ZMod p)ˣ) (loc : L+j=p+q) : g^j=g^(p*q+1-L) := by
  letI : Fact p.Prime := ⟨hp⟩
  have op : orderOf g∣p-1 := (Nat.prime_iff_card_units p).mp hp ▸ orderOf_dvd_card
  have id : p*q+1=p+q+(p-1)*(q-1) := by
    rw [show p=(p-1)+1 by have := hp.pos; omega,show q=(q-1)+1 by omega]
    simp only [Nat.add_sub_cancel]
    ring
  have expo : p*q+1-L=j+(p-1)*(q-1) := by omega
  have kill : g^((p-1)*(q-1))=1 := orderOf_dvd_iff_pow_eq_one.mp (dvd_mul_of_dvd_left op _)
  rw [expo,pow_add,kill,mul_one]

/-- A complete decision after the two first-occupied searches. The variable
a is the first hit on either side, and b is the first possible successor
once a is shared. Each differing pair of predicates gives a proper gcd by
the oracle. If neither test distinguishes the primes, only identical orders
with square at most W can remain unresolved. -/
theorem classify {p q L j W : ℕ} (hp : p.Prime) (hq : q.Prime)
    (gp : (ZMod p)ˣ) (gq : (ZMod q)ˣ) (loc : L+j=p+q) (inside : j≤W) :
    let E := p*q+1-L
    let dp := orderOf gp
    let dq := orderOf gq
    let a := min (E%dp) (E%dq)
    let b := a+min dp dq
    a≤W ∧ (
    (¬ ((∃ i≤a, gp^i=gp^E) ↔ (∃ i≤a, gq^i=gq^E))) ∨
    (W < b ∧ j=a) ∨
    (b≤W ∧ ¬ ((∃ i, a < i ∧ i≤b ∧ gp^i=gp^E) ↔ (∃ i, a < i ∧ i≤b ∧ gq^i=gq^E))) ∨
    (b≤W ∧ dp=dq ∧ b-a=dp ∧ (roundedSum (p*q) L (b-a)=p+q ∨ dp^2≤W))) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  let E := p*q+1-L
  let dp := orderOf gp
  let dq := orderOf gq
  let a := min (E%dp) (E%dq)
  let b := a+min dp dq
  have jp : gp^j=gp^E := true_index hp hq.pos gp loc
  have jq : gq^j=gq^E := by
    simpa only [E,Nat.mul_comm q p] using true_index hq hp.pos gq (loc.trans (Nat.add_comm p q))
  have room : a≤W := (min_le_left ..).trans ((prefix_threshold gp E W).mp ⟨j,inside,jp⟩)
  refine ⟨room,?_⟩
  by_cases diff : (∃ i≤a, gp^i=gp^E) ↔ (∃ i≤a, gq^i=gq^E)
  · have threshold := diff
    rw [prefix_threshold,prefix_threshold] at threshold
    change (E%dp≤a ↔ E%dq≤a) at threshold
    have same : E%dp=a ∧ E%dq=a := by
      rcases le_total (E%dp) (E%dq) with lr|rl
      · have eq : a=E%dp := min_eq_left lr
        exact ⟨eq.symm,le_antisymm (threshold.mp eq.ge) (min_le_right ..)⟩
      · have eq : a=E%dq := min_eq_right rl
        exact ⟨le_antisymm (threshold.mpr eq.ge) (min_le_left ..),eq.symm⟩
    have firstP : gp^a=gp^E := pow_eq_pow_iff_modEq.mpr (by rw [←same.1]; exact Nat.mod_mod ..)
    have firstQ : gq^a=gq^E := pow_eq_pow_iff_modEq.mpr (by rw [←same.2]; exact Nat.mod_mod ..)
    by_cases short : W < b
    · exact Or.inr (Or.inl ⟨short,singleton_index gp same.1.symm inside jp
        (short.trans_le (Nat.add_le_add_left (min_le_left dp dq) a))⟩)
    · have fits : b≤W := by omega
      by_cases gap : (∃ i, a < i ∧ i≤b ∧ gp^i=gp^E) ↔ (∃ i, a < i ∧ i≤b ∧ gq^i=gq^E)
      · rw [suffix_threshold gp firstP,suffix_threshold gq firstQ] at gap
        change (a+dp≤a+min dp dq ↔ a+dq≤a+min dp dq) at gap
        have orders : dp=dq := by omega
        have observed : b-a=dp := by dsimp [b]; rw [←orders,min_self]; omega
        refine Or.inr (Or.inr (Or.inr ⟨fits,orders,observed,?_⟩))
        by_cases small : dp^2≤W
        · exact Or.inr small
        · rw [observed]
          have pd : dp∣p-1 := (Nat.prime_iff_card_units p).mp hp ▸ orderOf_dvd_card
          have qd : dp∣q-1 := orders ▸ ((Nat.prime_iff_card_units q).mp hq ▸ orderOf_dvd_card)
          exact Or.inl (rounded_sum_eq (L:=L) (W:=W) hp.pos hq.pos pd qd
            (loc ▸ Nat.le_add_right L j) (loc ▸ Nat.add_le_add_left inside L) (lt_of_not_ge small))
      · exact Or.inr (Or.inr (Or.inl ⟨fits,gap⟩))
  · exact Or.inl diff

end PrimeFactors.GeometricOrderReadout
