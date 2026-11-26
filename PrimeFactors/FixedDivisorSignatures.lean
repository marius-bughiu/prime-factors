import PrimeFactors.ChebyshevPrimeSample
import Mathlib.Data.Nat.Bitwise

/-! Separating two primes with gcds against constants fixed before the input.
The integer products in the construction can be very large. -/
namespace PrimeFactors.FixedDivisorSignatures

open Finset

/-- Product of the members of the public catalogue bearing one chosen bit. -/
noncomputable def column (S : Finset ℕ) (bit : ℕ → Bool) : ℕ :=
  ∏ x ∈ S.filter (fun x => bit x = true), x

theorem column_dvd {S : Finset ℕ} {p : ℕ} (pp : p.Prime) (mem : p∈S)
    (unique : ∀ x∈S, p ∣ x → x=p) (bit : ℕ → Bool) :
    p ∣ column S bit ↔ bit p=true := by
  rw [column,(Nat.prime_iff.mp pp).dvd_finset_prod_iff]
  constructor
  · rintro ⟨x,hx,dvd⟩
    obtain ⟨inside,set⟩ := mem_filter.mp hx
    rwa [← unique x inside dvd]
  · exact fun set => ⟨p,mem_filter.mpr ⟨mem,set⟩,dvd_refl _⟩

/-- With a single prime in the column, the gcd is that entire prime. -/
theorem separates {p q c : ℕ} (pp : p.Prime) (qp : q.Prime)
    (diff : ¬(p∣c ↔ q∣c)) : c.gcd (p*q)=p ∨ c.gcd (p*q)=q := by
  rw [Nat.gcd_comm]
  by_cases left : p∣c
  · have right : ¬q∣c := fun h => diff ⟨fun _ => h,fun _ => left⟩
    left
    rw [Nat.mul_comm]
    exact Nat.gcd_mul_of_coprime_of_dvd (qp.coprime_iff_not_dvd.mpr right) left
  · have right : q∣c := by by_contra h; exact diff (iff_of_false left h)
    exact Or.inr (Nat.gcd_mul_of_coprime_of_dvd (pp.coprime_iff_not_dvd.mpr left) right)

private theorem same_gcd {p q c : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (equal : p∣c ↔ q∣c) : c.gcd (p*q)=1 ∨ c.gcd (p*q)=p*q := by
  by_cases h : p∣c
  · exact Or.inr (Nat.gcd_eq_right ((Nat.coprime_primes pp qp).mpr ne |>.mul_dvd_of_dvd_of_dvd h (equal.mp h)))
  · rw [Nat.gcd_comm]
    exact Or.inl ((pp.coprime_iff_not_dvd.mpr h).mul (qp.coprime_iff_not_dvd.mpr (mt equal.mpr h)))

/-- The jth constant encodes a bit of the index among the odd candidates.
No primality decisions enter this catalogue. -/
noncomputable def intervalColumn (B j : ℕ) : ℕ :=
  column (Ico B (2*B)) (fun x => ((x-B)/2).testBit j)

theorem interval_bit {B p : ℕ} (pp : p.Prime) (lo : B≤p) (hi : p<2*B) (j : ℕ) :
    p ∣ intervalColumn B j ↔ ((p-B)/2).testBit j = true := by
  apply column_dvd pp (mem_Ico.mpr ⟨lo,hi⟩)
  intro x mem dvd
  obtain ⟨xl,xh⟩ := mem_Ico.mp mem
  exact Nat.eq_of_dvd_of_lt_two_mul (by omega) dvd (by omega)

theorem bit_distinguishes {a b k : ℕ} (ne : a≠b) (ha : a<2^k) (hb : b<2^k) :
    ∃ j : Fin k, a.testBit j ≠ b.testBit j := by
  by_contra! same
  apply ne
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases h : j<k
  · exact same ⟨j,h⟩
  · have order := Nat.pow_le_pow_right (by decide : 0<2) (by omega : k≤j)
    rw [Nat.testBit_lt_two_pow (ha.trans_le order),Nat.testBit_lt_two_pow (hb.trans_le order)]

/-- One of k fixed constants returns exactly p or q for every pair of distinct
odd primes between B and 2B, when B≤2^(k+1). -/
theorem interval_split {B k p q : ℕ} (scale : B≤2^(k+1))
    (pp : p.Prime) (qp : q.Prime) (ne : p≠q) (oddP : p%2=1) (oddQ : q%2=1)
    (pl : B≤p) (pu : p<2*B) (ql : B≤q) (qu : q<2*B) :
    ∃ j : Fin k, (intervalColumn B j).gcd (p*q)=p ∨ (intervalColumn B j).gcd (p*q)=q := by
  rw [pow_succ] at scale
  obtain ⟨j,diff⟩ := bit_distinguishes (k:=k) (a:=(p-B)/2) (b:=(q-B)/2)
    (by omega) (by omega) (by omega)
  refine ⟨j,separates pp qp (fun equal => diff ?_)⟩
  rw [interval_bit pp pl pu j,interval_bit qp ql qu j] at equal
  simpa using equal

/-- A catalogue of primes can implement any prescribed bit signature. -/
theorem prescribe (S : Finset ℕ) (pr : ∀ p∈S, Nat.Prime p) {k : ℕ}
    (bits : ℕ → Fin k → Bool) (p : ℕ) (hp : p∈S) (j : Fin k) :
    p ∣ column S (fun x => bits x j) ↔ bits p j=true := by
  apply column_dvd (pr p hp) hp
  intro x hx dvd
  exact ((Nat.dvd_prime (pr x hx)).mp dvd).resolve_left (pr p hp).ne_one |>.symm

/-- Every pair in the catalogue must be separable by at least one fixed gcd. -/
def covers {k : ℕ} (C : Fin k → ℕ) (S : Finset ℕ) : Prop :=
  ∀ p∈S, ∀ q∈S, p≠q → ∃ j, 1<(C j).gcd (p*q) ∧ (C j).gcd (p*q)<p*q

/-- Necessity includes arbitrary constants, including zero. If two primes have
the same divisibility signature every gcd returns 1 or the whole product. -/
theorem clique_bound {k : ℕ} {C : Fin k → ℕ} {S : Finset ℕ} (pr : ∀ p∈S, Nat.Prime p)
    (coverage : covers C S) : S.card ≤ 2^k := by
  let sig (p : S) (j : Fin k) := decide (p.val ∣ C j)
  have inj : Function.Injective sig := by
    intro p q equal
    apply Subtype.ext
    by_contra ne
    obtain ⟨j,lo,hi⟩ := coverage p p.property q q.property ne
    have bits := congrFun equal j
    have agree : p.val ∣ C j ↔ q.val ∣ C j := by simpa only [sig,decide_eq_decide] using bits
    rcases same_gcd (pr _ p.property) (pr _ q.property) ne agree with h | h <;> omega
  simpa using Fintype.card_le_of_injective sig inj

/-- This information bound is sharp on a complete catalogue of primes.
Assign the primes distinct binary words and multiply the primes in each bit column. -/
theorem clique_iff {S : Finset ℕ} (pr : ∀ p∈S, Nat.Prime p) (k : ℕ) :
    (∃ C : Fin k → ℕ, covers C S) ↔ S.card≤2^k := by
  classical
  constructor
  · rintro ⟨C,cover⟩
    exact clique_bound pr cover
  · intro room
    have limit : Fintype.card S ≤ Fintype.card (Fin k → Bool) := by simpa using room
    let code : S ↪ (Fin k → Bool) := (Fintype.equivFin S).toEmbedding.trans
      ((Fin.castLEEmb limit).trans (Fintype.equivFin (Fin k → Bool)).symm.toEmbedding)
    let bit (p : ℕ) : Fin k → Bool := if mem : p∈S then code ⟨p,mem⟩ else fun _ => false
    refine ⟨fun j => column S (fun p => bit p j), ?_⟩
    intro p hp q hq ne
    have diff : ∃ j, bit p j≠bit q j := by
      by_contra! same
      apply ne
      have he : code ⟨p,hp⟩ = code ⟨q,hq⟩ := by
        simpa only [bit,dif_pos hp,dif_pos hq] using funext same
      exact congrArg Subtype.val (code.injective he)
    obtain ⟨j,diff⟩ := diff
    have divs : ¬(p∣column S (fun a => bit a j) ↔ q∣column S (fun a => bit a j)) := by
      rw [prescribe S pr bit p hp j,prescribe S pr bit q hq j]
      simpa using diff
    refine ⟨j,?_⟩
    rcases separates (pr p hp) (pr q hq) divs with eq|eq <;> rw [eq]
    · exact ⟨(pr p hp).one_lt, lt_mul_of_one_lt_right (pr p hp).pos (pr q hq).one_lt⟩
    · exact ⟨(pr q hq).one_lt, lt_mul_of_one_lt_left (pr q hq).pos (pr p hp).one_lt⟩

/-- All but at most one of the clique primes divide the combined positive constants. -/
theorem clique_height {k B : ℕ} {C : Fin k → ℕ} {S : Finset ℕ}
    (bp : 0<B) (lo : ∀ p∈S, B≤p) (pr : ∀ p∈S, Nat.Prime p)
    (positive : ∀ j, 0<C j) (coverage : covers C S) :
    B^(S.card-1) ≤ ∏ j, C j := by
  classical
  let T := ∏ j, C j
  let seen := S.filter (fun p => p∣T)
  let absent := S.filter (fun p => ¬p∣T)
  have one : absent.card ≤ 1 := by
    apply card_le_one.mpr
    intro p hp q hq
    obtain ⟨pm,np⟩ := mem_filter.mp hp
    obtain ⟨qm,nq⟩ := mem_filter.mp hq
    by_contra ne
    obtain ⟨j,lower,upper⟩ := coverage p pm q qm ne
    have col : C j ∣ T := dvd_prod_of_mem C (mem_univ j)
    have both : p ∣ C j ↔ q ∣ C j := iff_of_false (fun h => np (h.trans col)) (fun h => nq (h.trans col))
    rcases same_gcd (pr _ pm) (pr _ qm) ne both with eq|eq <;> omega
  have total : seen.card+absent.card=S.card := filter_card_add_filter_neg_card_eq_card _
  have div : ∏ p ∈ seen, p ∣ T := Finset.prod_primes_dvd T
    (fun p hp => Nat.prime_iff.mp (pr p (mem_filter.mp hp).1))
    (fun _ hp => (mem_filter.mp hp).2)
  calc
    _ ≤ B^seen.card := Nat.pow_le_pow_right bp (by omega)
    _ ≤ ∏ p ∈ seen, p := by
      apply pow_card_le_prod
      intro p hp
      exact lo p (mem_filter.mp hp).1
    _ ≤ T := Nat.le_of_dvd (prod_pos (fun j _ => positive j)) div

open MixedPrefixSample
set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
attribute [local irreducible] X primes upperPrimes eligible ordered sample

theorem full_size_upper {p q : ℕ} (mem : (p,q)∈eligible) :
    ∃ j : Fin 1022, (intervalColumn X j).gcd (p*q)=p ∨ (intervalColumn X j).gcd (p*q)=q := by
  rw [eligible,sample] at mem
  obtain ⟨ord,_⟩ := mem_filter.mp mem
  obtain ⟨pm,qm,ne,_,_⟩ := (mem_ordered (E:=fun _ => True) (z:=(p,q))).mp ord
  rw [primes] at pm qm
  obtain ⟨pi,pp⟩ := mem_filter.mp pm
  obtain ⟨qi,qp⟩ := mem_filter.mp qm
  obtain ⟨pl,pu⟩ := mem_Ico.mp pi
  obtain ⟨ql,qu⟩ := mem_Ico.mp qi
  have b : 2<X := by rw [X]; decide +kernel
  exact interval_split (by rw [X]) pp qp ne
    (pp.eq_two_or_odd.resolve_left (by omega)) (qp.eq_two_or_odd.resolve_left (by omega)) pl pu ql qu

private theorem upper_pair {p q : ℕ} (pm : p∈upperPrimes) (qm : q∈upperPrimes) (ord : p<q) :
    (p,q)∈eligible := by
  rw [upperPrimes] at pm qm
  obtain ⟨ps,pl⟩ := mem_filter.mp pm
  obtain ⟨qs,ql⟩ := mem_filter.mp qm
  have bound := Nat.mul_le_mul pl ql
  rw [eligible,sample]
  exact mem_filter.mpr ⟨mem_ordered.mpr ⟨ps,qs,ord.ne,by nlinarith only [bound,Nat.zero_le (X*X)],trivial⟩,ord⟩

private theorem upper_prime (p : ℕ) (hp : p∈upperPrimes) : p.Prime := by
  rw [upperPrimes] at hp
  have inside := (mem_filter.mp hp).1
  rw [primes] at inside
  exact (mem_filter.mp inside).2

private theorem upper_covered {k : ℕ} {C : Fin k → ℕ}
    (all : ∀ z∈eligible, ∃ j, 1<(C j).gcd (z.1*z.2) ∧ (C j).gcd (z.1*z.2)<z.1*z.2) :
    covers C upperPrimes := by
  intro p hp q hq ne
  rcases lt_or_gt_of_ne ne with ord|ord
  · exact all (p,q) (upper_pair hp hq ord)
  · simpa only [Nat.mul_comm q p] using all (q,p) (upper_pair hq hp ord)

/-- A uniform solver using only gcds with its list of constants needs at least
1012 distinct coordinates to split every eligible product at target width. -/
theorem full_size_lower {k : ℕ} {C : Fin k → ℕ}
    (all : ∀ z∈eligible, ∃ j, 1<(C j).gcd (z.1*z.2) ∧ (C j).gcd (z.1*z.2)<z.1*z.2) :
    1012≤k := by
  have bound := clique_bound upper_prime (upper_covered all)
  have large := ChebyshevPrimeSample.prime_count
  change 11*X < 35500*(upperPrimes.card-1) at large
  by_contra! small
  have powbound := Nat.pow_le_pow_right (by decide : 0<2) (by omega : k≤1011)
  have scale : 35500*(2^1011:ℕ) < 11*X := by rw [X]; decide +kernel
  omega

private theorem bit_budget {k b : ℕ} {S : Finset ℕ} {C bits : Fin k → ℕ}
    (lo : ∀ p∈S, 2^b≤p) (pr : ∀ p∈S, Nat.Prime p)
    (positive : ∀ j, 0<C j) (size : ∀ j, C j≤2^(bits j)) (coverage : covers C S) :
    b*(S.card-1) ≤ ∑ j, bits j := by
  have lower := clique_height (pow_pos (by decide : 0<2) _) lo pr positive coverage
  have top : ∏ j, C j ≤ 2^(∑ j, bits j) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact prod_le_prod' (fun j _ => size j)
  rw [←pow_mul] at lower
  exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (lower.trans top)

private theorem mass_lower : 2^1021 < 1023*(upperPrimes.card-1) := by
  have scale : 35500*(2^1021:ℕ) < 1023*(11*X) := by rw [X]; decide +kernel
  have large := ChebyshevPrimeSample.prime_count
  change 11*X < 35500*(upperPrimes.card-1) at large
  apply Nat.lt_of_mul_lt_mul_left (a:=35500)
  calc
    _ < 1023*(11*X) := scale
    _ ≤ 1023*(35500*(upperPrimes.card-1)) := Nat.mul_le_mul_left _ large.le
    _ = _ := by ac_rfl

/-- Total storage if the positive constants are written in binary. Zeros are
uninformative gcd coordinates on a semiprime and can be replaced by ones. -/
theorem full_size_storage {k : ℕ} {C bits : Fin k → ℕ} (positive : ∀ j, 0<C j)
    (size : ∀ j, C j≤2^(bits j))
    (all : ∀ z∈eligible, ∃ j, 1<(C j).gcd (z.1*z.2) ∧ (C j).gcd (z.1*z.2)<z.1*z.2) :
    2^1021 < ∑ j, bits j := by
  have lo (p : ℕ) (hp : p∈upperPrimes) : X≤p := by
    rw [upperPrimes] at hp
    have inside := (mem_filter.mp hp).1
    rw [primes] at inside
    exact (mem_Ico.mp (mem_filter.mp inside).1).1
  exact mass_lower.trans_le (bit_budget (b:=1023) (fun p hp => by rw [←X]; exact lo p hp)
    upper_prime positive size (upper_covered all))

/-- The same bound permits zeros, whose gcd with every input is the input itself. -/
theorem full_size_storage_any {k : ℕ} {C bits : Fin k → ℕ} (size : ∀ j, C j≤2^(bits j))
    (all : ∀ z∈eligible, ∃ j, 1<(C j).gcd (z.1*z.2) ∧ (C j).gcd (z.1*z.2)<z.1*z.2) :
    2^1021 < ∑ j, bits j := by
  apply full_size_storage (C:=fun j => max 1 (C j))
    (fun j => lt_of_lt_of_le (by decide : 0<1) (le_max_left 1 (C j)))
    (fun j => max_le (Nat.one_le_pow _ _ (by decide)) (size j))
  intro z hz
  obtain ⟨j,lo,hi⟩ := all z hz
  have nonzero : C j≠0 := by rintro zero; simp [zero] at hi
  exact ⟨j,by rwa [max_eq_right (Nat.pos_of_ne_zero nonzero)],
    by rwa [max_eq_right (Nat.pos_of_ne_zero nonzero)]⟩

/-- The second bit column of [16,32) gives a factor with no prime catalogue. -/
theorem small : (intervalColumn 16 1).gcd 437=23 ∧ Nat.Prime 19 ∧ Nat.Prime 23 ∧ 19*23=437 := by
  decide +kernel

end PrimeFactors.FixedDivisorSignatures
