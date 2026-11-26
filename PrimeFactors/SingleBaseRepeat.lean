import PrimeFactors.FrobeniusFixedCounts
import PrimeFactors.SumSignatureProbability

/-! A repeat has one common gap at both primes. Count the individual units
for a given gap exactly, then take a finite union over the positive gaps. -/

namespace PrimeFactors.SingleBaseRepeat
open Finset

/-- The units that admit at least one positive exponent gap up to W. -/
noncomputable def repeated (n W : ℕ) [NeZero n] : Finset (ZMod n)ˣ :=
  (Icc 1 W).biUnion (fun e => univ.filter fun g => g^e=1)

@[simp] theorem mem_repeated {n W : ℕ} [NeZero n] {g : (ZMod n)ˣ} :
    g∈repeated n W ↔ ∃ e ∈ Icc 1 W, g^e=1 := by
  simp [repeated]

theorem unit_count {p q : ℕ} [NeZero (p*q)] (hp : p.Prime) (hq : q.Prime) (ne : p≠q) :
    Fintype.card (ZMod (p*q))ˣ=(p-1)*(q-1) := by
  rw [ZMod.card_units_eq_totient,Nat.totient_mul ((Nat.coprime_primes hp hq).mpr ne),
    Nat.totient_prime hp,Nat.totient_prime hq]

/-- No independence across different exponents is used. For one specified gap,
the two cyclic power kernels combine exactly under the unit CRT isomorphism. -/
theorem gap_count {p q : ℕ} [NeZero (p*q)] (hp : p.Prime) (hq : q.Prime) (ne : p≠q)
    (e : ℕ) :
    (univ.filter fun x : (ZMod (p*q))ˣ => x^e=1).card=(e.gcd (p-1))*(e.gcd (q-1)) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  let crt := (Units.mapEquiv (ZMod.chineseRemainder ((Nat.coprime_primes hp hq).mpr ne)).toMulEquiv).trans MulEquiv.prodUnits
  let P := univ.filter (fun x : (ZMod p)ˣ => x^e=1)
  let Q := univ.filter (fun x : (ZMod q)ˣ => x^e=1)
  let S := univ.filter (fun x : (ZMod (p*q))ˣ => x^e=1)
  have eqn : S.image crt = P ×ˢ Q := by
    ext z
    rw [mem_image,mem_product]
    constructor
    · rintro ⟨x,hx,rfl⟩
      have val : x^e=1 := (mem_filter.mp hx).2
      have same : crt (x^e)=crt 1 := congrArg crt val
      rw [map_pow,map_one] at same
      exact ⟨mem_filter.mpr ⟨mem_univ _,congrArg Prod.fst same⟩,
        mem_filter.mpr ⟨mem_univ _,congrArg Prod.snd same⟩⟩
    · rintro ⟨hx,hy⟩
      refine ⟨crt.symm z,mem_filter.mpr ⟨mem_univ _,crt.injective ?_⟩,crt.apply_symm_apply _⟩
      rw [map_pow,map_one,crt.apply_symm_apply]
      exact Prod.ext (mem_filter.mp hx).2 (mem_filter.mp hy).2
  have counts := congrArg card eqn
  rw [card_image_of_injective _ crt.injective,card_product] at counts
  have pc : P.card=e.gcd (p-1) := by
    dsimp only [P]
    rw [FrobeniusFixedCounts.cyclic_count,(Nat.prime_iff_card_units p).mp hp]
  have qc : Q.card=e.gcd (q-1) := by
    dsimp only [Q]
    rw [FrobeniusFixedCounts.cyclic_count,(Nat.prime_iff_card_units q).mp hq]
  exact counts.trans (congrArg₂ (·*·) pc qc)

theorem elements_bound {p q : ℕ} [NeZero (p*q)] (hp : p.Prime) (hq : q.Prime)
    (ne : p≠q) (W : ℕ) :
    (repeated (p*q) W).card ≤ ∑ e ∈ Icc 1 W, (e.gcd (p-1))*(e.gcd (q-1)) := by
  unfold repeated
  exact card_biUnion_le.trans (le_of_eq (sum_congr rfl fun e _ => gap_count hp hq ne e))

/-- The same count in the tuple convention of the public signature decoder. -/
theorem singleton_count (n W : ℕ) [NeZero n] :
    (SumSignatureProbability.short (ZMod n)ˣ 1 W).card=(repeated n W).card := by
  classical
  let S := SumSignatureProbability.short (ZMod n)ˣ 1 W
  have eqn : S.image (fun u => u 0)=repeated n W := by
    ext x
    rw [mem_image,mem_repeated]
    constructor
    · rintro ⟨u,hu,rfl⟩
      obtain ⟨e,he,good⟩ := SumSignatureProbability.mem_short.mp hu
      exact ⟨e,he,good 0⟩
    · rintro ⟨e,he,hx⟩
      exact ⟨fun _ => x,SumSignatureProbability.mem_short.mpr ⟨e,he,fun _ => hx⟩,rfl⟩
  have inj : Function.Injective (fun u : Fin 1→(ZMod n)ˣ => u 0) := by
    intro u v same
    funext i
    simpa only [Subsingleton.elim i 0] using same
  rw [←eqn,card_image_of_injective _ inj]

theorem sum_gcd {p q : ℕ} [NeZero (p*q)] (hp : p.Prime) (hq : q.Prime) (ne : p≠q) (W : ℕ) :
    (SumSignatureProbability.short (ZMod (p*q))ˣ 1 W).card ≤
      ∑ e ∈ Icc 1 W, (e.gcd (p-1))*(e.gcd (q-1)) := by
  rw [singleton_count]
  exact elements_bound hp hq ne W

end PrimeFactors.SingleBaseRepeat
