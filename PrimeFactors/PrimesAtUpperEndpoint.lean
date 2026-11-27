import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic
import Mathlib.Tactic.ReduceModChar

/-! A two-divisor comparison for the last 255 integer positions below 2^1024.
Trial division up to 10^6 and Brent's cycle method produced proper divisors.
Their product below lets Lean check 251 exclusions in one finite gcd table.
The remaining two exclusions use Fermat's theorem to base two. -/
namespace PrimeFactors.PrimesAtUpperEndpoint

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

abbrev U : ℕ := 2^1024

private abbrev sieveProduct : ℕ :=
  [2,3,5,7,11,13,17,19,23,29,31,41,53,61,71,79,83,109,137,151,157,163,227,
   251,373,419,491,547,571,587,811,881,929,1231,1811,3671,12641,50131,87991,
   210961,7113851,52802329,8691583337,37993173619,1213562468941].prod

private theorem sieve : ∀ i : Fin 256, (U-i.val).Coprime sieveProduct →
    i.val=105 ∨ i.val=129 ∨ i.val=179 ∨ i.val=243 := by decide +kernel

private theorem fermat_two {q : ℕ} (prime : q.Prime) (large : 2<q) :
    (2 : ZMod q)^(q-1)=1 := by
  letI : Fact q.Prime := ⟨prime⟩
  apply ZMod.pow_card_sub_one_eq_one
  intro zero
  have dvd := (ZMod.natCast_zmod_eq_zero_iff_dvd 2 q).mp (by simpa using zero)
  exact (not_le_of_gt large) (Nat.le_of_dvd (by decide) dvd)

private theorem fermat_reject {q r : ℕ} (large : 2<q)
    (check : (2 : ZMod q)^(q-1)=(r : ZMod q)) (unequal : (r : ZMod q)≠1) : ¬q.Prime :=
  fun prime => unequal (check.symm.trans (fermat_two prime large))

private theorem exclusions {i : ℕ} (bad : i=129 ∨ i=243) : ¬(U-i).Prime := by
  rcases bad with rfl|rfl
  · apply fermat_reject (r:=5329144314051618668881536053874015287803430692014252532824816913462971091683925286327586775265574165821290747988084742228325724391712435442791533499676089399781469619952453118455585867498349749135773357781394256078216154192641647529523582205376928341806854003496688624304487211891124850539584118427273464983) (by decide +kernel) _ (by decide +kernel)
    change (2 : ZMod 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137087)^179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137086=_
    reduce_mod_char
  · apply fermat_reject (r:=76018693672950343132365648225131815305794401345244802013553946032420897906907488048728643369280026342031784140210880319480866645174824884439173320079467682599422750005998292782291058925472342280513776822304242242400174886078927626424385898066979275529109750847454622337290410305881623843483685174674395404469) (by decide +kernel) _ (by decide +kernel)
    change (2 : ZMod 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224136973)^179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224136972=_
    reduce_mod_char

/-- Any prime in the half-open interval [2^1024-255, 2^1024) equals one of
these two integers. The implication needs no external primality certificates. -/
theorem candidates {q : ℕ} (prime : q.Prime) (lo : U-255≤q) (hi : q<U) :
    q=U-105 ∨ q=U-179 := by
  let i : Fin 256 := ⟨U-q,by omega⟩
  have eq : U-i.val=q := by dsimp [i]; omega
  have large : sieveProduct<q := (by decide +kernel : sieveProduct<U-255).trans_le lo
  have cop := prime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide : 0<sieveProduct) large)
  rw [←eq] at cop
  rcases sieve i cop with a|a|a|a
  · exact Or.inl (eq.symm.trans (congrArg (U-·) a))
  · exact False.elim ((exclusions (Or.inl a)) (eq.symm ▸ prime))
  · exact Or.inr (eq.symm.trans (congrArg (U-·) a))
  · exact False.elim ((exclusions (Or.inr a)) (eq.symm ▸ prime))

/-- Test the only two possible divisors using at most two remainder operations.
Exclude the product itself so every returned divisor is proper. -/
def trial (n : ℕ) : Option ℕ :=
  if U-105<n ∧ U-105∣n then some (U-105)
  else if U-179<n ∧ U-179∣n then some (U-179)
  else none

/-- A composite with a proper prime divisor in the interval splits by the
two direct tests. The returned divisor and its exact quotient reconstruct n. -/
theorem split {n q : ℕ} (prime : q.Prime) (lo : U-255≤q) (hi : q<U)
    (proper : q<n) (divides : q∣n) :
    ∃ d, trial n=some d ∧ 1<d ∧ d<n ∧ 1<n/d ∧ d*(n/d)=n := by
  have finish {d : ℕ} (dd : d∣n) (dn : d<n) (dp : 1<d) (out : trial n=some d) :
      ∃ a, trial n=some a ∧ 1<a ∧ a<n ∧ 1<n/a ∧ a*(n/a)=n := by
    have eq := Nat.mul_div_cancel' dd
    have nontrivial : 1<n/d := by
      by_contra! bad
      have cap := Nat.mul_le_mul_left d bad
      rw [eq,Nat.mul_one] at cap
      exact (not_le_of_gt dn) cap
    exact ⟨d,out,dp,dn,nontrivial,eq⟩
  by_cases first : U-105<n ∧ U-105∣n
  · exact finish first.2 first.1 (by decide +kernel) (by simp only [trial,if_pos first])
  rcases candidates prime lo hi with eq|eq
  · exact False.elim (first (eq ▸ ⟨proper,divides⟩))
  · subst q
    have second := And.intro proper divides
    exact finish divides proper prime.one_lt (by simp only [trial,if_neg first,if_pos second])

end PrimeFactors.PrimesAtUpperEndpoint
