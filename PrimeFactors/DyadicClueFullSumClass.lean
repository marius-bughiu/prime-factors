import PrimeFactors.DyadicFactorClueGain
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Data.ZMod.Units

/-! Whether a fixed factor suffix gives any higher-precision restrictions
on the sum, after its sharp single congruence is imposed. -/
namespace PrimeFactors.DyadicClueFullSumClass

/-- A candidate integer sum has a modular factorization with the chosen
first-factor suffix at each binary precision. -/
def Possible (k : ℕ) (N a s : ℤ) : Prop :=
  ∀ e : ℕ, ∃ x : ℤ, x ≡ a [ZMOD (2:ℤ)^k] ∧ x*(s-x) ≡ N [ZMOD (2:ℤ)^e]

private theorem cop_two {x : ℤ} (odd : Odd x) : IsCoprime (2 : ℤ) x := by
  obtain ⟨b,hb⟩ := odd
  exact ⟨-b,1,by linarith⟩

private theorem even_power {w : ℕ} (pos : 0<w) : Even ((2:ℤ)^w) :=
  (by decide : Even (2:ℤ)).pow_of_ne_zero pos.ne'

/-- A quadratic with odd linear coefficient and even quadratic coefficient
permutes residues modulo every power of two. -/
theorem quadratic_bijective {c d : ℤ} (co : Odd c) (de : Even d) (e : ℕ) :
    Function.Bijective (fun u : ZMod (2^e) => (c:ZMod _)*u+(d:ZMod _)*u^2) := by
  have inj : Function.Injective (fun u : ZMod (2^e) => (c:ZMod _)*u+(d:ZMod _)*u^2) := by
    rintro u v eq
    obtain ⟨i,rfl⟩ := ZMod.intCast_surjective u
    obtain ⟨j,rfl⟩ := ZMod.intCast_surjective v
    have modEq : c*i+d*i^2 ≡ c*j+d*j^2 [ZMOD (2:ℤ)^e] := by
      rw [show (2:ℤ)^e = ((2^e:ℕ):ℤ) by push_cast; rfl]
      apply (ZMod.intCast_eq_intCast_iff _ _ (2^e)).mp
      push_cast
      exact eq
    have div : (2:ℤ)^e ∣ (c+d*(i+j))*(j-i) := by
      convert Int.modEq_iff_dvd.mp modEq using 1
      ring
    have unit := cop_two (co.add_even (de.mul_right (i+j)))
    apply (ZMod.intCast_eq_intCast_iff _ _ (2^e)).mpr
    push_cast
    exact Int.modEq_iff_dvd.mpr (unit.pow_left.dvd_of_dvd_mul_left div)
  exact ⟨inj,Finite.surjective_of_injective inj⟩

private theorem lift {k t w : ℕ} {a N s : ℤ} (inside : k≤w) (wide : t<w)
    (slope : ∃ c : ℤ, Odd c ∧ s-2*a=2^t*c)
    (base : (2:ℤ)^(w+t)∣a*(s-a)-N) : Possible k N a s := by
  obtain ⟨c,co,cs⟩ := slope
  obtain ⟨h,hs⟩ := base
  have epos : 0<w-t := by omega
  have power : (2:ℤ)^(w-t)*2^t=2^w := by rw [←pow_add,Nat.sub_add_cancel wide.le]
  intro e
  obtain ⟨v,hv⟩ := (quadratic_bijective co (even_power epos).neg e).surjective ((-h:ℤ):ZMod (2^e))
  obtain ⟨u,rfl⟩ := ZMod.intCast_surjective v
  have rem : c*u+(-(2:ℤ)^(w-t))*u^2 ≡ -h [ZMOD (2:ℤ)^e] := by
    rw [show (2:ℤ)^e = ((2^e:ℕ):ℤ) by push_cast; rfl]
    apply (ZMod.intCast_eq_intCast_iff _ _ (2^e)).mp
    push_cast
    simpa using hv
  refine ⟨a+2^w*u, Int.modEq_iff_dvd.mpr ?_, Int.modEq_iff_dvd.mpr ?_⟩
  · rw [show a-(a+2^w*u)=2^w*(-u) by ring]
    exact (pow_dvd_pow (2:ℤ) inside).trans (dvd_mul_right _ _)
  · have eq : N-(a+2^w*u)*(s-(a+2^w*u)) =
        (2:ℤ)^(w+t)*(-h-(c*u+(-2^(w-t))*u^2)) := by
      rw [pow_add] at hs ⊢
      linear_combination -hs - (2:ℤ)^w*u*cs - (2:ℤ)^w*u^2*power
    exact eq ▸ dvd_mul_of_dvd_right (Int.modEq_iff_dvd.mp rem) _

private def width (k t : ℕ) := if t=k then k+1 else k

private theorem width_bounds {t k : ℕ} (pos : 0<k) (le : t≤k) :
    k≤width k t ∧ t<width k t ∧ 0<width k t := by
  unfold width
  split <;> omega

private theorem necessary {k t : ℕ} {a N s g : ℤ} (pos : 0<k) (le : t≤k)
    (ao : Odd a) (go : Odd g) (disc : a^2-N=2^t*g) (all : Possible k N a s) :
    (2:ℤ)^(width k t+t)∣a*(s-a)-N := by
  let E := width k t+t
  obtain ⟨x,cl,ok⟩ := all E
  obtain ⟨u,hu⟩ := Int.modEq_iff_dvd.mp cl.symm
  have xval : x=a+2^k*u := by linarith
  have xo : Odd x := xval ▸ ao.add_even ((even_power pos).mul_right u)
  have first : (2:ℤ)^E∣(x-a)*(a*x-N) := by
    by_cases same : t=k
    · subst t
      have term : Even (u*(g+a*u)) := by
        rcases Int.even_or_odd u with even|odd
        · exact even.mul_right _
        · exact (go.add_odd (ao.mul odd)).mul_left _
      obtain ⟨b,hb⟩ := term
      refine ⟨b,?_⟩
      simp only [E,width,if_true,pow_add,pow_one,xval]
      linear_combination (2:ℤ)^k*u*disc + ((2:ℤ)^k)^2*hb
    · have power : (2:ℤ)^k=2^t*2^(k-t) := by rw [←pow_add,Nat.add_sub_of_le le]
      refine ⟨u*(g+a*2^(k-t)*u),?_⟩
      simp only [E,width,if_neg same,pow_add,xval]
      linear_combination (2:ℤ)^k*u*disc + a*2^k*u^2*power
  have change := dvd_sub first (dvd_mul_of_dvd_left (Int.modEq_iff_dvd.mp ok) a)
  have ident : (x-a)*(a*x-N)-(N-x*(s-x))*a = x*(a*(s-a)-N) := by ring
  rw [ident] at change
  exact (cop_two xo).pow_left.dvd_of_dvd_mul_left change

/-- If a²−N has exact binary valuation t≤k, an integer sum has witnesses
at every power of two if and only if it obeys this single public congruence. -/
theorem full_class {k t : ℕ} {a N s g : ℤ} (pos : 0<k) (le : t≤k)
    (ao : Odd a) (go : Odd g) (disc : a^2-N=2^t*g) :
    Possible k N a s ↔ a*s ≡ a^2+N [ZMOD (2:ℤ)^((if t=k then k+1 else k)+t)] := by
  have eq : a^2+N-a*s= -(a*(s-a)-N) := by ring
  rw [Int.modEq_iff_dvd,eq,Int.dvd_neg]
  constructor
  · exact necessary pos le ao go disc
  · intro base
    obtain ⟨h,hs⟩ := base
    have wb := width_bounds pos le
    change a*(s-a)-N=2^(width k t+t)*h at hs
    rw [pow_add] at hs
    have transfer : a*(s-2*a)=2^t*(2^(width k t)*h-g) := by linear_combination hs-disc
    have cancel := (cop_two ao).pow_left.dvd_of_dvd_mul_left (Dvd.intro _ transfer.symm)
    obtain ⟨c,hc⟩ := cancel
    have coeff : a*c=2^(width k t)*h-g := by
      rw [hc] at transfer
      apply mul_left_cancel₀ (by positivity : (2:ℤ)^t≠0)
      linear_combination transfer
    have co : Odd c := by
      have val : Odd (a*c) := by
        rw [coeff,sub_eq_add_neg,add_comm]
        exact go.neg.add_even ((even_power wb.2.2).mul_right h)
      exact (Int.odd_mul.mp val).2
    exact lift wb.1 wb.2.1 ⟨c,co,hc⟩ ⟨h,by simpa [pow_add] using hs⟩

end PrimeFactors.DyadicClueFullSumClass
