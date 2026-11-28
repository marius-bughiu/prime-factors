import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic

/-! The reciprocal primes in any invertible progression have divergent sum.
For a fixed positive integer n, the progression 1 modulo 8n also guarantees
that n is a nonzero square at every prime in it. -/

namespace PrimeFactors.SplittingGuessPrimes

open Finset Real Filter ArithmeticFunction ArithmeticFunction.vonMangoldt
open scoped Topology

/-- The supplementary laws and quadratic reciprocity enter through the Jacobi
symbol's periodicity in its denominator modulo 4n. -/
theorem square_of_one {n p : ℕ} (hn : 0<n) (hp : p.Prime) (ap : p % (8*n) = 1) :
    ¬p∣n ∧ IsSquare (n : ZMod p) := by
  have gt : 1 < 8*n := by omega
  have pbig : 8*n ≤ p := by
    by_contra! small
    rw [Nat.mod_eq_of_lt small] at ap
    exact hp.ne_one ap
  have odd : Odd p := hp.odd_of_ne_two (by omega)
  have rem : p % (4*n) = 1 := by
    have dv : 4*n ∣ 8*n := ⟨2,by ring⟩
    rw [←Nat.mod_mod_of_dvd p dv,ap,Nat.mod_eq_of_lt (by omega)]
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨fun h => (not_le_of_gt (show n<p by omega)) (Nat.le_of_dvd hn h),?_⟩
  have eq := jacobiSym.mod_right' n odd
  rw [rem,jacobiSym.one_right] at eq
  exact_mod_cast ZMod.isSquare_of_jacobiSym_eq_one (p:=p) eq

noncomputable def reciprocal {q : ℕ} (a : ZMod q) (k : ℕ) : ℝ := by
  classical exact if k.Prime ∧ (k : ZMod q)=a then 1/(k:ℝ) else 0

private noncomputable def term {q : ℕ} (a : ZMod q) (t : ℝ) (k : ℕ) :=
  t * (residueClass a k / (k:ℝ)^(1+t))

private theorem term_bound {q : ℕ} (a : ZMod q) {t : ℝ} (ht : 0<t) (ht' : t≤1) (k : ℕ) :
    ‖term a t k‖ ≤ reciprocal a k + (if k.Prime then 0 else residueClass a k)/(k:ℝ) := by
  classical
  unfold term
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg ht.le (div_nonneg (residueClass_nonneg _ _) (rpow_nonneg (Nat.cast_nonneg _) _)))]
  by_cases pk : k.Prime
  · simp only [term,reciprocal,pk, true_and,if_true,zero_div,add_zero]
    by_cases h : (k:ZMod q)=a
    · simp only [h,if_true,residueClass,Set.indicator_of_mem (show k∈{m:ℕ | (m:ZMod q)=a} from h),
        vonMangoldt_apply_prime pk]
      have kp : 0 < (k:ℝ) := by exact_mod_cast pk.pos
      rw [rpow_add kp, rpow_one, ←mul_div_assoc]
      rw [div_le_div_iff₀ (mul_pos kp (rpow_pos_of_pos kp _)) kp]
      have bound : t*Real.log k ≤ (k:ℝ)^t := by
        rw [rpow_def_of_pos kp]
        linarith only [Real.add_one_le_exp (Real.log k*t),mul_comm t (Real.log k)]
      nlinarith only [mul_le_mul_of_nonneg_right bound kp.le]
    · simp [h,residueClass]
  · simp only [term,reciprocal,pk,false_and,if_false,zero_add]
    rcases k.eq_zero_or_pos with rfl|kp
    · simp
    have p : 0 < (k:ℝ) := by exact_mod_cast kp
    have one : 1 ≤ (k:ℝ) := by exact_mod_cast kp
    have den : (k:ℝ) ≤ (k:ℝ)^(1+t) := by
      calc
        _ = (k:ℝ)^(1:ℝ) := (rpow_one _).symm
        _ ≤ _ := rpow_le_rpow_of_exponent_le one (by linarith)
    calc
      t*(residueClass a k / (k:ℝ)^(1+t)) ≤ 1*(residueClass a k / (k:ℝ)^(1+t)) :=
        mul_le_mul_of_nonneg_right ht' (div_nonneg (residueClass_nonneg _ _) (rpow_nonneg p.le _))
      _ ≤ _ := by simpa only [one_mul] using
        div_le_div_of_nonneg_left (residueClass_nonneg a k) p den

private theorem term_tends {q : ℕ} (a : ZMod q) (k : ℕ) :
    Tendsto (fun t : ℝ => term a t k) (𝓝[>] 0) (𝓝 0) := by
  rcases k.eq_zero_or_pos with rfl|kp
  · simp [term,residueClass_apply_zero]
  have nz : (k:ℝ)≠0 := by exact_mod_cast kp.ne'
  have cont : ContinuousAt (fun t : ℝ => residueClass a k/(k:ℝ)^(1+t)) 0 := by
    fun_prop (disch := first | positivity | assumption)
  have h := (continuousAt_id.mul cont).tendsto
  simpa only [id_eq,zero_mul,term] using h.mono_left nhdsWithin_le_nhds

/-- Dirichlet's reciprocal-prime divergence for any invertible progression.
Mathlib supplies the pole with positive residue of its von Mangoldt series.
If the reciprocal-prime series converged, Tannery's theorem would force its
residue to vanish. -/
theorem not_summable_progression {q : ℕ} [NeZero q] {a : ZMod q} (unit : IsUnit a) :
    ¬Summable (reciprocal a) := by
  classical
  intro converges
  have dom := converges.add (summable_residueClass_non_primes_div a)
  have near : ∀ᶠ t : ℝ in 𝓝[>] 0, 0<t ∧ t≤1 :=
    (show ∀ᶠ t : ℝ in 𝓝[>] 0, 0<t from self_mem_nhdsWithin).and
      (eventually_lt_nhds (show (0:ℝ)<1 by norm_num) |>.filter_mono nhdsWithin_le_nhds |>.mono (fun _ h => h.le))
  have lim := tendsto_tsum_of_dominated_convergence dom (term_tends a)
    (near.mono (fun t ht k => term_bound a ht.1 ht.2 k))
  have zero : Tendsto (fun t => ∑' k, term a t k) (𝓝[>] 0) (𝓝 0) := by simpa using lim
  obtain ⟨C,hC⟩ := LSeries_residueClass_lower_bound unit
  have hl : ∀ᶠ t : ℝ in 𝓝[>] 0, (q.totient:ℝ)⁻¹ ≤ (∑' k, term a t k) + t*C := by
    filter_upwards [near] with t ht
    have pole := hC (x:=1+t) (show 1+t ∈ Set.Ioc (1:ℝ) 2 from ⟨by linarith [ht.1],by linarith [ht.2]⟩)
    rw [show (1:ℝ)+t-1=t by ring] at pole
    simp only [term,tsum_mul_left]
    have bound := (div_le_iff₀ ht.1).mp (show (q.totient:ℝ)⁻¹/t ≤ (∑' k, residueClass a k/(k:ℝ)^(1+t))+C by linarith only [pole])
    linarith only [bound]
  have zc : Tendsto (fun t : ℝ => t*C) (𝓝[>] 0) (𝓝 (0*C)) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).mul_const C
  have bad := ge_of_tendsto (zero.add zc) hl
  have positive : 0 < (q.totient:ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q))
  linarith

/-- Arbitrarily large finite reciprocal sums, after omitting any prescribed
initial range, on square-unit primes for the fixed positive integer n. -/
theorem large_tail {n : ℕ} (hn : 0<n) (cut : ℕ) (target : ℝ) :
    ∃ S : Finset ℕ, (∀ p∈S, p.Prime ∧ cut≤p ∧ ¬p∣n ∧ IsSquare (n:ZMod p)) ∧
      target < ∑ p∈S, (1:ℝ)/p := by
  classical
  letI : NeZero (8*n) := ⟨by omega⟩
  let a : ZMod (8*n) := 1
  let f := reciprocal a
  let b := ∑ p∈range cut, (1:ℝ)/p
  have ex : ∃ k : ℕ, target+b < ∑ p∈range k, f p := by
    by_contra! bounded
    apply not_summable_progression (q:=8*n) (a:=a) isUnit_one
    exact summable_of_sum_range_le (fun i => by unfold reciprocal; split_ifs <;> positivity) bounded
  obtain ⟨k,big⟩ := ex
  let U := (range k).filter fun p : ℕ => p.Prime ∧ (p:ZMod (8*n))=a
  let V := U ∩ range cut
  have eq : (∑ p∈range k, f p) = ∑ p∈U, (1:ℝ)/p := by dsimp only [U]; rw [sum_filter]; rfl
  rw [eq] at big
  have split := sum_sdiff (f:=fun p : ℕ => (1:ℝ)/p) (inter_subset_left : V⊆U)
  have small : (∑ p∈V, (1:ℝ)/p) ≤ b := sum_le_sum_of_subset_of_nonneg
    (inter_subset_right : V ⊆ range cut) (fun _ _ _ => by positivity)
  refine ⟨U \ V,?_,by linarith only [big,split,small]⟩
  intro p good
  obtain ⟨pu,pv⟩ := mem_sdiff.mp good
  obtain ⟨prime,cls⟩ := (mem_filter.mp pu).2
  have rem := (ZMod.natCast_eq_natCast_iff' p 1 (8*n)).mp (by simpa only [Nat.cast_one] using cls)
  rw [Nat.mod_eq_of_lt (by omega : 1<8*n)] at rem
  exact ⟨prime,le_of_not_gt (fun lt => pv (mem_inter.mpr ⟨pu,mem_range.mpr lt⟩)),
    square_of_one hn prime rem⟩

end PrimeFactors.SplittingGuessPrimes
