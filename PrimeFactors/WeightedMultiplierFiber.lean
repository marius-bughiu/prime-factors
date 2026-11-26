import PrimeFactors.WeightedMultiplierPopulation
import PrimeFactors.WeightedMultiplierPoints

/-! A fixed pair of weighted labels injects every matching public product
into a bounded set of Pell solutions. The two multipliers may coincide.
A match giving the entire input as its difference gcd is excluded. -/

namespace PrimeFactors.WeightedMultiplierFiber
open Finset WeightedMultiplierPopulation
set_option exponentiation.threshold 4096
set_option maxRecDepth 4096

structure Hit (r s A B n J : ℕ) : Prop where
  top : Real.sqrt n ≤ 2*(2:ℝ)^1023
  first : Label r J A (Real.sqrt n)
  second : Label s J B (Real.sqrt n)
  witness : ∃ d e z : ℕ, A^2=d+4*r*n ∧ B^2=e+4*s*n ∧ z^2=d*e ∧ (A*B-z).gcd n<n

theorem Hit.nonsingular {r s A B n J : ℕ} (h : Hit r s A B n J) :
    0<difference (r,s) A B := by
  obtain ⟨d,e,z,ha,hb,hz,proper⟩ := h.witness
  apply Nat.pos_of_ne_zero
  intro zero
  have eq := Int.natAbs_eq_zero.mp zero
  change (s:ℤ)*(A:ℤ)^2-(r:ℤ)*(B:ℤ)^2=0 at eq
  have same : s*A^2=r*B^2 := by exact_mod_cast sub_eq_zero.mp eq
  rw [WeightedMultiplierPell.zero_gcd ha hb hz same] at proper
  exact proper.false

private theorem budget_sizes {k b : ℕ}
    (row : (k,b) ∈ [(4,0),(16,16),(64,64),(128,128),(160,64),(64,256)]) :
    2^k≤(2^(k/2))^2 ∧ 24*2^b≤2^(k/2)*2^1023 ∧
    512*2^k*2^(k/2)*2^1023*2^b≤2^2048 := by
  obtain ⟨even,_,short⟩ := reported_budgets row
  have scale : 24*2^b ≤ 2^1023 := by
    change 64*(24*2^b+1) ≤ 2^1023 at short
    omega
  refine ⟨?_,scale.trans (Nat.le_mul_of_pos_left _ (by positivity)),(reported_height row).le⟩
  rw [←pow_mul,Nat.mul_comm (k/2),even]

/-- Count distinct products from the actual square tests, with no advice
about a root, its squarefree part, or the other products in the set. -/
theorem bound {k b : ℕ}
    (row : (k,b) ∈ [(4,0),(16,16),(64,64),(128,128),(160,64),(64,256)])
    {r s A B : ℕ} (rp : 0<r) (rk : r≤2^k) (sp : 0<s) (sk : s≤2^k)
    (S : Finset ℕ) (hs : ∀ n∈S, Hit r s A B n (2^b)) :
    S.card ≤ 4096*((difference (r,s) A B)^2).divisors.card := by
  classical
  rcases S.eq_empty_or_nonempty with empty|nonempty
  · simp [empty]
  obtain ⟨m,hm⟩ := nonempty
  have cp := (hs m hm).nonsingular
  obtain ⟨t,f,rad,free⟩ := Nat.sq_mul_squarefree (r*s)
  let C := difference (r,s) A B
  let d (n : ℕ) := A^2-4*r*n
  let e (n : ℕ) := B^2-4*s*n
  let point (n : ℕ) := (s*d n+r*e n,2*f*(d n*e n).sqrt)
  have data (n : ℕ) (hn : n∈S) : A^2=d n+4*r*n ∧ B^2=e n+4*s*n ∧
      ((d n*e n).sqrt)^2=d n*e n := by
    obtain ⟨v,w,z,ha,hb,square,_⟩ := (hs n hn).witness
    have first : d n=v := by dsimp [d]; omega
    have second : e n=w := by dsimp [e]; omega
    rw [first,second,←square,Nat.sqrt_eq']
    exact ⟨ha,hb,rfl⟩
  have readout {n : ℕ} (hn : n∈S) :
      (point n).1+(8*r*s)*n=s*A^2+r*B^2 := by
    obtain ⟨a,b,_⟩ := data n hn
    dsimp [point]
    rw [a,b]
    ring
  have inj : Set.InjOn point S := by
    intro n hn m hm eq
    have same := congrArg Prod.fst eq
    have prod : (8*r*s)*n=(8*r*s)*m := by
      have u := readout hn
      have v := readout hm
      omega
    exact Nat.eq_of_mul_eq_mul_left (by positivity) prod
  have norm {n : ℕ} (hn : n∈S) :
      (point n).1^2=t*(point n).2^2+C^2 := by
    obtain ⟨a,b,z⟩ := data n hn
    have a' : (d n:ℤ)+4*r*n=(A:ℤ)^2 := by exact_mod_cast a.symm
    have b' : (e n:ℤ)+4*s*n=(B:ℤ)^2 := by exact_mod_cast b.symm
    have z' : (((d n*e n).sqrt:ℕ):ℤ)^2=(d n:ℤ)*e n := by exact_mod_cast z
    have rad' : (r:ℤ)*s=t*(f:ℤ)^2 := by exact_mod_cast (mul_comm (f^2) t ▸ rad).symm
    have eq := WeightedMultiplierPell.norm_identity (eq_sub_of_add_eq a') (eq_sub_of_add_eq b') z' rad'
    have plus := sub_eq_iff_eq_add.mp eq
    dsimp [point,C,difference]
    apply (Nat.cast_inj (R:=ℤ)).mp
    push_cast
    rw [sq_abs]
    linarith only [plus]
  rw [← Finset.card_image_of_injOn inj]
  apply (WeightedMultiplierPoints.points (C:=C) (K:=2048) cp free _ ?_).trans
  · exact le_rfl
  intro z hz
  obtain ⟨n,hn,rfl⟩ := mem_image.mp hz
  have eq := norm hn
  have lower : 0<(point n).1 := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz] at eq
    have positive : 0<C^2 := pow_pos cp 2
    omega
  obtain ⟨cap,small,size⟩ := budget_sizes row
  obtain ⟨a,b,_⟩ := data n hn
  have top := first_coordinate_lt rp sp rk sk cap small (Real.sqrt_nonneg _) (by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using (hs n hn).top) (hs n hn).first (hs n hn).second
    (Real.sq_sqrt (Nat.cast_nonneg n)) a b
  exact ⟨lower,eq,top.trans_le size⟩

end PrimeFactors.WeightedMultiplierFiber
