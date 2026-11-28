import PrimeFactors.CircleMarkRationalFrequency
import Mathlib.NumberTheory.ArithmeticFunction

/-! Finite Möbius estimates for visible lattice points in a rectangle or
any positive subregion. The tail is charged once to the enclosing rectangle. -/
namespace PrimeFactors.CircleMarkPrimitiveDensity

open Finset ArithmeticFunction CircleMarkRationalFrequency
open scoped ArithmeticFunction

/-- Number of lattice points whose two coordinates are divisible by `d`. -/
noncomputable def multiplicity (S : Finset (ℕ×ℕ)) (d : ℕ) : ℕ :=
  (S.filter fun z => d∣z.1 ∧ d∣z.2).card

/-- The coefficient of the area at finite Möbius cutoff `K`. -/
noncomputable def coefficient (K : ℕ) : ℚ := ∑ d∈Icc 1 K, (μ d:ℚ)/(d:ℚ)^2

private theorem indicator {H i j : ℕ} (ip : 0 < i) (ih : i≤H) :
    (if i.Coprime j then (1:ℚ) else 0) =
      ∑ d∈Icc 1 H, if d∣i ∧ d∣j then (μ d:ℚ) else 0 := by
  have gp : 0 < i.gcd j := Nat.gcd_pos_of_pos_left j ip
  have sel : (Icc 1 H).filter (fun d => d∣i ∧ d∣j) = (i.gcd j).divisors := by
    ext d
    simp only [mem_filter,mem_Icc,Nat.mem_divisors,Nat.dvd_gcd_iff]
    exact ⟨fun h => ⟨h.2, gp.ne'⟩, fun ⟨h,_⟩ => ⟨⟨Nat.pos_of_dvd_of_pos h.1 ip, (Nat.le_of_dvd ip h.1).trans ih⟩,h⟩⟩
  rw [←sum_filter,sel]
  have inv := congrArg (fun f : ArithmeticFunction ℤ => f (i.gcd j)) coe_zeta_mul_moebius
  simp only [coe_zeta_mul_apply,one_apply] at inv
  by_cases one : i.gcd j=1 <;> simp only [Nat.Coprime,one,if_true,if_false] at inv ⊢ <;>
    exact_mod_cast inv.symm

private theorem expansion {S : Finset (ℕ×ℕ)} {H D : ℕ} (sub : S⊆rectangle H D) :
    ((S.filter (fun z => z.1.Coprime z.2)).card:ℚ) =
      ∑ d∈Icc 1 H, (μ d:ℚ)*multiplicity S d := by
  calc
    _ = ∑ z∈S, if z.1.Coprime z.2 then (1:ℚ) else 0 := by simp
    _ = ∑ z∈S, ∑ d∈Icc 1 H, if d∣z.1 ∧ d∣z.2 then (μ d:ℚ) else 0 := by
      apply sum_congr rfl
      intro z zm
      obtain ⟨lo,hi⟩ := mem_Icc.mp (mem_product.mp (sub zm)).1
      exact indicator lo hi
    _ = _ := by rw [sum_comm]; apply sum_congr rfl; intro d _; rw [←sum_filter]; simp [multiplicity,mul_comm]

theorem rectangle_multiplicity (H D d : ℕ) :
    multiplicity (rectangle H D) d=(H/d)*(D/d) := by
  have eqn : (rectangle H D).filter (fun z => d∣z.1 ∧ d∣z.2) =
      ((Icc 1 H).filter (d∣·)) ×ˢ ((Icc 1 D).filter (d∣·)) := by
    ext z
    simp only [rectangle,mem_filter,mem_product]
    tauto
  rw [multiplicity,eqn,card_product,Nat.Icc_succ_left 0 H,Nat.Icc_succ_left 0 D,
    Nat.Ioc_filter_dvd_card_eq_div,Nat.Ioc_filter_dvd_card_eq_div]

private theorem tail_weight (K N : ℕ) (kp : 0<K) :
    ∑ d∈Icc (K+1) (K+N), (1:ℚ)/(d:ℚ)^2 ≤ 1/(K:ℚ)-1/((K:ℚ)+N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show K+N.succ = (K+N)+1 by omega,sum_Icc_succ_top (by omega : K+1≤K+N+1)]
    push_cast
    let t := (K:ℚ)+N
    have positive : 0<t := by dsimp [t]; positivity
    have bound : 1/(t+1)^2 ≤ 1/t-1/(t+1) := by
      calc
        1/(t+1)^2 ≤ 1/(t*(t+1)) := by
          apply one_div_le_one_div_of_le (by positivity)
          nlinarith
        _ = _ := by field_simp
    change _ + 1/(t+1)^2 ≤ _
    change _ ≤ 1/(K:ℚ)-1/t at ih
    have last : (K:ℚ)+(N+1)=t+1 := by dsimp [t]; ring
    rw [last]
    linarith

/-- For every shape the uncomputed terms depend only on its bounding box. -/
theorem truncated {S : Finset (ℕ×ℕ)} {H D K : ℕ} (sub : S⊆rectangle H D)
    (kp : 0<K) (kh : K≤H) :
    |((S.filter (fun z => z.1.Coprime z.2)).card:ℚ) -
      ∑ d∈Icc 1 K, (μ d:ℚ)*multiplicity S d| ≤ (H:ℚ)*D/K := by
  let f := fun d : ℕ => (μ d:ℚ)*multiplicity S d
  have blocks : Icc 1 H=Icc 1 K ∪ Icc (K+1) H := by ext n; simp only [mem_Icc,mem_union]; omega
  have split : Disjoint (Icc 1 K) (Icc (K+1) H) := by
    apply disjoint_left.mpr; intro x hx hy; have := mem_Icc.mp hx; have := mem_Icc.mp hy; omega
  rw [expansion sub, blocks,sum_union split,add_sub_cancel_left]
  have term (d : ℕ) : |f d|≤((H:ℚ)*D)*(1/(d:ℚ)^2) := by
    have subcard : multiplicity S d≤(H/d)*(D/d) := (card_le_card (filter_subset_filter _ sub)).trans_eq
      (rectangle_multiplicity H D d)
    have abs_mu : |(μ d:ℚ)|≤1 := by exact_mod_cast abs_moebius_le_one (n:=d)
    dsimp [f]
    rw [abs_mul,abs_of_nonneg (show (0:ℚ)≤multiplicity S d from Nat.cast_nonneg _)]
    calc _ ≤ 1*((H/d:ℕ):ℚ)*((D/d:ℕ):ℚ) := by
           simpa only [one_mul,Nat.cast_mul] using mul_le_mul abs_mu
             (show ((multiplicity S d):ℚ)≤((H/d:ℕ):ℚ)*((D/d:ℕ):ℚ) by exact_mod_cast subcard)
             (Nat.cast_nonneg _) zero_le_one
         _ ≤ ((H:ℚ)/d)*((D:ℚ)/d) := by
           rw [one_mul]; exact mul_le_mul Nat.cast_div_le Nat.cast_div_le (by positivity) (by positivity)
         _ = _ := by ring
  have tail := tail_weight K (H-K) kp
  rw [Nat.add_sub_of_le kh] at tail
  have upper : (∑ d∈Icc (K+1) H, (1:ℚ)/(d:ℚ)^2) ≤ 1/(K:ℚ) := tail.trans (sub_le_self _ (by positivity))
  calc |∑ d∈Icc (K+1) H, f d| ≤ ∑ d∈Icc (K+1) H, |f d| := abs_sum_le_sum_abs ..
       _ ≤ _ := sum_le_sum (fun d _ => term d)
       _ = _ := (mul_sum ..).symm
       _ ≤ _ := by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left upper (by positivity : 0≤(H:ℚ)*D)

/-- A period count for a shape incurs one rounded-count error per small
divisor, and one tail term for the complete enclosing box. -/
theorem region_lower {S : Finset (ℕ×ℕ)} {H D K : ℕ} {V E : ℚ}
    (sub : S⊆rectangle H D) (kp : 0<K) (kh : K≤H)
    (err : ∀ d∈Icc 1 K, |(multiplicity S d:ℚ) - V/(d:ℚ)^2| ≤ E) :
    coefficient K*V-(K:ℚ)*E-(H:ℚ)*D/K ≤ ((S.filter (fun z => z.1.Coprime z.2)).card:ℚ) := by
  have weighted := sum_le_sum (s:=Icc 1 K) (fun d dm =>
    (abs_le.mp (show |(μ d:ℚ)*((multiplicity S d:ℚ)-V/(d:ℚ)^2)|≤E by
      rw [abs_mul]
      simpa using mul_le_mul (show |(μ d:ℚ)|≤1 by exact_mod_cast abs_moebius_le_one (n:=d))
        (err d dm) (abs_nonneg _) zero_le_one)).1)
  have rewrite (d : ℕ) : (μ d:ℚ)*((multiplicity S d:ℚ)-V/(d:ℚ)^2)=
      (μ d:ℚ)*multiplicity S d - ((μ d:ℚ)/(d:ℚ)^2)*V := by ring
  simp only [rewrite,sum_sub_distrib,←sum_mul,sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul] at weighted
  have remainder := (abs_le.mp (truncated sub kp kh)).1
  unfold coefficient
  linarith

-- Finite computation of μ by testing divisibility. Both equivalences are
-- proved here so the final comparison can be reduced by Lean's kernel.
private def primesIn (n : ℕ) :=
  (Icc 2 n).filter (fun p => p.Prime ∧ p ∣ n)

private def finiteMu (n : ℕ) : ℤ :=
  if ∀ p ∈ primesIn n, ¬ p*p ∣ n then (-1)^((primesIn n).card) else 0

private theorem finiteMu_eq {n : ℕ} (hn : 0 < n) : finiteMu n = μ n := by
  have factors : primesIn n = n.primeFactors := by
    ext p
    simp only [primesIn, mem_filter, mem_Icc, Nat.mem_primeFactors_of_ne_zero hn.ne']
    exact ⟨And.right, fun h => ⟨⟨h.1.two_le, Nat.le_of_dvd hn h.2⟩, h⟩⟩
  have square : (∀ p ∈ n.primeFactors, ¬ p*p ∣ n) ↔ Squarefree n := by
    rw [Nat.squarefree_iff_prime_squarefree]
    refine ⟨fun h p hp dv => h p ?_ dv, fun h p hp => h p (Nat.prime_of_mem_primeFactors hp)⟩
    exact (Nat.mem_primeFactors_of_ne_zero hn.ne').mpr ⟨hp, (dvd_mul_right p p).trans dv⟩
  rw [finiteMu, factors]
  by_cases sq : Squarefree n
  · rw [if_pos (square.mpr sq), moebius_apply_of_squarefree sq, cardFactors_apply, Nat.primeFactors,
      List.toFinset_card_of_nodup ((Nat.squarefree_iff_nodup_primeFactorsList hn.ne').mp sq)]
  · rw [if_neg (fun h => sq (square.mp h)), moebius_eq_zero_of_not_squarefree sq]

/-- Exact finite arithmetic gives the coefficient used for the explicit density. -/
theorem coefficient_160 : (608:ℚ)/1000 < coefficient 160 := by
  unfold coefficient
  have eqn : (∑ d∈Icc 1 160, (μ d:ℚ)/(d:ℚ)^2) =
      ∑ d∈Icc 1 160, (finiteMu d:ℚ)/(d:ℚ)^2 := by
    apply sum_congr rfl
    intro d hd
    rw [finiteMu_eq (mem_Icc.mp hd).1]
  rw [eqn]
  set_option maxRecDepth 10000 in
    set_option maxHeartbeats 1000000 in decide +kernel

private theorem rounded_upper (n d : ℕ) (dp : 0 < d) :
    (n:ℚ)/d ≤ ((n/d:ℕ):ℚ)+1 := by
  apply le_of_lt
  apply (div_lt_iff₀ (by exact_mod_cast dp : (0:ℚ)<d)).mpr
  exact_mod_cast (by simpa only [Nat.mul_comm d] using Nat.lt_mul_div_succ n dp)

theorem rectangle_error (H D d : ℕ) (dp : 0 < d) :
    |(multiplicity (rectangle H D) d:ℚ)-(H:ℚ)*D/(d:ℚ)^2| ≤ (H:ℚ)+D := by
  rw [rectangle_multiplicity, Nat.cast_mul, show (H:ℚ)*D/(d:ℚ)^2 = (H/d)*(D/d) by ring]
  have hfloor := Nat.cast_div_le (α:=ℚ) (m:=H) (n:=d)
  have dfloor := Nat.cast_div_le (α:=ℚ) (m:=D) (n:=d)
  have hcap : (H:ℚ)/d ≤ H := div_le_self (by positivity) (by exact_mod_cast dp)
  have dcap : ((D/d:ℕ):ℚ) ≤ D := by exact_mod_cast Nat.div_le_self D d
  rw [abs_of_nonpos (sub_nonpos.mpr (mul_le_mul hfloor dfloor (by positivity) (by positivity)))]
  have a := mul_le_mul_of_nonneg_left (rounded_upper D d dp) (by positivity : 0 ≤ (H:ℚ)/d)
  have b := mul_le_mul_of_nonneg_right (rounded_upper H d dp) (by positivity : 0 ≤ ((D/d:ℕ):ℚ))
  nlinarith only [a,b,hcap,dcap]

/-- At least 60.1% of the pairs are visible for side lengths of at least 2^20. -/
theorem large_rectangle {H D : ℕ} (hl : 2^20 ≤ H) (dl : 2^20 ≤ D) :
    601*(H*D) < 1000*(primitive H D).card := by
  have lower := region_lower (S:=rectangle H D) (Subset.rfl) (K:=160)
    (by decide) (by omega) (fun d hd => rectangle_error H D d (mem_Icc.mp hd).1)
  change _ ≤ ((primitive H D).card:ℚ) at lower
  have Hlo : (1048576:ℚ) ≤ H := by exact_mod_cast hl
  have Dlo : (1048576:ℚ) ≤ D := by exact_mod_cast dl
  have h := mul_le_mul_of_nonneg_left Dlo (by positivity : (0:ℚ) ≤ H)
  have d := mul_le_mul_of_nonneg_right Hlo (by positivity : (0:ℚ) ≤ D)
  have v : (0:ℚ) < (H:ℚ)*D := mul_pos (by linarith) (by linarith)
  have coef := mul_lt_mul_of_pos_right coefficient_160 v
  exact_mod_cast (show 601*((H:ℚ)*D) < 1000*(primitive H D).card by
    norm_num only [Nat.cast_ofNat] at lower
    nlinarith only [lower,h,d,coef,v])

theorem three_fifths {H D : ℕ} (hl : 2^20 ≤ H) (dl : 2^20 ≤ D) :
    3*(H*D) < 5*(primitive H D).card := by
  have := large_rectangle hl dl
  omega

end PrimeFactors.CircleMarkPrimitiveDensity
