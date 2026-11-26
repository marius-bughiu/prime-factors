import PrimeFactors.ArbitraryDivisorWindow
import PrimeFactors.ReciprocalSumSlice

/-! A prescribed-center weighted trace can be tested against the existing
modulo-211 table before taking a large integer square root. -/
namespace PrimeFactors.WeightedSumResidueSlice

open Finset ArbitraryDivisorWindow ReciprocalSumSlice

local instance : Fact (Nat.Prime 211) := ⟨by norm_num⟩

/-- For a nonzero leading coefficient, solve for the residue of the scaled
divisor using the ordinary sum table. A zero leading coefficient is linear. -/
noncomputable def residues (n a b z : ZMod 211) : Finset (ZMod 211) :=
  if a = 0 then (if z = 0 then ∅ else {b*n/z})
  else (fromSum (a*b*n) z).image (fun v => v/a)

theorem card_residues (n a b z : ZMod 211) : (residues n a b z).card ≤ 2 := by
  unfold residues
  split
  · split <;> simp
  · exact card_image_le.trans (fromSum_card ..)

theorem mem_residues {n a b z d : ZMod 211} (unit : n ≠ 0) (usable : a ≠ 0 ∨ b ≠ 0) :
    d ∈ residues n a b z ↔ d*(z-a*d)=b*n := by
  by_cases ha : a=0
  · have hb : b≠0 := usable.resolve_left (not_not.mpr ha)
    by_cases hz : z=0
    · simp [residues,ha,hz,hb,unit]
    · simp [residues,ha,hz,eq_div_iff hz]
  · simp only [residues, if_neg ha, mem_image, mem_fromSum]
    constructor
    · rintro ⟨v,hv,vd⟩
      have eqv : v = a*d := by rw [eq_comm,mul_comm]; exact ((eq_div_iff ha).mp vd.symm)
      rw [eqv] at hv
      exact mul_left_cancel₀ ha (by linear_combination hv)
    · intro h
      exact ⟨a*d,by linear_combination a*h,by field_simp⟩

private theorem divide_weights {n c w a b u v : ℤ} (win : Window n c w)
    (wt : Weights n c w a b) (hu : a=211*u) (hv : b=211*v) : Weights n c w u v := by
  obtain ⟨ap,bp,bcap,err⟩ := wt
  rw [hu,hv,show 211*u*c^2-211*v*n=211*(u*c^2-v*n) by ring,abs_mul] at err
  have wp := win.1
  have : 0≤|u*c^2-v*n| *(2*w+1) := mul_nonneg (abs_nonneg _) (by omega)
  norm_num at err
  exact ⟨by omega,by omega,by omega,by linarith only [err,this]⟩

/-- The existence theorem for weights permits choosing a pair which does not
vanish simultaneously modulo the fixed table prime. -/
theorem usable_weights {n c w : ℕ} (win : Window n c w) :
    ∃ a b : ℤ, Weights n c w a b ∧ ((a:ZMod 211) ≠ 0 ∨ (b:ZMod 211) ≠ 0) := by
  classical
  let works (j : ℕ) := ∃ a : ℤ, Weights n c w a j
  have existsW : ∃ j, works j := by
    obtain ⟨a,b,wt⟩ := weights_exist win
    exact ⟨b.toNat,a,by simpa only [Int.toNat_of_nonneg wt.2.1.le] using wt⟩
  obtain ⟨a,wt⟩ := Nat.find_spec existsW
  refine ⟨a,Nat.find existsW,wt,?_⟩
  by_contra! h
  obtain ⟨u,hu⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a 211).mp h.1
  obtain ⟨v,hv⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (Nat.find existsW:ℤ) 211).mp h.2
  have wt' := divide_weights win wt hu hv
  have smaller : v.toNat < Nat.find existsW := by have := wt'.2.1; omega
  exact Nat.find_min existsW smaller ⟨u,by simpa only [Int.toNat_of_nonneg wt'.2.1.le] using wt'⟩

/-- The new modular test covers every odd divisor in the window, using only
the small square table and its publicly chosen weights and trace. -/
theorem covers {n c w a b d q : ℤ} (win : Window n c w) (wt : Weights n c w a b)
    (unit : (n:ZMod 211) ≠ 0) (usable : (a:ZMod 211) ≠ 0 ∨ (b:ZMod 211) ≠ 0)
    (pair : n=d*q) (nearby : |d-c| ≤ w) (od : Odd d) (oq : Odd q) :
    (d:ZMod 211) ∈ residues n a b (traceRow n c a b) := by
  apply (mem_residues unit usable).mpr
  rw [←trace_eq win wt pair nearby od oq,pair]
  push_cast
  ring

/-- At most four odd integer positions survive an 844-integer slice. -/
theorem four_positions (l u : ℤ) (n a b z : ZMod 211) (width : u-l≤843) :
    (oddSites l u (residues n a b z)).card ≤ 4 :=
  (oddSites_card l u _ width).trans (Nat.mul_le_mul_left 2 (card_residues ..))

/-- Every full 844-integer block inside the entire ratio-two range admits
public weights with at most four surviving odd positions. -/
theorem four_on_full_block {n l : ℕ} (large : 2^29≤l) (lower : n≤2*l^2)
    (upper : (l+843)^2≤n) (unit : ((n:ℤ):ZMod 211)≠0) :
    ∃ a b : ℤ, Weights n ((l:ℤ)+421) 422 a b ∧
      let sites := oddSites l ((l:ℤ)+843) (residues n a b (traceRow n ((l:ℤ)+421) a b))
      sites.card ≤ 4 ∧ 416 ≤ (ordinary l ((l:ℤ)+843) \ sites).card ∧
      ∀ d q : ℤ, (n:ℤ)=d*q → Odd d → Odd q → (l:ℤ)≤d → d≤(l:ℤ)+843 → d∈sites := by
  have bot : n≤2*(l+421)^2 := lower.trans (by gcongr; omega)
  have top : (l+421)^2≤n := (show (l+421)^2≤(l+843)^2 by gcongr; omega).trans upper
  have win : Window n (l+421:ℕ) (422:ℕ) := by
    refine ⟨by decide,by positivity,by exact_mod_cast top,by exact_mod_cast bot,?_⟩
    push_cast
    change 300605792 < (l:ℤ)+421-422
    omega
  obtain ⟨a,b,wt,usable⟩ := usable_weights win
  push_cast at win wt
  refine ⟨a,b,wt,?_⟩
  dsimp only
  have cap := four_positions (l:ℤ) ((l:ℤ)+843) (n:ZMod 211) a b
    (traceRow n ((l:ℤ)+421) a b) (by omega)
  refine ⟨cap,?_,?_⟩
  · have bound := card_le_card_sdiff_add_card (s:=ordinary l ((l:ℤ)+843))
      (t:=oddSites l ((l:ℤ)+843) (residues n a b (traceRow n ((l:ℤ)+421) a b)))
    rw [ordinary_full] at bound
    omega
  · intro d q pair od oq lo hi
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨lo,hi⟩,?_,?_⟩
    · obtain ⟨u,hu⟩ := od
      omega
    · apply covers win wt unit usable pair (abs_le.mpr (by omega)) od oq

end PrimeFactors.WeightedSumResidueSlice
