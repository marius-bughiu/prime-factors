import PrimeFactors.ComplementaryBatch
namespace PrimeFactors.ComplementaryBirthday
open Finset TwelveResidueCollision TwelveImageSize ComplementaryKeys UniformFiberBirthday

noncomputable def cleaned (p : ℕ) [Fact p.Prime] :=
  (regulars p).filter fun x => value x≠1-value x
noncomputable def outputs (p : ℕ) [Fact p.Prime] := (cleaned p).image (fold ∘ value)

private theorem size_lower {p : ℕ} [Fact p.Prime] (big : 864<p) : p≤(cleaned p).card+25 := by
  have all := filter_card_add_filter_neg_card_eq_card (s:=regulars p) (fun x => value x=1-value x)
  have mid := middle_bound big
  have old := regular_count p
  change ((regulars p).filter (fun x => value x=1-value x)).card + (cleaned p).card = (regulars p).card at all
  omega

private theorem count_clean {p : ℕ} [Fact p.Prime] (big : 864<p) {x : ZMod p} (hx : x∈cleaned p) :
    ((cleaned p).filter (fun y => fold (value x)=fold (value y))).card =
      12 + (if IsSquare (3:ZMod p) then 12 else 0) := by
  obtain ⟨rx,apart⟩ := mem_filter.mp hx
  rw [←fold_count big rx apart]
  congr 1
  ext y
  simp only [cleaned,mem_filter]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · rintro ⟨ry,h⟩
    refine ⟨⟨ry,fun fixed => apart ?_⟩,h⟩
    rcases (fold_eq _ _).mp h with eq|eq
    · rwa [eq]
    · linear_combination -fixed + 2*eq

noncomputable def project {p : ℕ} [Fact p.Prime] (x : ↥(cleaned p)) : ↥(outputs p) :=
  ⟨fold (value x.val), mem_image_of_mem _ x.property⟩

theorem project_fiber {p : ℕ} [Fact p.Prime] (big : 864<p) (b : ↥(outputs p)) :
    Nat.card {x : ↥(cleaned p) // project x=b} = 12+(if IsSquare (3:ZMod p) then 12 else 0) := by
  obtain ⟨a,ha,eq⟩ := mem_image.mp b.property
  change fold (value a)=b.val at eq
  let e : {x : ↥(cleaned p) // project x=b} ≃
      ↥((cleaned p).filter (fun y => fold (value a)=fold (value y))) :=
    { toFun := fun x => ⟨x.1.val,mem_filter.mpr ⟨x.1.property,eq.trans (congrArg Subtype.val x.2).symm⟩⟩
      invFun := fun y => ⟨⟨y.val,(mem_filter.mp y.property).1⟩,
        Subtype.ext ((mem_filter.mp y.property).2.symm.trans eq)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe,count_clean big ha]

set_option exponentiation.threshold 2050
set_option maxRecDepth 8192
def budget : ℕ := 105*2^504

theorem budget_ratio : 128*budget=105*2^511 := by norm_num [budget]

private theorem bounds {p : ℕ} [Fact p.Prime] (lo : 2^1023≤p) (hi : p<2^1024) :
    2^1018≤(outputs p).card ∧ (12+(if IsSquare (3:ZMod p) then 12 else 0))*(outputs p).card≤2^1024 := by
  have big : 864<p := (by norm_num : 864<2^1023).trans_le lo
  have card := seed_card (project (p:=p)) (project_fiber big)
  simp only [Fintype.card_coe] at card
  have small : (cleaned p).card ≤ p := by simpa using (cleaned p).card_le_univ
  have many := size_lower big
  split_ifs at * <;> norm_num at * <;> omega

/-- The product bound on no-collision words uses the different local
image sizes at the two primes. -/
theorem mixed_bound {d e : ℕ} (dlo : 2^1018≤d) (elo : 2^1018≤e)
    (dhi : 24*d≤2^1024) (ehi : 12*e≤2^1024) :
    (95:ℝ)/100 < distinctProbability (d*e) budget -
      distinctProbability d budget * distinctProbability e budget := by
  have mpos : 0<budget := by norm_num [budget]
  have small : budget≤2^1018 := by norm_num [budget]
  have dp := mpos.trans_le (small.trans dlo)
  have ep := mpos.trans_le (small.trans elo)
  apply bound_from_rates mpos (small.trans dlo) (small.trans elo)
  · have u : (24:ℝ)*d≤2^1024 := by exact_mod_cast dhi
    have v : (12:ℝ)*e≤2^1024 := by exact_mod_cast ehi
    have a : (2:ℝ)≤(budget:ℝ)*(budget-1)/(2*d) := by
      apply (le_div_iff₀ (by positivity)).mpr
      norm_num [budget] at u ⊢
      linarith only [u]
    have b : (1:ℝ)≤(budget:ℝ)*(budget-1)/(2*e) := by
      apply (le_div_iff₀ (by positivity)).mpr
      norm_num [budget] at v ⊢
      linarith only [v]
    calc
      _ = -((budget:ℝ)*(budget-1)/(2*d) + (budget:ℝ)*(budget-1)/(2*e)) := by ring
      _ ≤ -((2:ℝ)+1) := neg_le_neg (add_le_add a b)
      _ ≤ _ := by norm_num
  · have dR : (2:ℝ)^1018≤d := by exact_mod_cast dlo
    have eR : (2:ℝ)^1018≤e := by exact_mod_cast elo
    have product := mul_le_mul dR eR (by positivity) (by positivity)
    rw [Nat.cast_mul]
    apply (div_le_iff₀ (by positivity)).mpr
    norm_num [budget] at product ⊢
    linarith only [product]

/-- On independent uniform regular, nonmiddle coordinates of any mixed
prime pair, the smaller budget already gives a proper collision with
probability above 95 percent. Ordering here only identifies the two roles. -/
theorem mixed_odds {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (pl : 2^1023≤p) (ph : p<2^1024) (ql : 2^1023≤q) (qh : q<2^1024)
    (yes : IsSquare (3:ZMod p)) (no : ¬IsSquare (3:ZMod q)) :
    (95:ℝ)/100 < TwelveSeedBirthday.odds
      (Prod.map (project (p:=p)) (project (p:=q))) budget := by
  have pbig : 864<p := (by norm_num : 864<2^1023).trans_le pl
  have qbig : 864<q := (by norm_num : 864<2^1023).trans_le ql
  have hp := bounds pl ph
  have hq := bounds ql qh
  simp [yes] at hp
  simp [no] at hq
  have positive (r : ℕ) [Fact r.Prime] (lower : 2^1018≤(outputs r).card) :
      0<Fintype.card ↥(outputs r) := by
    rw [Fintype.card_coe]
    exact (by norm_num : 0<2^1018).trans_le lower
  have lower := proper_probability_lower (B:=↥(outputs p)) (C:=↥(outputs q)) budget
    (positive p hp.1) (positive q hq.1)
  simp only [Fintype.card_coe] at lower
  have h := (mixed_bound hp.1 hq.1 hp.2 hq.2).trans_le lower
  let f := Prod.map (project (p:=p)) (project (p:=q))
  have fp (b : ↥(outputs p)) : Nat.card {a : ↥(cleaned p) // project a=b}=24 := by
    simpa [yes] using project_fiber pbig b
  have fq (b : ↥(outputs q)) : Nat.card {a : ↥(cleaned q) // project a=b}=12 := by
    simpa [no] using project_fiber qbig b
  have rate := event_probability f (product_fibers _ _ fp fq) (by norm_num : 0<24*12)
    (m:=budget) (fun w => ProperPair w)
  rw [Fintype.card_prod,Fintype.card_prod] at rate
  unfold TwelveSeedBirthday.odds
  rw [Fintype.card_prod]
  simp only [Fintype.card_coe] at rate ⊢
  exact h.trans_eq rate.symm

end PrimeFactors.ComplementaryBirthday
