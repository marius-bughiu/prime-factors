import PrimeFactors.FractionalTwoCorrectionObstructions

/-! The largest possible denominator when at most two ordinary corrections
are allowed for every unit factor pair of a fixed product residue. -/
namespace PrimeFactors.FractionalTwoCorrectionLimit

open Finset FractionalCorrectionBudget FractionalPrefixResidues

/-- Each modular sum at any divisor is the reduction of a compatible
ordinary correction at the original modulus. -/
theorem projects {m d : ℕ} [NeZero m] [NeZero d] (div : d ∣ m)
    (u : (ZMod m)ˣ) {t : ZMod d} (ht : AdmissibleSum (ZMod.unitsMap div u : ZMod d) t) :
    t ∈ (menu u).image (fun a : ℕ => (a : ZMod d)) := by
  obtain ⟨a,ha,rfl⟩ := (represents _ _).mp ht
  obtain ⟨v,_,rfl⟩ := mem_image.mp ha
  obtain ⟨w,rfl⟩ := ZMod.unitsMap_surjective div v
  refine mem_image.mpr ⟨correction u w, mem_image_of_mem _ (mem_univ _), ?_⟩
  have reduce (z : (ZMod m)ˣ) : ((z : ZMod m).val : ZMod d) = (ZMod.unitsMap div z : ZMod d) := by
    change _ = ZMod.castHom div (ZMod d) (z : ZMod m)
    simpa only [map_natCast] using congrArg (ZMod.castHom div (ZMod d)) (ZMod.natCast_zmod_val (z : ZMod m))
  simp only [correction,Nat.cast_add,ZMod.natCast_zmod_val,←map_div,reduce]

private theorem leaves_three {m d : ℕ} [NeZero m] [NeZero d] (div : d ∣ m) (u : (ZMod m)ˣ)
    {a b c : ZMod d} (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (ha : AdmissibleSum (ZMod.unitsMap div u : ZMod d) a)
    (hb : AdmissibleSum (ZMod.unitsMap div u : ZMod d) b)
    (hc : AdmissibleSum (ZMod.unitsMap div u : ZMod d) c) : 3 ≤ (menu u).card := by
  let A := (menu u).image (fun t : ℕ => (t : ZMod d))
  have sub : ({a,b,c} : Finset _) ⊆ A := by
    simpa only [insert_subset_iff,singleton_subset_iff] using
      And.intro (projects div u ha) ⟨projects div u hb,projects div u hc⟩
  have count := (card_le_card sub).trans card_image_le
  simpa [ab,ac,bc] using count

private theorem possible_divisor {m : ℕ} [NeZero m] (u : (ZMod m)ˣ)
    (small : (menu u).card ≤ 2) : m ∣ 120960 := by
  let g := m.gcd 20160
  let k := m/g
  have lower := spacing_bound u
  have cube : k ≤ 3 := by
    change m / m.gcd 20160 ≤ 3
    interval_cases e : (menu u).card <;> simp_all <;> omega
  have pos : 0 < k := Nat.div_pos (Nat.le_of_dvd (NeZero.pos m) (Nat.gcd_dvd_left ..))
    (Nat.gcd_pos_of_pos_left _ (NeZero.pos m))
  have factor : k ∣ 6 := by interval_cases k <;> decide
  have div := Nat.mul_dvd_mul (Nat.gcd_dvd_right m 20160) factor
  simpa only [k,g,Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)] using div

private def obstruction (m : ℕ) : Prop := 7∣m ∨ 27∣m ∨ 64∣m ∨ 45∣m ∨ 80∣m ∨ 144∣m
private instance (m : ℕ) : Decidable (obstruction m) := by unfold obstruction; infer_instance

private theorem large_divisor {m : ℕ} (h : m ∣ 120960) (large : 120 < m) : obstruction m := by
  change m ∣ 2^7 * (3^3 * (5^1 * 7^1)) at h
  obtain ⟨A,BCD,ha,hBCD,rfl⟩ := Nat.dvd_mul.mp h
  obtain ⟨B,CD,hb,hCD,rfl⟩ := Nat.dvd_mul.mp hBCD
  obtain ⟨C,D,hc,hd,rfl⟩ := Nat.dvd_mul.mp hCD
  obtain ⟨a,la,rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ha
  obtain ⟨b,lb,rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hb
  obtain ⟨c,lc,rfl⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 5)).mp hc
  obtain ⟨d,ld,rfl⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 7)).mp hd
  have table : ∀ a : Fin 8, ∀ b : Fin 4, ∀ c d : Fin 2,
      let M := 2^a.val * (3^b.val * (5^c.val * 7^d.val))
      120 < M → obstruction M := by decide +kernel
  exact table ⟨a,by omega⟩ ⟨b,by omega⟩ ⟨c,by omega⟩ ⟨d,by omega⟩ large

/-- A complete list of at most two ordinary corrections forces m ≤ 120,
even if the product residue is chosen separately at every modulus. -/
theorem at_most_120 {m : ℕ} [NeZero m] (u : (ZMod m)ˣ) (small : (menu u).card ≤ 2) :
    m ≤ 120 := by
  by_contra! large
  have excludes (d : ℕ) [NeZero d] (listed : d ∈ ([7,27,64,45,80,144] : List ℕ)) : ¬ d ∣ m := by
    intro div
    obtain ⟨_,_,_,ab,ac,bc,ha,hb,hc⟩ :=
      FractionalTwoCorrectionObstructions.three listed (ZMod.unitsMap div u)
    have lower := leaves_three div u ab ac bc ha hb hc
    omega
  have bad := large_divisor (possible_divisor u small) large
  rcases bad with h|h|h|h|h|h
  all_goals exact excludes _ (by decide) h

set_option exponentiation.threshold 4096 in
/-- Counting an entire interval with at most two universal corrections at
2048 bits takes more than 2^2040 integer positions. -/
theorem full_cutoff {n m : ℕ} [NeZero m] (width : 2^2047 ≤ n) (u : (ZMod m)ˣ)
    (small : (menu u).card ≤ 2) : 2^2040 < n/m := by
  apply (Nat.le_div_iff_mul_le (NeZero.pos m)).mpr
  exact (Nat.mul_le_mul_left (2^2040+1) (at_most_120 u small)).trans
    ((by norm_num : (2^2040+1)*120 ≤ (2^2047 : ℕ)).trans width)

end PrimeFactors.FractionalTwoCorrectionLimit
