import PrimeFactors.FareyWork

namespace PrimeFactors.SparseFareyWork

open Finset FareyWork

/-- Indices in an aligned window are grouped by their quotient modulo M;
a block costs a record only if one of its allowed indices is in the window. -/
noncomputable def occupied (M phase length : ℕ) (kept : Finset ℕ) : Finset ℕ :=
  ((Ico phase (phase+length)).filter (fun u => u%M ∈ kept)).image (fun u => u/M)

/-- Following a single retained index through all its periods gives a
different occupied block for every complete length-M portion of the window. -/
theorem full_periods {M phase length r : ℕ} (hm : 0<M) {kept : Finset ℕ}
    (hr : r<M) (keep : r ∈ kept) : length/M ≤ (occupied M phase length kept).card := by
  let v := phase%M
  have hv : v<M := Nat.mod_lt _ hm
  let e := if v≤r then r-v else M+r-v
  have facts : e<M ∧ (phase+e)%M=r := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (show e<M by dsimp only [e]; split <;> omega)]
    change e<M ∧ (v+e)%M=r
    dsimp only [e]
    split
    · rename_i h
      rw [Nat.add_sub_of_le h, Nat.mod_eq_of_lt hr]
      omega
    · rename_i h
      rw [show v+(M+r-v) = r+M by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hr]
      omega
  have image : (range (length/M)).image (fun j => (phase+e)/M+j) ⊆ occupied M phase length kept := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
    have bound := (Nat.le_div_iff_mul_le hm).mp (show j+1 ≤ length/M by simpa using mem_range.mp hj)
    refine mem_image.mpr ⟨phase+e+j*M,mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,?_⟩,?_⟩,?_⟩
    · rw [Nat.add_mul,one_mul] at bound
      omega
    · simpa [Nat.add_mul_mod_self_right,facts.2] using keep
    · rw [Nat.add_mul_div_right _ _ hm]
  have inj : Function.Injective (fun j : ℕ => (phase+e)/M+j) := fun _ _ => Nat.add_left_cancel
  simpa only [card_image_of_injective _ inj,card_range] using card_le_card image

def labelCount (lo hi offset step : ℕ) : ℕ :=
  if lo+offset≤hi then (hi-(lo+offset))/step+1 else 0

/-- At most one more ordinary block than shifted nonempty blocks is needed
at equal span, irrespective of the position of the first allowed label. -/
theorem row_compare {M phase r : ℕ} (hm : 0<M) {kept : Finset ℕ}
    (hr : r<M) (keep : r∈kept) (lo hi offset step : ℕ) :
    rowGiants lo hi offset step M ≤
      (occupied M phase (labelCount lo hi offset step) kept).card+1 := by
  have hits := full_periods (phase:=phase) (length:=labelCount lo hi offset step) hm hr keep
  unfold rowGiants labelCount at *
  split_ifs with inside
  · let L := (hi-(lo+offset))/step+1
    have less : (L+M-1)/M < L/M+2 := by
      apply (Nat.div_lt_iff_lt_mul hm).mpr
      have := Nat.lt_mul_div_succ L hm
      nlinarith only [this, Nat.sub_le (L+M) 1]
    change (L+M-1)/M ≤ _
    simp only [if_pos inside] at hits
    change L/M ≤ _ at hits
    omega
  · omega

/-- For every positive K and every wheel that keeps at least half of the
positions in its arithmetic span, the full translated schedule already needs
more than 2^403 records at 2048 bits. Only one of its phases is charged. -/
theorem half_density_2048 {N K M r : ℕ} (large : 2^2047≤N) (hk : 1≤K) (hm : 0<M)
    (window : ℕ × ℕ → Window) (phase : ℕ × ℕ → ℕ) (kept : Finset ℕ)
    (hr : r<M) (keep : r∈kept) (density : M≤2*kept.card)
    (valid : ∀ z ∈ primitiveOffsets K, (window z).admissible N K (z.2+z.1) z.2) :
    let G := ∑ z ∈ primitiveOffsets K,
      let w := window z
      let rad := 4*(z.2+z.1)*z.2*N
      (occupied M (phase z) (labelCount (ceilSqrt rad) (rad+w.gain).sqrt w.offset w.step) kept).card
    2^403 < (primitiveOffsets K).card+G+kept.card := by
  have previous := complete_farey_2048 large hk hm window valid
  let rows := primitiveOffsets K
  let g := fun z : ℕ × ℕ =>
    let rad := 4*(z.2+z.1)*z.2*N
    let w := window z
    (occupied M (phase z) (labelCount (ceilSqrt rad) (rad+w.gain).sqrt w.offset w.step) kept).card
  have sums : (∑ z ∈ rows, (window z).blocks N (z.2+z.1) z.2 M) ≤
      (∑ z ∈ rows, g z)+rows.card := by
    simpa only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,mul_one] using
      sum_le_sum (s:=rows) (fun z _ => row_compare (phase:=phase z) hm hr keep
        (ceilSqrt (4*(z.2+z.1)*z.2*N)) (4*(z.2+z.1)*z.2*N+(window z).gain).sqrt
        (window z).offset (window z).step)
  change 2^404 < rows.card+(∑ z ∈ rows, (window z).blocks N (z.2+z.1) z.2 M)+M at previous
  change 2^403 < rows.card+(∑ z ∈ rows, g z)+kept.card
  omega

/-- The three primes used in the 99-bit comparison keep all unit residues
in each full period, with ratio 240/385. -/
theorem wheel385_density : ((range 385).filter (fun i => i%5≥1 ∧ i%7≥1 ∧ i%11≥1)).card = 240 :=
  by decide +kernel

end PrimeFactors.SparseFareyWork
