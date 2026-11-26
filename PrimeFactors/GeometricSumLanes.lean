import PrimeFactors.GeometricDoubleMatch
import PrimeFactors.PowerSignature

/-! Skipping impossible low sum digits before evaluating a geometric product. -/
namespace PrimeFactors.GeometricSumLanes
open Finset

/-- Odd residues are units modulo 32 and their eighth power is 1. -/
noncomputable def residues (n : ℕ) : Finset ℕ :=
  ((range 32).filter (fun x => x%2=1)).image (fun x => (x+n*x^7)%32)

/-- Offset in a 32-term block, starting at the public lower endpoint. -/
noncomputable def offsets (n l : ℕ) : Finset ℕ :=
  (range 32).filter (fun i => (l+i)%32∈residues n)

private theorem finite_mask : ∀ a b : Fin 32, a.val%2=1 → b.val%2=1 →
    (a.val+b.val)%32∈residues ((a.val*b.val)%32) := by decide +kernel

theorem true_residue {p q : ℕ} (po : p%2=1) (qo : q%2=1) :
    (p+q)%32 ∈ residues ((p*q)%32) := by
  have h := finite_mask ⟨p%32,Nat.mod_lt _ (by decide)⟩ ⟨q%32,Nat.mod_lt _ (by decide)⟩
  simp only [Nat.mod_mod_of_dvd _ (by decide : 2∣32), ←Nat.add_mod, ←Nat.mul_mod, Fin.val_mk] at h
  exact h po qo

private theorem size_table : ∀ n l : Fin 32, n.val%2=1 →
    (offsets n.val l.val).card = if n.val%8=5 then 2 else 4 := by
  decide +kernel

theorem offset_count {n : ℕ} (odd : n%2=1) (l : ℕ) :
    (offsets (n%32) (l%32)).card = if n%8=5 then 2 else 4 := by
  have h := size_table ⟨n%32,Nat.mod_lt _ (by decide)⟩ ⟨l%32,Nat.mod_lt _ (by decide)⟩
  simp only [Fin.val_mk,Nat.mod_mod_of_dvd _ (by decide : 2∣32),Nat.mod_mod_of_dvd _ (by decide : 8∣32)] at h
  exact h odd

/-- Complete blocks each supply exactly two or four terms. Only one final block
can be partial. This function counts lane entries by their position and block. -/
noncomputable def kept (n l count : ℕ) := (range count).filter fun i => i%32∈offsets (n%32) (l%32)

theorem block_bounds (n l count : ℕ) :
    (count/32)*(offsets (n%32) (l%32)).card ≤ (kept n l count).card ∧
    (kept n l count).card ≤ ((count+31)/32)*(offsets (n%32) (l%32)).card := by
  let M := offsets (n%32) (l%32)
  have pack : ((range (count/32)) ×ˢ M).card ≤ (kept n l count).card := by
    apply card_le_card_of_injOn (fun z : ℕ×ℕ => 32*z.1+z.2)
    · intro z hz
      obtain ⟨hq,hr⟩ := mem_product.mp hz
      have r := mem_range.mp (mem_filter.mp hr).1
      have q := mem_range.mp hq
      apply mem_filter.mpr
      exact ⟨mem_range.mpr (by omega),by simpa [Nat.mul_add_mod,Nat.mod_eq_of_lt r] using hr⟩
    · intro a ha b hb e
      have ar := mem_range.mp (mem_filter.mp (mem_product.mp ha).2).1
      have br := mem_range.mp (mem_filter.mp (mem_product.mp hb).2).1
      apply Prod.ext <;> dsimp only at * <;> omega
  have unpack : (kept n l count).card ≤ ((range ((count+31)/32)) ×ˢ M).card := by
    apply card_le_card_of_injOn (fun i : ℕ => (i/32,i%32))
    · intro i hi
      obtain ⟨ic,im⟩ := mem_filter.mp hi
      exact mem_product.mpr ⟨mem_range.mpr (by have := mem_range.mp ic; omega),im⟩
    · intro a _ b _ h
      have q := congrArg Prod.fst h
      have r := congrArg Prod.snd h
      dsimp only at q r
      omega
  simpa only [card_product,card_range,M] using And.intro pack unpack

theorem true_offset {p q l count : ℕ} (po : p%2=1) (qo : q%2=1)
    (start : l≤p+q) (stop : p+q-l<count) : p+q-l ∈ kept (p*q) l count := by
  have allowed := true_residue po qo
  have sum : l+(p+q-l)=p+q := by omega
  apply mem_filter.mpr
  refine ⟨mem_range.mpr stop, mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (by decide)),?_⟩⟩
  rwa [←Nat.add_mod, sum]

set_option exponentiation.threshold 4096 in
/-- Even this exact low-word filter leaves more positions than direct evaluation
can afford. At most four lanes cover every survivor of its 32-wheel. -/
theorem full_size_count {n l count : ℕ} (bits : 2^2047≤n) (odd : n%2=1)
    (span : (9*n/2).sqrt-ceilSqrt (4*n)<count) :
    2^1016 ≤ (kept n l count).card ∧ (kept n l count).card ≤ 4*((count+31)/32) := by
  have lo := (block_bounds n l count).1
  have hi := (block_bounds n l count).2
  rw [offset_count odd] at lo hi
  have width := GeometricDoubleMatch.width_at_2048 bits
  split_ifs at lo hi <;> constructor <;> omega

set_option exponentiation.threshold 4096 in
/-- A full blocked evaluation with at most four lanes and one partial block per
lane still needs a very large block degree or a very large number of points. -/
theorem block_cost {keptCount degree points : ℕ} (many : 2^1016 ≤ keptCount)
    (covers : keptCount ≤ 4*(degree*(points+1))) : 2^507 ≤ max degree (points+1) := by
  by_contra! low
  have d := (le_max_left degree (points+1)).trans_lt low
  have p := (le_max_right degree (points+1)).trans_lt low
  have product := Nat.mul_lt_mul_of_lt_of_le d p.le (by positivity)
  have hi : 4*degree*(points+1)<4*(2^507*2^507) := by
    rw [Nat.mul_assoc]; exact Nat.mul_lt_mul_of_pos_left product (by decide)
  have power : 4*((2:ℕ)^507*2^507)=2^1016 := by decide +kernel
  rw [Nat.mul_assoc,power] at hi
  omega

/-- On a retained progression the same product-side target identifies the
index in that progression. The geometric base is raised to the public stride. -/
theorem true_lane {p q L stride j : ℕ} (hp : p.Prime) (hq : q.Prime) (ne : p≠q)
    (u : (ZMod (p*q))ˣ) (index : L+stride*j=p+q) (early : L≤p*q+1) :
    (u^stride)^j=u^(p*q+1-L) := by
  apply mul_left_cancel (a:=u^L)
  rw [←pow_mul,←pow_add,index,←pow_add,Nat.add_sub_of_le early,unit_pow_factorSum hp hq ne]

end PrimeFactors.GeometricSumLanes
