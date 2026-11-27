import PrimeFactors.ReciprocalFloorPrefixes
import Mathlib.Tactic.NormNum.Prime

/-! The small-denominator quotient tables at two neighboring inputs differ
by a single exchange at a semiprime. Their ranks have an isolated discrepancy. -/
namespace PrimeFactors.AdjacentQuotientSets

open Finset

/-- Proper denominators in the chosen initial interval. -/
noncomputable def keys (n H : ℕ) : Finset ℕ := (Icc 2 H).image (n/·)

private theorem smaller_divisor {p q k H : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p≤q)
    (cut : H≤(p*q).sqrt) (mem : k∈Icc 2 H) (hd : k∣p*q) : k=p := by
  obtain ⟨b,hb⟩ := hd
  obtain ⟨lo,hi⟩ := mem_Icc.mp mem
  have kp : 0<k := by omega
  have sq := Nat.le_sqrt.mp (hi.trans cut)
  rw [hb] at sq
  exact (ordered_semiprime_pair_unique hp hq ord ((Nat.mul_le_mul_left_iff kp).mp sq)
    (by omega) hb.symm).1

private theorem unchanged {p q k H : ℕ} (hp : p.Prime) (hq : q.Prime) (ord : p≤q)
    (cut : H≤(p*q).sqrt) (mem : k∈Icc 2 H) (ne : k≠p) :
    p*q/k=(p*q-1)/k := by
  have nd : ¬k∣p*q := fun d => ne (smaller_divisor hp hq ord cut mem d)
  have zero := ReciprocalFloorPrefixes.jump_eq (Nat.mul_pos hp.pos hq.pos) k
  rw [if_neg nd] at zero
  change p*q/k-(p*q-1)/k=0 at zero
  exact le_antisymm (Nat.le_of_sub_eq_zero zero) (Nat.div_le_div_right (Nat.sub_le ..))

private theorem away {p q k : ℕ} (pp : 0<p) (kp : 0<k) (gap : p+2≤q) (ne : k≠p) :
    p*q/k<q-1 ∨ q<p*q/k := by
  rcases lt_or_gt_of_ne ne with low|high
  · right
    apply (Nat.le_div_iff_mul_le kp).mpr
    nlinarith only [Nat.mul_le_mul_left q (Nat.succ_le_iff.mpr low),low.trans_le (by omega : p≤q)]
  · left
    apply (Nat.div_lt_iff_lt_mul kp).mpr
    have eq : q-1+1=q := by omega
    have mul := Nat.mul_le_mul_left (q-1) (Nat.succ_le_iff.mpr high)
    nlinarith only [mul,congrArg (fun u => p*u) eq,gap,eq]

/-- All common values are in C. The only new key at N is the larger
prime q and the only lost key is q−1. -/
theorem exchange {p q H : ℕ} (hp : p.Prime) (hq : q.Prime) (gap : p+2≤q)
    (start : p≤H) (cut : H≤(p*q).sqrt) :
    ∃ C : Finset ℕ, q∉C ∧ q-1∉C ∧
      keys (p*q) H=insert q C ∧ keys (p*q-1) H=insert (q-1) C := by
  let I := Icc 2 H
  let C := (I.erase p).image (p*q/·)
  have pin : p∈I := mem_Icc.mpr ⟨hp.two_le,start⟩
  have val : p*q/p=q := Nat.mul_div_cancel_left _ hp.pos
  have prev : (p*q-1)/p=q-1 := by
    have j := ReciprocalFloorPrefixes.jump_eq (Nat.mul_pos hp.pos hq.pos) p
    rw [if_pos (dvd_mul_right ..)] at j
    change p*q/p-(p*q-1)/p=1 at j
    rw [val] at j
    omega
  have all (k : ℕ) (hk : k∈I.erase p) : p*q/k<q-1 ∨ q<p*q/k := by
    have lo : 2≤k := (mem_Icc.mp (mem_erase.mp hk).2).1
    exact away hp.pos (by omega) gap (mem_erase.mp hk).1
  have missing : q∉C ∧ q-1∉C := by
    constructor <;> intro h <;> obtain ⟨k,hk,eq⟩ := mem_image.mp h <;> specialize all k hk <;> omega
  have eq' : (I.erase p).image ((p*q-1)/·)=C := by
    apply image_congr
    intro k hk
    obtain ⟨ne,mem⟩ := mem_erase.mp hk
    exact (unchanged hp hq (by omega) cut mem ne).symm
  refine ⟨C,missing.1,missing.2,?_,?_⟩
  · change I.image _=_
    rw [←insert_erase pin,image_insert,val]
  · change I.image _=_
    rw [←insert_erase pin,image_insert,prev,eq']

/-- A high-label suffix rank is bigger for N exactly at threshold q. -/
theorem rank_jump {p q H : ℕ} (hp : p.Prime) (hq : q.Prime) (gap : p+2≤q)
    (start : p≤H) (cut : H≤(p*q).sqrt) (y : ℕ) :
    ((keys (p*q) H).filter (y≤·)).card =
      ((keys (p*q-1) H).filter (y≤·)).card + (if y=q then 1 else 0) := by
  obtain ⟨C,high,low,a,b⟩ := exchange hp hq gap start cut
  rw [a,b,filter_insert,filter_insert]
  have h₁ : q∉C.filter (y≤·) := fun h => high (mem_filter.mp h).1
  have h₂ : q-1∉C.filter (y≤·) := fun h => low (mem_filter.mp h).1
  split_ifs <;> (try simp only [card_insert_of_not_mem h₁,card_insert_of_not_mem h₂]) <;> omega

private theorem div_strict {n i j : ℕ} (ip : 0 < i) (lt : i < j) (size : j*j≤n) :
    n/j < n / i := by
  have jp : 0 < j := ip.trans lt
  have large := (Nat.le_div_iff_mul_le jp).mpr size
  have gap := Nat.mul_le_mul_left (n/j) (Nat.succ_le_iff.mpr lt)
  have fit := Nat.div_mul_le_self n j
  apply (Nat.le_div_iff_mul_le ip).mpr
  nlinarith only [large,gap,fit,lt]

/-- Computing each rank separately needs one division, a minimum and a
subtraction. This does not supply the unknown threshold where they differ. -/
theorem rank {n H y : ℕ} (size : H*H≤n) (yp : 0<y) :
    ((keys n H).filter (y≤·)).card=min H (n/y)-1 := by
  rw [keys,filter_image]
  have indices : (Icc 2 H).filter (fun k : ℕ => y≤n/k)=Icc 2 (min H (n/y)) := by
    ext k
    simp only [mem_filter,mem_Icc,le_min_iff]
    by_cases lo : 2≤k
    · have kp : 0<k := by omega
      rw [Nat.le_div_iff_mul_le kp,Nat.le_div_iff_mul_le yp,mul_comm y k]
      tauto
    · tauto
  rw [indices,card_image_of_injOn]
  · rw [Nat.card_Icc]
    omega
  · intro i hi j hj eq
    change n / i = n / j at eq
    obtain ⟨ilo,ihi⟩ := mem_Icc.mp hi
    obtain ⟨jlo,jhi⟩ := mem_Icc.mp hj
    have fi := (le_min_iff.mp ihi).1
    have fj := (le_min_iff.mp jhi).1
    rcases lt_trichotomy i j with l|l|l
    · have := div_strict (by omega : 0 < i) l ((Nat.mul_le_mul fj fj).trans size)
      omega
    · exact l
    · have := div_strict (by omega : 0 < j) l ((Nat.mul_le_mul fi fi).trans size)
      omega

/-- The large states of a grouped summatory recursion consist of the root
and the proper quotient keys above its table of values 0,…,H. -/
noncomputable def states (n H : ℕ) : Finset ℕ := insert n ((keys n H).filter (H<·))

private theorem proper_small {n H k : ℕ} (hn : 4≤n) (hk : k∈keys n H) : k<n-1 := by
  obtain ⟨i,mem,rfl⟩ := mem_image.mp hk
  have il : 2 ≤ i := (mem_Icc.mp mem).1
  change n / i < n-1
  have upper := Nat.div_le_div_left il (by decide : 0<2) (a:=n)
  omega

/-- With a shared square-root base table, the second root and q−1 are the
only new large states when moving from N to N−1. -/
theorem two_new_states {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (gap : p+2≤q) :
    let N := p*q
    let H := N.sqrt
    states (N-1) H \ states N H = {N-1,q-1} := by
  let N := p*q
  let H := N.sqrt
  have pp := hp.two_le
  have qp := hq.two_le
  have four : 4≤N := Nat.mul_le_mul pp qp
  have start : p≤H := Nat.le_sqrt.mpr (Nat.mul_le_mul_left p (by omega))
  have hi : H<q-1 := by
    apply Nat.lt_of_not_ge
    intro bad
    have h := Nat.le_sqrt.mp bad
    change (q-1)*(q-1)≤p*q at h
    have eq : q-1+1=q := by omega
    nlinarith only [h,eq,congrArg (fun a => a*(q-1)) eq,
      Nat.mul_le_mul_right q gap]
  obtain ⟨C,cq,cm,first,prev⟩ := exchange hp hq gap start (H:=H) le_rfl
  have small (z : ℕ) (hz : z∈C) : z<N-1 :=
    proper_small four (first ▸ mem_insert_of_mem hz : z∈keys N H)
  have big : q<N-1 := by
    have h := Nat.mul_le_mul_right q pp
    change q<p*q-1
    omega
  change (insert (N-1) ((keys (N-1) H).filter (H<·))) \
      (insert N ((keys N H).filter (H<·))) = _
  change keys N H=insert q C at first
  change keys (N-1) H=insert (q-1) C at prev
  rw [first,prev]
  ext z
  simp only [mem_sdiff,mem_insert,mem_singleton,mem_filter]
  by_cases hz : z∈C
  · have := small z hz
    have nz : z ≠ q-1 := fun eq => cm (eq ▸ hz)
    simp only [hz,or_true,true_and]
    omega
  · simp only [hz,or_false]
    omega

set_option exponentiation.threshold 2050 in
/-- Even with all first-call memoized values supplied, the grouped root
loop at N−1 has at least 2^1023−1 distinct quotient blocks at full width. -/
theorem full_size_root_blocks {N : ℕ} (width : 2^2047≤N) :
    2^1023-1 ≤ (keys (N-1) (N-1)).card := by
  let H : ℕ := 2^1023
  have sq : H*H≤N-1 := by
    have h : (2:ℕ)^1023*2^1023<2^2047 := by
      rw [←pow_add]
      exact Nat.pow_lt_pow_right (by decide) (by decide)
    change 2^1023*2^1023≤N-1
    omega
  have lo : H≤N-1 :=
    (Nat.le_mul_of_pos_left H (by dsimp only [H]; positivity)).trans sq
  have size := rank (y:=1) sq (by decide)
  rw [Nat.div_one,min_eq_left lo] at size
  change H-1≤_
  rw [←size]
  apply card_le_card
  intro z hz
  obtain ⟨k,hk,eq⟩ := mem_image.mp (mem_filter.mp hz).1
  obtain ⟨kl,ku⟩ := mem_Icc.mp hk
  exact mem_image.mpr ⟨k,mem_Icc.mpr ⟨kl,ku.trans lo⟩,eq⟩

/-- Each measured comparison product consists of its two stated primes. -/
theorem comparison_factors :
    (137:ℕ).Prime ∧ (251:ℕ).Prime ∧ 137*251=34387 ∧
    (269:ℕ).Prime ∧ (491:ℕ).Prime ∧ 269*491=132079 ∧
    (1811:ℕ).Prime ∧ (2011:ℕ).Prime ∧ 1811*2011=3641921 ∧
    (6827:ℕ).Prime ∧ (7307:ℕ).Prime ∧ 6827*7307=49884889 := by
  norm_num

end PrimeFactors.AdjacentQuotientSets
