import PrimeFactors.TwoMaximalClueSuffixes

/-! Keep the odd product fixed and vary the supplied odd suffix. The
frequencies here give each length-k suffix one vote. -/
namespace PrimeFactors.FixedProductClueTails

open Finset DyadicFactorClueGain
open private PrimeFactors.DyadicFactorClueGain.one_class from PrimeFactors.DyadicFactorClueGain
open private PrimeFactors.TwoMaximalClueSuffixes.root_signs from PrimeFactors.TwoMaximalClueSuffixes
open private PrimeFactors.LocalMidpointLanes.odd_square from PrimeFactors.LocalMidpointLanes

noncomputable def suffixes (k : ℕ) := (range (2^k)).filter Odd
noncomputable def tail (k N j : ℕ) := (suffixes k).filter (fun a => j≤extra k a N)

theorem suffixes_card {k : ℕ} (hk : 1≤k) : (suffixes k).card=2^(k-1) := by
  have defn : suffixes k=(range (2^k)).filter (fun a => a ≡ 1 [MOD 2^1]) := by
    ext a
    simp only [suffixes,mem_filter,mem_range,Nat.odd_iff,Nat.ModEq,pow_one]
  rw [defn,PrimeFactors.DyadicFactorClueGain.one_class hk]

private theorem criterion {k N a j : ℕ} (hk : 1≤k) (le : j≤k+1) (odd : Odd a) :
    j≤extra k a N ↔ N ≡ a^2+2^k [MOD 2^j] := by
  rw [extra_iff hk, and_iff_right le]
  obtain ⟨v,hv⟩ := odd
  have term : a*2^k ≡ 2^k [MOD 2^(k+1)] := by
    rw [show a*2^k=2^k+v*2^(k+1) by rw [hv,pow_succ]; ring]
    simp [Nat.ModEq]
  have shift := (term.of_dvd (pow_dvd_pow 2 le)).add_left (a^2)
  exact ⟨fun h => h.trans shift,fun h => h.trans shift.symm⟩

private theorem low_bits {k N a j : ℕ} (hk : 3≤k) (low : j≤3) (odd : Odd a) :
    j≤extra k a N ↔ N ≡ 1 [MOD 2^j] := by
  rw [criterion (by omega) (by omega) odd]
  have sqZ := PrimeFactors.LocalMidpointLanes.odd_square (by exact_mod_cast odd : Odd (a:ℤ))
  have sq : a^2 ≡ 1 [MOD 8] := by
    apply Int.natCast_modEq_iff.mp
    push_cast
    exact (Int.modEq_iff_dvd.mpr sqZ).symm
  have vanish := Nat.modEq_zero_iff_dvd.mpr (pow_dvd_pow (2:ℕ) (low.trans hk))
  have rhs : a^2+2^k ≡ 1 [MOD 2^j] := by
    simpa only [add_zero] using (sq.of_dvd (show 2^j∣8 from pow_dvd_pow 2 low)).add vanish
  exact ⟨fun h => h.trans rhs,fun h => h.trans rhs.symm⟩

/-- For three of the four odd residues modulo eight the gain is constant.
The remaining class always gains at least three bits. -/
theorem gains_by_residue {k a N : ℕ} (hk : 3≤k) (odd : Odd a) :
    ((N%8=3 ∨ N%8=7) → extra k a N=1) ∧
    (N%8=5 → extra k a N=2) ∧ (N%8=1 → 3≤extra k a N) := by
  have one : 1≤extra k a N ↔ N%2=1 := low_bits hk (by decide) odd
  have two : 2≤extra k a N ↔ N%4=1 := low_bits hk (by decide) odd
  have three : 3≤extra k a N ↔ N%8=1 := low_bits hk (by decide) odd
  omega

private theorem odd_of_class {a r t : ℕ} (tp : 0<t) (rr : Odd r) (h : a ≡ r [MOD 2^t]) : Odd a :=
  Nat.odd_iff.mpr ((show a%2=r%2 from h.of_dvd (dvd_pow_self 2 tp.ne')).trans (Nat.odd_iff.mp rr))

private theorem classes {k t N : ℕ} (hk : 3≤k) (lo : 2≤t) (hi : t≤k) (good : N%8=1) :
    ∃ r s : ℕ, Odd r ∧ Odd s ∧ ¬r ≡ s [MOD 2^t] ∧
      ∀ a : ℕ, Odd a → (t+1≤extra k a N ↔ a ≡ r [MOD 2^t] ∨ a ≡ s [MOD 2^t]) := by
  obtain ⟨r,s,_,op,menu⟩ := TwoMaximalClueSuffixes.opposite_pair hk good
  have rm : r∈TwoMaximalClueSuffixes.menu k N := menu ▸ mem_insert_self ..
  have sm : s∈TwoMaximalClueSuffixes.menu k N := menu ▸ mem_insert_of_mem (mem_singleton_self _)
  have unit {b : ℕ} (h : b∈TwoMaximalClueSuffixes.menu k N) :=
    ((TwoMaximalClueSuffixes.mem_maximum (by omega) (Nat.odd_iff.mpr (by omega))).mp h).2.1
  have ro := unit rm
  have so := unit sm
  have root := (TwoMaximalClueSuffixes.mem_square.mp rm).2.of_dvd
    (pow_dvd_pow (2:ℤ) (by omega : t+1≤k+1))
  have flip : (s:ℤ) ≡ -(r:ℤ) [ZMOD (2:ℤ)^t] := by
    simpa using (op.of_dvd (pow_dvd_pow (2:ℤ) hi)).add_left (-(r:ℤ))
  refine ⟨r,s,ro,so,?_,?_⟩
  · intro same
    have cast : (r:ℤ) ≡ (s:ℤ) [ZMOD (2:ℤ)^t] := by exact_mod_cast Int.natCast_modEq_iff.mpr same
    have four := (cast.trans flip).of_dvd (show (4:ℤ)∣(2:ℤ)^t from pow_dvd_pow 2 lo)
    change (r:ℤ)%4=(-(r:ℤ))%4 at four
    obtain ⟨v,eq⟩ := ro
    omega
  · intro a ao
    rw [criterion (by omega) (by omega) ao,←Int.natCast_modEq_iff]
    push_cast
    have shift : (N:ℤ) ≡ a^2+2^k [ZMOD (2:ℤ)^(t+1)] ↔
        (a:ℤ)^2 ≡ (N:ℤ)-2^k [ZMOD (2:ℤ)^(t+1)] := by
      rw [Int.modEq_iff_dvd,Int.modEq_iff_dvd,
        show (N:ℤ)-2^k-a^2 = -(a^2+2^k-N) by ring,Int.dvd_neg]
    rw [shift]
    have center : (a:ℤ)^2 ≡ (N:ℤ)-2^k [ZMOD (2:ℤ)^(t+1)] ↔
        (a:ℤ)^2 ≡ (r:ℤ)^2 [ZMOD (2:ℤ)^(t+1)] :=
      ⟨fun h => h.trans root.symm,fun h => h.trans root⟩
    rw [center,PrimeFactors.TwoMaximalClueSuffixes.root_signs (by omega) _ _ (by exact_mod_cast ro)]
    have cast (b : ℕ) : (a:ℤ) ≡ (b:ℤ) [ZMOD (2:ℤ)^t] ↔ a ≡ b [MOD 2^t] := by
      exact_mod_cast Int.natCast_modEq_iff (a:=a) (b:=b) (n:=2^t)
    exact or_congr (cast r) ((Iff.intro (fun h => h.trans flip.symm) (fun h => h.trans flip)).trans (cast s))

/-- On the one-mod-eight branch, there are exactly two classes modulo
2^(j−1) at every level j from three through the upper endpoint. -/
theorem tail_one_mod_eight {k N j : ℕ} (hk : 3≤k) (good : N%8=1)
    (low : 3≤j) (high : j≤k+1) : (tail k N j).card=2^(k+2-j) := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
  have le : t≤k := by omega
  obtain ⟨r,s,ro,so,apart,hit⟩ := classes hk (by omega) le good
  let C (u : ℕ) := (range (2^k)).filter (fun a => a ≡ u [MOD 2^t])
  have sets : tail k N (t+1)=C r ∪ C s := by
    ext a
    simp only [tail,suffixes,C,mem_filter,mem_range,mem_union]
    constructor
    · rintro ⟨⟨size,unit⟩,pass⟩
      exact ((hit a unit).mp pass).elim (fun l => Or.inl ⟨size,l⟩) (fun r => Or.inr ⟨size,r⟩)
    · rintro (⟨size,l⟩|⟨size,r⟩)
      · have unit := odd_of_class (by omega) ro l
        exact ⟨⟨size,unit⟩,(hit a unit).mpr (Or.inl l)⟩
      · have unit := odd_of_class (by omega) so r
        exact ⟨⟨size,unit⟩,(hit a unit).mpr (Or.inr r)⟩
  have dis : Disjoint (C r) (C s) := disjoint_left.mpr (fun _ l r =>
    apart ((Nat.ModEq.symm (mem_filter.mp l).2).trans (mem_filter.mp r).2))
  rw [sets,card_union_of_disjoint dis]
  change ((range _).filter _).card+((range _).filter _).card=_
  rw [PrimeFactors.DyadicFactorClueGain.one_class le,PrimeFactors.DyadicFactorClueGain.one_class le,
    show k+2-(t+1)=k-t+1 by omega,pow_succ,Nat.mul_two]

/-- Exact histogram below the upper endpoint, obtained by differencing
successive tails. The endpoint itself has two suffixes. -/
theorem exact_one_mod_eight {k N j : ℕ} (hk : 3≤k) (good : N%8=1)
    (low : 3≤j) (high : j≤k) :
    ((suffixes k).filter (fun a => extra k a N=j)).card=2^(k+1-j) := by
  let exactSet := (suffixes k).filter (fun a => extra k a N=j)
  have split : tail k N j=exactSet ∪ tail k N (j+1) := by
    ext a
    simp only [tail,exactSet,mem_filter,mem_union]
    by_cases mem : a∈suffixes k
    · simp only [mem,true_and]
      omega
    · simp [mem]
  have dis : Disjoint exactSet (tail k N (j+1)) := disjoint_left.mpr (fun _ l r =>
    (not_le_of_gt (Nat.lt_succ_self j)) ((mem_filter.mp l).2 ▸ (mem_filter.mp r).2))
  have counts := congrArg card split
  rw [tail_one_mod_eight hk good low (by omega),card_union_of_disjoint dis,
    tail_one_mod_eight hk good (by omega) (by omega),show k+2-(j+1)=k+1-j by omega,
    show k+2-j=k+1-j+1 by omega,pow_succ] at counts
  change exactSet.card=_
  omega

private theorem shifted_geom (n : ℕ) : (∑ i∈range n,(2:ℕ)^(n-i))=2^(n+1)-2 := by
  have geometric : (∑ i∈range n,(2:ℕ)^i)=2^n-1 := by
    simpa using geom_sum_mul_of_one_le (by decide : 1≤(2:ℕ)) n
  calc
    _ = (∑ i∈range n,2^(n-1-i))*2 := by
      rw [sum_mul]
      apply sum_congr rfl
      intro i hi
      rw [show n-i=(n-1-i)+1 by have := mem_range.mp hi; omega,pow_succ]
    _ = (∑ i∈range n,2^i)*2 := by rw [sum_range_reflect (fun i => (2:ℕ)^i)]
    _ = _ := by rw [geometric,pow_succ]; have := Nat.one_le_two_pow (n:=n); omega

/-- Exact total and hence the first moment at a fixed product that is one
modulo eight. The top two suffixes are included with their actual gain. -/
theorem total_one_mod_eight {k N : ℕ} (hk : 3≤k) (good : N%8=1) :
    (∑ a∈suffixes k,extra k a N)=2^(k+1)-2 := by
  have decompose (a : ℕ) (mem : a∈suffixes k) :
      extra k a N=2+∑ i∈range (k-1),if i+3≤extra k a N then 1 else 0 := by
    have bottom := (gains_by_residue hk (mem_filter.mp mem).2).2.2 good
    have top := ((extra_iff (by omega : 1≤k) a N _).mp (le_refl _)).1
    have eq : (range (k-1)).filter (fun i => i+3≤extra k a N)=range (extra k a N-2) := by
      ext i
      simp only [mem_range,mem_filter]
      omega
    rw [sum_boole,eq,card_range,Nat.cast_id]
    omega
  calc
    _ = ∑ a∈suffixes k,(2+∑ i∈range (k-1),if i+3≤extra k a N then 1 else 0) :=
      sum_congr rfl decompose
    _ = (suffixes k).card*2+∑ i∈range (k-1),(tail k N (i+3)).card := by
      rw [sum_add_distrib,sum_comm (s:=suffixes k) (t:=range (k-1))]
      simp only [tail,sum_boole,Nat.cast_id,sum_const,nsmul_eq_mul]
    _ = 2^(k-1)*2+∑ i∈range (k-1),2^(k-1-i) := by
      rw [suffixes_card (by omega)]
      congr 1
      apply sum_congr rfl
      intro i hi
      have := mem_range.mp hi
      rw [tail_one_mod_eight hk good (by omega) (by omega)]
      congr 1
      omega
    _ = _ := by
      rw [shifted_geom,show k-1+1=k by omega,←pow_succ,show k-1+1=k by omega,pow_succ]
      have := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 1≤k)
      omega

theorem mean_one_mod_eight {k N : ℕ} (hk : 3≤k) (good : N%8=1) :
    ((∑ a∈suffixes k,extra k a N : ℕ):ℚ)/(suffixes k).card=4-2/(2:ℚ)^(k-1) := by
  have pos : 2≤(2:ℕ)^(k+1) := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 1≤k+1)
  rw [total_one_mod_eight hk good,suffixes_card (by omega),Nat.cast_sub pos,
    show k+1=k-1+2 by omega,pow_add]
  push_cast
  field_simp
  ring

end PrimeFactors.FixedProductClueTails
