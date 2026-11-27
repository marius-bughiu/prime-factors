import PrimeFactors.HighWordSumRanking
import PrimeFactors.HighWordSuffixTransfer

/-! Ranking the even sums of sorted odd factor pairs from the high word
and the residue of their product. -/

namespace PrimeFactors.HighWordSuffixRanking

open HighWordSumRanking Finset

/-- Half-gaps in the chosen row passing a specified test on residue classes. -/
noncomputable def options (x B n w P : ℕ) (accept : ℕ→ℕ→Bool) (u : ℕ) : Finset ℕ :=
  (gaps x B n w u).filter fun v => accept (u%P) (v%P)

/-- Integer arithmetic linking the first row in a class to the uniform
radical separation argument. -/
private theorem bounds {B P n w r u₀ u : ℕ} (above : n+w<r^2)
    (below : (r-1)^2<n+w) (step : B≤2*r+1) (lo : r≤u₀) (early : u₀<r+P)
    (later : u₀+P≤u) (fit : u<B) :
    n+w<u₀^2 ∧ u₀^2-(n+w)≤2*(B*P) ∧ u₀^2-(n+w)+B*P≤u^2-(n+w) := by
  have up := Nat.pow_le_pow_left lo 2
  have rup : 0<r := by by_contra! h; have := Nat.eq_zero_of_le_zero h; simp_all
  have rpred : r-1+1=r := by omega
  let displacement := u₀-(r-1)
  have gap : u₀=(r-1)+displacement := by dsimp [displacement]; omega
  have m1 := Nat.mul_le_mul (show displacement≤P by omega) (show u₀+(r-1)≤2*B by omega)
  have id : displacement*(u₀+(r-1))+(r-1)^2=u₀^2 := by rw [gap]; ring
  have close : u₀^2≤n+w+2*(B*P) := by nlinarith only [id,m1,below]
  have move := Nat.pow_le_pow_left later 2
  have gain := Nat.mul_le_mul (show B≤2*u₀+P by omega) (le_refl P)
  have span : u₀^2+B*P≤u^2 := by nlinarith only [move,gain]
  omega

private theorem unclipped {x B n w r u P : ℕ} (pp : 0<P) (evenP : 2∣P)
    (align : P∣u-r) (ord : r≤u) (fit : r<B) (lower : x≤r) (above : n+w<r^2)
    (noclip : r^2<n+(min (r-x) (B-1-r))^2)
    (drop : Real.sqrt ((u^2-n:ℕ):ℝ)-Real.sqrt ((u^2-(n+w):ℕ):ℝ)+(P:ℝ)≤
      Real.sqrt ((r^2-n:ℕ):ℝ)-Real.sqrt ((r^2-(n+w):ℕ):ℝ)) :
    ∃ D : ℕ, P∣D ∧ ∀ v∈gaps x B n w u, D≤v ∧ v-D∈gaps x B n w r := by
  have su := Nat.pow_le_pow_left ord 2
  have ordR := Real.sqrt_le_sqrt (show (((r^2-(n+w):ℕ):ℝ))≤((u^2-(n+w):ℕ):ℝ) by
    exact_mod_cast (show r^2-(n+w)≤u^2-(n+w) by omega))
  obtain ⟨D,dper,all⟩ := HighWordSuffixTransfer.shift pp (Real.sqrt_nonneg _) ordR drop
  refine ⟨D,dper,?_⟩
  intro v hv
  obtain ⟨_,_,_,vlo,vhi,vpar⟩ := mem_gaps.mp hv
  have rsq : 0<r^2-(n+w) := by omega
  have l1 : Real.sqrt ((u^2-(n+w):ℕ):ℝ)≤v := root_down.mpr (by omega)
  have h1 : (v:ℝ)≤Real.sqrt ((u^2-n:ℕ):ℝ) := root_up.mpr (by omega)
  obtain ⟨dv,lo,hi⟩ := all v l1 h1
  have pos : 0<((v-D:ℕ):ℝ) := lt_of_lt_of_le (Real.sqrt_pos.mpr (by exact_mod_cast rsq)) lo
  have vlo0 := root_down.mp lo
  have vhi0 := root_up.mp hi
  have clip : v-D≤min (r-x) (B-1-r) := by
    by_contra! bad
    have far := Nat.pow_le_pow_left bad.le 2
    omega
  have l := (le_min_iff.mp clip).1
  have h := (le_min_iff.mp clip).2
  have de : (v-D)%2=v%2 := HighWordSuffixTransfer.sub_mod (evenP.trans dper) dv
  have ue : (u-(u-r))%2=u%2 := HighWordSuffixTransfer.sub_mod (evenP.trans align) (show u-r≤u by omega)
  have red : u-(u-r)=r := by omega
  rw [red] at ue
  refine ⟨dv,mem_gaps.mpr ⟨by exact_mod_cast pos,by omega,by omega,by omega,by omega,by omega⟩⟩

/-- Every suffix predicate periodic in the midpoint and half-gap has at
least as many admissible (integer) pairs in the first row of its class. -/
theorem same_class {B P n w r u₀ u : ℕ} (accept : ℕ→ℕ→Bool) (pp : 0<P) (evenP : 2∣P)
    (large : 4096*P^3≤B) (word : w+1=B) (above : n+w<r^2) (below : (r-1)^2<n+w)
    (step : B≤2*r+1) (lo : r≤u₀) (early : u₀<r+P) (ord : u₀≤u) (align : P∣u-u₀) :
    (options (B/2) B n w P accept u).card≤(options (B/2) B n w P accept u₀).card := by
  by_cases eq : u₀=u
  · subst u; rfl
  by_cases live : (gaps (B/2) B n w u).Nonempty
  · obtain ⟨v,hv⟩ := live
    have liveBound := (mem_gaps.mp hv).2.2.1
    have fit : u<B := by omega
    have later : u₀+P≤u := by
      have := Nat.le_of_dvd (show 0<u-u₀ by omega) align
      omega
    obtain ⟨first,close,move⟩ := bounds above below step lo early later fit
    obtain ⟨D,dp,all⟩ : ∃ D : ℕ, P∣D ∧ ∀ v∈gaps (B/2) B n w u, D≤v ∧ v-D∈gaps (B/2) B n w u₀ := by
      by_cases clipped : n+(min (u₀-B/2) (B-1-u₀))^2≤u₀^2
      · refine ⟨u-u₀,align,?_⟩
        intro z hz
        have cap := (mem_gaps.mp hz).2.2.2.2.1
        have zz : u=u₀+(u-u₀) := by omega
        have bound : u-u₀≤z := by
          by_contra! bad
          have far := Nat.pow_le_pow_left bad.le 2
          rw [zz] at cap
          nlinarith only [far,cap,first,Nat.zero_le (u₀*(u-u₀))]
        obtain ⟨_,xmin,mid,_,share,par⟩ := mem_gaps.mp hz
        have clip := Nat.le_sqrt'.mpr (show (min (u₀-B/2) (B-1-u₀))^2≤u₀^2-n by omega)
        obtain ⟨zp,zx,zB,zlo,zhi,zpar⟩ := clip_map ord first mid xmin share clip (by omega)
        exact ⟨bound,mem_gaps.mpr ⟨zp,zx,zB,zlo,zhi,zpar par⟩⟩
      · apply unclipped pp evenP align ord (by omega) (by omega) first (lt_of_not_ge clipped)
        have firstsq := Nat.pow_le_pow_left ord 2
        have ra : u₀^2-n=u₀^2-(n+w)+w := by omega
        have ua : u^2-n=u^2-(n+w)+w := by omega
        rw [ra,ua,Nat.cast_add,Nat.cast_add]
        apply HighWordSuffixTransfer.later (B:=(B:ℝ)) (P:=(P:ℝ)) (by exact_mod_cast pp) (by exact_mod_cast large) _ _ (by positivity) (by exact_mod_cast close) (by exact_mod_cast move)
        · have tw : B≤2*w := by have := Nat.one_le_pow 3 P pp; omega
          exact (div_le_iff₀ (by norm_num)).mpr (by exact_mod_cast (show B≤w*2 by omega))
        · exact_mod_cast (show w≤B by omega)
    have mids : (u-(u-u₀))%P=u%P := HighWordSuffixTransfer.sub_mod align (show u-u₀≤u by omega)
    rw [show u-(u-u₀)=u₀ by omega] at mids
    apply Finset.card_le_card_of_injOn (fun z => z-D)
    · intro z hz
      obtain ⟨raw,cond⟩ := Finset.mem_filter.mp hz
      obtain ⟨zd,keep⟩ := all z raw
      exact Finset.mem_filter.mpr ⟨keep,by rwa [mids, (show (z-D)%P=z%P from HighWordSuffixTransfer.sub_mod dp zd)]⟩
    · intro z hz t ht eqz
      have lz := (all z (Finset.mem_filter.mp hz).1).1
      have lt := (all t (Finset.mem_filter.mp ht).1).1
      change z-D=t-D at eqz
      omega
  · have empty := Finset.not_nonempty_iff_eq_empty.mp live
    simp [options,empty]

/-- For an arbitrary residue predicate, every midpoint is dominated by the
floor square root of the upper word endpoint or one of the first P
consecutive midpoints above it. This concerns integer pairs of equal width. -/
theorem first_block {b h P : ℕ} (size : 14≤b) (lo : 2^b/2≤h) (hi : h<2^b)
    (pp : 0<P) (evenP : 2∣P) (large : 4096*P^3≤2^b) (accept : ℕ→ℕ→Bool) (u : ℕ) :
    let B := 2^b
    let n := B*h
    let w := B-1
    let a := (n+w).sqrt
    let count := fun z => (options (B/2) B n w P accept z).card
    ∃ u₀, (u₀=a ∨ a+1≤u₀ ∧ u₀<a+1+P) ∧ count u≤count u₀ := by
  let B := 2^b
  let n := B*h
  let w := B-1
  let a := (n+w).sqrt
  let count := fun z => (options (B/2) B n w P accept z).card
  change ∃ u₀, (u₀=a ∨ a+1≤u₀ ∧ u₀<a+1+P) ∧ count u≤count u₀
  have frame : HighWordSumRankingBounds.Frame B n (n+w) := HighWordSumRankingBounds.endpoints size lo hi
  by_cases first : u≤a
  · refine ⟨a,Or.inl rfl,?_⟩
    rcases eq_or_lt_of_le first with rfl|small
    · rfl
    · have below := Nat.pow_le_pow_left (show u≤a-1 by omega) 2
      have previous : (a-1)^2<n := frame.prev
      have empty : gaps (B/2) B n w u=∅ := Finset.not_nonempty_iff_eq_empty.mp (by
        rintro ⟨v,hv⟩
        have := (mem_gaps.mp hv).2.2.2.1
        omega)
      simp [count,options,empty]
  · let r := a+1
    let d := u-r
    let u₀ := r+d%P
    have ru : r≤u := by dsimp [r]; omega
    have eqd : u=r+d := by dsimp [d]; omega
    have in0 : r≤u₀ := Nat.le_add_right _ _
    have in1 : u₀<r+P := Nat.add_lt_add_left (Nat.mod_lt _ pp) _
    have ord : u₀≤u := by dsimp [u₀]; have := Nat.mod_le d P; omega
    have align : P∣u-u₀ := by
      refine ⟨d/P,?_⟩
      have := Nat.mod_add_div d P
      dsimp [u₀]; omega
    refine ⟨u₀,Or.inr ⟨in0,in1⟩,?_⟩
    have word : w+1=B := by dsimp [w,B]; have := Nat.two_pow_pos b; omega
    have nonsq : a^2<n+w := by
      by_contra! h
      have alt := PrimeFactors.ceilSqrt_le_iff.mpr h
      rw [frame.ceil_eq] at alt
      change a+1≤a at alt
      omega
    exact same_class accept pp evenP large word frame.above (by simpa [r] using nonsq) frame.space in0 in1 ord align

/-- The public product constraint is a function of these two residues
whenever the suffix modulus divides P. -/
def productSuffix (m σ a v : ℕ) : Bool := decide (a^2%m=(σ+v^2)%m)

theorem mem_suffix {x B n w P m σ u v : ℕ} (part : m∣P) :
    v∈options x B n w P (productSuffix m σ) u ↔
      v∈gaps x B n w u ∧ (u-v)*(u+v)%m=σ%m := by
  have red (s : ℕ) : s%P≡s [MOD P] := Nat.mod_mod _ _
  have ur : (u%P)^2%m=u^2%m := ((red u).of_dvd part).pow 2
  have vr : (σ+(v%P)^2)%m=(σ+v^2)%m := (((red v).of_dvd part).pow 2).add_left σ
  simp only [options,Finset.mem_filter,productSuffix,decide_eq_true_eq,ur,vr]
  apply and_congr_right
  intro hv
  have vu : v≤u := by have := (mem_gaps.mp hv).2.1; omega
  have d : (u-v)*(u+v)+v^2=u^2 := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le vu
    rw [Nat.add_sub_cancel_left]; ring
  constructor
  · exact fun t => Nat.ModEq.add_right_cancel' (v^2) (d ▸ t)
  · exact fun t => d ▸ (Nat.ModEq.add_right (v^2) t)

/-- Sorted distinct odd integer pairs in the original product word and midpoint
row whose product has the observed remainder modulo m. -/
noncomputable def suffixPairs (x B n w m σ u : ℕ) : Finset (ℕ×ℕ) :=
  (pairs x B n w u).filter fun z => z.1*z.2%m=σ%m

/-- Checking the remainder in midpoint and half-gap coordinates counts the
original pairs with that product remainder exactly once. -/
theorem options_card_pairs {P m : ℕ} (part : m∣P) (x B n w σ u : ℕ) :
    (options x B n w P (productSuffix m σ) u).card=(suffixPairs x B n w m σ u).card := by
  have keep : options x B n w P (productSuffix m σ) u =
      (gaps x B n w u).filter (fun v => (u-v)*(u+v)%m=σ%m) := by
    ext v
    simp only [mem_filter]
    exact mem_suffix part
  rw [suffixPairs,pairs_eq_gap_image,filter_image,card_image_of_injective,keep]
  · intro a b eq
    exact Nat.add_left_cancel (congrArg Prod.snd eq)

/-- Some midpoint in the closed block from the floor square root of the word
top through that root plus lcm(2,m) attains the global maximum over all rows.
The population being counted consists of odd integer pairs of the given width. -/
theorem maximum_pairs {b h m : ℕ} (size : 14≤b) (lo : 2^b/2≤h) (hi : h<2^b)
    (mp : 0<m) (large : 4096*(Nat.lcm 2 m)^3≤2^b) (σ : ℕ) :
    let B := 2^b
    let n := B*h
    let w := B-1
    let a := (n+w).sqrt
    let P := Nat.lcm 2 m
    let count := fun u => (suffixPairs (B/2) B n w m σ u).card
    ∃ u₀∈Icc a (a+P), ∀ u, count u≤count u₀ := by
  let B := 2^b
  let n := B*h
  let w := B-1
  let a := (n+w).sqrt
  let P := Nat.lcm 2 m
  let count := fun u => (suffixPairs (B/2) B n w m σ u).card
  change ∃ u₀∈Icc a (a+P), ∀ u, count u≤count u₀
  have pp : 0<P := Nat.lcm_pos (by decide) mp
  have dp : 2∣P := Nat.dvd_lcm_left ..
  have dm : m∣P := Nat.dvd_lcm_right ..
  have first : a∈Icc a (a+P) := mem_Icc.mpr ⟨le_rfl,Nat.le_add_right ..⟩
  obtain ⟨u₀,inside,maximum⟩ := exists_max_image (Icc a (a+P)) count ⟨a,first⟩
  refine ⟨u₀,inside,?_⟩
  intro u
  obtain ⟨t,where',bound⟩ := first_block size lo hi pp dp large (productSuffix m σ) u
  have it : t∈Icc a (a+P) := by
    change t=a ∨ a+1≤t ∧ t<a+1+P at where'
    exact mem_Icc.mpr (by omega)
  change (options (B/2) B n w P (productSuffix m σ) u).card≤
    (options (B/2) B n w P (productSuffix m σ) t).card at bound
  rw [options_card_pairs dm,options_card_pairs dm] at bound
  exact bound.trans (maximum _ it)


/-- With 1,024-bit integers and a product remainder modulo 120,
121 consecutive midpoint counts attain the global integer-pair maximum. -/
theorem target_120 {h : ℕ} (lo : 2^1024/2≤h) (hi : h<2^1024) (σ : ℕ) :
    let B := 2^1024
    let n := B*h
    let w := B-1
    let a := (n+w).sqrt
    let count := fun u => (suffixPairs (B/2) B n w 120 σ u).card
    ∃ u₀∈Finset.Icc a (a+120), ∀ u, count u≤count u₀ := by
  have period : Nat.lcm 2 120=120 := by decide
  have eligible : 4096*(Nat.lcm 2 120)^3≤2^1024 := by rw [period]; decide +kernel
  simpa only [period] using maximum_pairs (by decide : 14≤1024) lo hi
    (by decide : 0<120) eligible σ

end PrimeFactors.HighWordSuffixRanking
