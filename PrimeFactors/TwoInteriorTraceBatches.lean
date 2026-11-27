import PrimeFactors.MarginalTraceCoverage

/-! Divide a second batch of square tests between two disjoint ranges for the
smaller factor. All intervals use the first omitted admissible label. -/
namespace PrimeFactors.TwoInteriorTraceBatches
open Real MarginalTraceWidth

noncomputable def thirtyFiveRoot : ℝ := √(√35)

private theorem root35 : 1≤thirtyFiveRoot ∧ thirtyFiveRoot≤49/20 ∧
    84/100≤thirtyFiveRoot^2/7 ∧ thirtyFiveRoot^2/7≤85/100 ∧ thirtyFiveRoot^4=35 := by
  have lo : (588/100:ℝ)≤√35 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hi : √(35:ℝ)≤595/100 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have jsq : thirtyFiveRoot^2=√35 := sq_sqrt (sqrt_nonneg _)
  refine ⟨(Real.le_sqrt (by norm_num) (sqrt_nonneg _)).mpr (by linarith only [lo]),
    Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith only [hi]⟩, by linarith only [lo,jsq],
    by linarith only [hi,jsq],?_⟩
  rw [show thirtyFiveRoot^4=(thirtyFiveRoot^2)^2 by ring,jsq,sq_sqrt (by norm_num)]

private theorem ranges (r : Fin 24) (unit : (r:ℕ).Coprime 6) (u : ℝ) :
    let a := height r u sixRoot 3 2 7
    let b := height r u thirtyFiveRoot 7 5 8
    let h := height r u sixRoot 3 2 16
    (20≤a ∧ a≤24) ∧ (48≤b ∧ b≤216) ∧ 0≤h ∧ h≤52 := by
  have table : ∀ z o : Fin 24, (z:ℕ).Coprime 6 →
      (20≤offset z o 3 2 7 ∧ offset z o 3 2 7<24) ∧
      (48≤offset z o 7 5 8 ∧ offset z o 7 5 8<216) ∧ offset z o 3 2 16<52 := by decide +kernel
  have gain (j : ℝ) : (0:ℝ)≤((⌈2*j^2*u^2⌉₊:ℝ)-2*j^2*u^2) ∧
      (⌈2*j^2*u^2⌉₊:ℝ)-2*j^2*u^2≤1 := ⟨sub_nonneg.mpr (Nat.le_ceil _),
        by linarith only [Nat.ceil_lt_add_one (by positivity : 0≤2*j^2*u^2)]⟩
  have band (j : ℝ) (a b i L H : ℕ)
      (lo : L≤offset r (⌈2*j^2*u^2⌉₊%24) a b i) (hi : offset r (⌈2*j^2*u^2⌉₊%24) a b i<H) :
      (L:ℝ)≤height r u j a b i ∧ height r u j a b i≤H := by
    have pl : (L:ℝ)≤offset r (⌈2*j^2*u^2⌉₊%24) a b i := by exact_mod_cast lo
    have ph : (offset r (⌈2*j^2*u^2⌉₊%24) a b i:ℝ)+1≤H := by exact_mod_cast hi
    dsimp only [height]
    exact ⟨by linarith only [pl,(gain j).1],by linarith only [ph,(gain j).2]⟩
  let o6 : Fin 24 := ⟨⌈2*sixRoot^2*u^2⌉₊%24,Nat.mod_lt _ (by decide)⟩
  let o35 : Fin 24 := ⟨⌈2*thirtyFiveRoot^2*u^2⌉₊%24,Nat.mod_lt _ (by decide)⟩
  obtain ⟨A,_,H⟩ := table r o6 unit
  obtain ⟨_,C,_⟩ := table r o35 unit
  exact ⟨by exact_mod_cast band sixRoot 3 2 7 20 24 A.1 A.2,
    by exact_mod_cast band thirtyFiveRoot 7 5 8 48 216 C.1 C.2,
    by exact_mod_cast band sixRoot 3 2 16 0 52 (Nat.zero_le _) H⟩

/-- The interval length divided by the fourth root of the product, with the
normalized center written C. -/
private theorem width_eq {u j h C : ℝ} (up : 0<u) (ep : 0<endpoint u j h) :
    (C*u^2)*endpoint u j h-(C*u^2)/endpoint u j h =
      (C*rise u j h*(1+1/endpoint u j h))*u := by
  let y := endpoint u j h
  have yr : (y-1)*u=rise u j h := by dsimp only [y,endpoint]; field_simp
  change C*u^2*y-C*u^2/y=C*rise u j h*(1+1/y)*u
  rw [←yr]
  field_simp
  ring

private theorem lower_width {u j h C c w : ℝ} (big : 100000≤u) (j1 : 1≤j)
    (h0 : 0≤h) (h1 : h≤900) (c0 : 0≤c) (cl : c≤C) (w0 : 0≤w) (wl : w*j≤√h) :
    (c*w*(199/100))*u ≤ (C*u^2)*endpoint u j h-(C*u^2)/endpoint u j h := by
  have jp : 0<j := by linarith only [j1]
  have up : 0<u := by linarith only [big]
  have Y := endpoint_small big j1 h0 h1
  have yp : 0<endpoint u j h := by linarith only [Y.1]
  have wl' := ((le_div_iff₀ jp).mpr wl).trans (linear_rise big j1 h0 h1).1
  have yl : 99/100 ≤ 1/endpoint u j h := (le_div_iff₀ yp).mpr (by linarith only [Y.2])
  have m := mul_le_mul cl wl' w0 (c0.trans cl)
  have k := mul_le_mul m (show 199/100 ≤ 1+1/endpoint u j h by linarith only [yl]) (by norm_num) (mul_nonneg (c0.trans cl) (w0.trans wl'))
  rw [width_eq up yp]
  exact mul_le_mul_of_nonneg_right k up.le

private theorem ordinary_cap {u m a b h : ℝ} (big : 100000≤u) (H : Heights m a b h) :
    u^2/endpoint u 1 a-u^2/endpoint u 1 b ≤ 861/100*u := by
  obtain ⟨A,B,_,gap,_⟩ := rise_gaps big six_root_bounds.1 six_root_bounds.2.1 H
  have up : 0<u := by linarith only [big]
  let e := endpoint u 1 a
  let f := endpoint u 1 b
  have e1 : 1≤e := le_add_of_nonneg_right (div_nonneg A up.le)
  have f1 : 1≤f := le_add_of_nonneg_right (div_nonneg B up.le)
  have ef1 := one_le_mul_of_one_le_of_one_le e1 f1
  have efp : 0<e*f := by linarith only [ef1]
  have eq : (f-e)*u=rise u 1 b-rise u 1 a := by dsimp only [e,f,endpoint]; field_simp
  change u^2/e-u^2/f ≤ 861/100*u
  rw [show u^2/e-u^2/f=((f-e)*u*u)/(e*f) by field_simp; ring,eq]
  apply (div_le_iff₀ efp).mpr
  exact (mul_le_mul_of_nonneg_right gap up.le).trans (le_mul_of_one_le_right (by positivity) ef1)

private theorem six_cap {u h : ℝ} (big : 100000≤u) (h0 : 0≤h) (h1 : h≤52) :
    let c := sixRoot^2/3*u^2
    c*endpoint u sixRoot h-c/endpoint u sixRoot h ≤ 8*u := by
  let y := endpoint u sixRoot h
  have up : 0<u := by linarith only [big]
  have htop : h≤900 := by linarith only [h1]
  have g := linear_rise big six_root_bounds.1 h0 htop
  have Y := endpoint_small big six_root_bounds.1 h0 htop
  have yp : 0<y := by linarith only [Y.1]
  have jlow : (3/2:ℝ)≤sixRoot := by
    apply (Real.le_sqrt (by norm_num) (sqrt_nonneg 6)).mpr
    apply (Real.le_sqrt (by positivity) (by norm_num)).mpr
    norm_num
  have h_rt : √h≤29/4 := sqrt_le_iff.mpr ⟨by norm_num, by linarith only [h1]⟩
  have hg : √h/sixRoot ≤ 29/6 := (div_le_iff₀ (by linarith)).mpr (by linarith only [h_rt,jlow])
  have hgood : rise u sixRoot h≤97/20 := by linarith only [g.2,hg]
  have z0 : 0≤rise u sixRoot h := (div_nonneg (sqrt_nonneg _) (by linarith only [jlow])).trans g.1
  have yi : 1/y≤1 := (div_le_iff₀ yp).mpr (by linarith only [Y.1])
  have V := mul_le_mul six_root_bounds.2.2.2.1 hgood z0 (by norm_num)
  have W := mul_le_mul V (show 1+1/y≤2 by linarith only [yi]) (by positivity) (by norm_num)
  have cap : sixRoot^2/3*rise u sixRoot h*(1+1/y)≤8 := by linarith only [W]
  dsimp only
  rw [width_eq up yp]
  exact mul_le_mul_of_nonneg_right cap up.le

/-- Endpoints of a weighted factor interval at the first omitted label. -/
structure Window where
  low : ℝ
  high : ℝ

noncomputable def Window.width (w : Window) : ℝ := w.high-w.low

noncomputable def weighted (r : Fin 24) (u j : ℝ) (a b k : ℕ) : Window :=
  let y := endpoint u j (height r u j a b k)
  let c := j^2/(a:ℝ)*u^2
  ⟨c/y,c*y⟩

noncomputable def ordinary (r : Fin 24) (u : ℝ) : Window :=
  ⟨u^2/endpoint u 1 (height r u 1 1 1 33),u^2/endpoint u 1 (height r u 1 1 1 16)⟩

/-- After charging a square root for each starting point, the joint search
adds over half a fourth root's worth of length beyond either single batch. -/
theorem widths {u : ℝ} (big : 100000≤u) (r : Fin 24) (unit : (r:ℕ).Coprime 6) :
    let A := weighted r u sixRoot 3 2 7
    let B := weighted r u thirtyFiveRoot 7 5 8
    let C := weighted r u sixRoot 3 2 16
    let O := ordinary r u
    O.low≤O.high ∧ C.low≤C.high ∧
      (80/100*u^2<A.low ∧ A.high<B.low ∧ B.high<O.low) ∧
      max O.width C.width+u/2<A.width+B.width := by
  have up : 0<u := by linarith only [big]
  have tp : 0<u^2 := sq_pos_of_pos up
  let a := height r u sixRoot 3 2 7
  let b := height r u thirtyFiveRoot 7 5 8
  let h := height r u sixRoot 3 2 16
  obtain ⟨ra,rb,rh⟩ := ranges r unit u
  have abot : 0≤a := by linarith only [ra.1]
  have bbot : 0≤b := by linarith only [rb.1]
  have atop : a≤900 := by linarith only [ra.2]
  have btop : b≤900 := by linarith only [rb.2]
  have rtA : (44/10:ℝ)≤√a := (Real.le_sqrt (by norm_num) abot).mpr (by linarith only [ra.1])
  have rtB : (687/100:ℝ)≤√b := (Real.le_sqrt (by norm_num) bbot).mpr (by linarith only [rb.1])
  have capA := lower_width (j:=sixRoot) (c:=81/100) (w:=28/10) big six_root_bounds.1 abot atop
    (by norm_num) six_root_bounds.2.2.1 (by norm_num) (by linarith only [six_root_bounds.2.1,rtA])
  have capB := lower_width (j:=thirtyFiveRoot) (c:=84/100) (w:=28/10) big root35.1 bbot btop
    (by norm_num) root35.2.2.1 (by norm_num) (by linarith only [root35.2.1,rtB])
  have H := actual_heights r unit u
  have ord := ordinary_cap big H
  have six := six_cap big rh.1 rh.2
  let x := endpoint u sixRoot a
  let y := endpoint u thirtyFiveRoot b
  let z := endpoint u sixRoot h
  have X := endpoint_small big six_root_bounds.1 abot atop
  have Y := endpoint_small big root35.1 bbot btop
  have Z := endpoint_small big six_root_bounds.1 rh.1 (by linarith only [rh.2])
  have xp : 0<x := by linarith only [X.1]
  have yp : 0<y := by linarith only [Y.1]
  have c0 : 0≤sixRoot^2/3*u^2 := by positivity
  have span : sixRoot^2/3*u^2/z≤sixRoot^2/3*u^2*z :=
    (div_le_self c0 Z.1).trans (le_mul_of_one_le_right c0 Z.1)
  have left : (80/100)*u^2 < (sixRoot^2/3*u^2)/x := by
    apply (lt_div_iff₀ xp).mpr
    linarith only [mul_lt_mul_of_pos_right (show 80/100*x<sixRoot^2/3 by linarith only [X.2,six_root_bounds.2.2.1]) tp]
  have disjoint : sixRoot^2/3*u^2*x < (thirtyFiveRoot^2/7*u^2)/y := by
    apply (lt_div_iff₀ yp).mpr
    have bound := mul_le_mul (mul_le_mul six_root_bounds.2.2.2.1 X.2 xp.le (by norm_num)) Y.2 yp.le (by norm_num)
    linarith only [mul_lt_mul_of_pos_right (show sixRoot^2/3*x*y<thirtyFiveRoot^2/7 by linarith only [bound,root35.2.2.1]) tp]
  have ending : thirtyFiveRoot^2/7*u^2*y < (99/100)*u^2 := by
    have bound := mul_le_mul root35.2.2.2.1 Y.2 yp.le (by norm_num)
    linarith only [mul_lt_mul_of_pos_right (show thirtyFiveRoot^2/7*y<99/100 by linarith only [bound]) tp]
  dsimp only [ordinary,weighted,Window.width,Nat.cast_ofNat]
  refine ⟨ordinary_span big H,span,⟨left,disjoint,ending.trans (separated big H).1⟩,?_⟩
  rw [←max_add_add_right]
  apply max_lt <;> first | linarith only [capA,capB,ord,up] | linarith only [capA,capB,six,up]

private theorem two_interval_count {a b l h c d : ℝ} (ord : a≤b) (room : b-a+3 < h-l+(d-c)) :
    (Finset.Icc ⌈a⌉ ⌊b⌋).card < (Finset.Ioo ⌊l⌋ ⌈h⌉).card + (Finset.Ioo ⌊c⌋ ⌈d⌉).card := by
  have gap : ((⌊b⌋:ℤ):ℝ)+1-⌈a⌉ < ((⌈h⌉:ℤ):ℝ)-⌊l⌋-1+(((⌈d⌉:ℤ):ℝ)-⌊c⌋-1) := by
    linarith only [room,Int.floor_le b,Int.le_ceil a,Int.le_ceil h,Int.floor_le l,Int.le_ceil d,Int.floor_le c]
  have positive : 0 < ((⌈h⌉:ℤ):ℝ)-⌊l⌋-1+(((⌈d⌉:ℤ):ℝ)-⌊c⌋-1) := by
    linarith only [room,ord,Int.le_ceil h,Int.floor_le l,Int.le_ceil d,Int.floor_le c]
  have p : (0:ℤ)<⌈h⌉-⌊l⌋-1+(⌈d⌉-⌊c⌋-1) := by exact_mod_cast positive
  have g : (⌊b⌋:ℤ)+1-⌈a⌉ < ⌈h⌉-⌊l⌋-1+(⌈d⌉-⌊c⌋-1) := by exact_mod_cast gap
  rw [Int.card_Icc,Int.card_Ioo,Int.card_Ioo]
  omega

private theorem two_progressions (z : ℤ) {M : ℕ} (mp : 0<M) {O A B : Window}
    (span : O.low≤O.high) (room : O.width+3*M<A.width+B.width) :
    (closedIndices z M O.low O.high).card <
      (openIndices z M A.low A.high).card + (openIndices z M B.low B.high).card := by
  have pos : (0:ℝ)<M := by exact_mod_cast mp
  apply two_interval_count (div_le_div_of_nonneg_right (sub_le_sub_right span z) pos.le)
  dsimp only [Window.width] at room
  convert (div_lt_div_iff_of_pos_right pos).mpr room using 1 <;> field_simp

/-- For each allowed remainder separately, the two short ranges cover more
new integer locations than either equal-cost comparison. Their placement
ensures the counts add without overlap or clipping at the bit-width bound. -/
theorem target {n M : ℕ} (z : ℤ) (mp : 0<M) (cap : M≤2^500) (unit : n.Coprime 6)
    (lo : 9/16*(2^1024:ℝ)^2≤n) (hi : (n:ℝ)≤5/8*(2^1024:ℝ)^2) :
    let r : Fin 24 := ⟨n%24,Nat.mod_lt _ (by decide)⟩
    let u := productRoot n
    let A := weighted r u sixRoot 3 2 7
    let B := weighted r u thirtyFiveRoot 7 5 8
    let C := weighted r u sixRoot 3 2 16
    let O := ordinary r u
    let size := (openIndices z M A.low A.high).card+(openIndices z M B.low B.high).card
    max ((2^1024:ℝ)/2) (⌈(n:ℝ)/(2^1024-1)⌉:ℤ)<A.low ∧ A.high<B.low ∧ B.high<O.low ∧
    (closedIndices z M O.low O.high).card<size ∧ (closedIndices z M C.low C.high).card<size := by
  let r : Fin 24 := ⟨n%24,Nat.mod_lt _ (by decide)⟩
  let u := productRoot n
  have ru : (r:ℕ).Coprime 6 := by
    change (n%24).gcd 6=1
    rw [Nat.gcd_comm,Nat.gcd_rec,Nat.mod_mod_of_dvd _ (by decide : 6∣24),←Nat.gcd_rec,Nat.gcd_comm]
    exact unit
  have t0 : 0≤u^2 := sq_nonneg _
  have eq : (u^2)^2=(n:ℝ) := by rw [show u^2=√(n:ℝ) from sq_sqrt (sqrt_nonneg _),sq_sqrt (Nat.cast_nonneg n)]
  have low : (2:ℝ)^511≤u := by
    apply le_of_sq_le_sq _ (sqrt_nonneg _)
    apply le_of_sq_le_sq _ t0
    rw [eq]
    exact le_trans (by norm_num) lo
  have large : 100000≤u := le_trans (by norm_num) low
  have bound := slice_lower (B:=(2:ℝ)^1024) (by norm_num) t0 (eq.symm ▸ lo) (eq.symm ▸ hi)
  rw [eq] at bound
  obtain ⟨ord,cs,geo,gain⟩ := widths large r ru
  have capR : (M:ℝ)≤(2:ℝ)^500 := by exact_mod_cast cap
  have share : 3*(M:ℝ)≤u/2 := by linarith only [low,capR]
  dsimp only
  refine ⟨bound.trans_lt geo.1,geo.2.1,geo.2.2,two_progressions z mp ord ?_,two_progressions z mp cs ?_⟩
  · exact (add_le_add (le_max_left _ _) share).trans_lt gain
  · exact (add_le_add (le_max_right _ _) share).trans_lt gain

/-- In either selected window, a genuine divisor pair yields its exact
weighted trace at a tested index and returns one of the factors by gcd. -/
theorem weighted_finds {p q a b count : ℕ} {j : ℝ} (pp : 0<p) (qp : 0<q) (apos : 0<a)
    (jp : 0<j) (weights : j^4=(a:ℝ)*b) (pu : p.Coprime 6) (unit : (a*b).Coprime (p*q)) :
    let n := p*q
    let r : Fin 24 := ⟨n%24,Nat.mod_lt _ (by decide)⟩
    let u := productRoot n
    let W := weighted r u j a b count
    let first := ⌈2*j^2*u^2⌉₊
    W.low<p ∧ (p:ℝ)<W.high ↔ ∃ i<count,
      let s := first+offset r (first%24) a b i
      let d := (s^2-4*(a*b)*n).sqrt
      s=a*p+b*q ∧ s^2=4*(a*b)*n+d^2 ∧ (n.gcd ((s+d)/2)=p ∨ n.gcd ((s+d)/2)=q) := by
  have band := factor_band_iff (H:=count) pp qp apos jp weights pu
  dsimp only [weighted] at band ⊢
  rw [show j^2/(a:ℝ)*productRoot (p*q)^2=j^2*productRoot (p*q)^2/a by ring,band]
  constructor
  · rintro ⟨i,charge,hit⟩
    refine ⟨i,charge,hit.symm,?_,WeightedTracePrefix.shared_gcd rfl rfl unit hit.symm⟩
    rw [←hit]
    have sq := multiplier_sum_square p q a b
    rw [mul_assoc 4 a b] at sq
    rw [sq,Nat.add_sub_cancel_left,Nat.sqrt_eq']
  · rintro ⟨i,charge,hit,_,_⟩
    exact ⟨i,charge,hit.symm⟩

private noncomputable def sampleLabel (a b first i : ℕ) :=
  first+offset (2416359541%24) (first%24) a b i

private theorem brackets_exclude (v d : ℕ) (small : d^2<v) (large : v<(d+1)^2) :
    ∀ t : ℕ, t^2≠v := by
  intro t heq
  rcases le_total t d with h|h
  · exact (not_le_of_lt small) (heq ▸ Nat.pow_le_pow_left h 2)
  · have dt : d<t := by by_contra! no; exact (not_le_of_lt small) (heq ▸ Nat.pow_le_pow_left no 2)
    exact (not_le_of_lt large) (heq ▸ Nat.pow_le_pow_left dt 2)

private theorem no_square_ordinary (i : Fin 33) :
    ∀ t : ℕ, t^2 ≠ (sampleLabel 1 1 98313 i)^2-4*2416359541 := by
  let roots : List ℕ := [452, 995, 1601, 1830, 2219, 2389, 2698, 2840, 3105, 3229, 3464, 3576, 3790, 3892, 4090, 4185, 4369, 4458, 4631, 4715, 4879, 4960, 5116, 5192, 5342, 5415, 5559, 5629, 5767, 5835, 5969, 6034, 6163]
  have brackets : ∀ j : Fin 33, let s := sampleLabel 1 1 98313 j; let d := roots[j.val]?.getD 0
      d^2 < s^2-4*2416359541 ∧ s^2-4*2416359541<(d+1)^2 := by decide +kernel
  exact brackets_exclude _ _ (brackets i).1 (brackets i).2

private theorem no_square_six (i : Fin 16) :
    ∀ t : ℕ, t^2 ≠ (sampleLabel 3 2 240817 i)^2-24*2416359541 := by
  let roots : List ℕ := [445, 1457, 1757, 2239, 2445, 2811, 2977, 3285, 3429, 3699, 3827, 4071, 4187, 4411, 4519, 4728]
  have brackets : ∀ j : Fin 16, let s := sampleLabel 3 2 240817 j; let d := roots[j.val]?.getD 0
      d^2 < s^2-24*2416359541 ∧ s^2-24*2416359541<(d+1)^2 := by decide +kernel
  exact brackets_exclude _ _ (brackets i).1 (brackets i).2

/-- The third (7,5) label splits this product. Neither full equal-cost
single-window comparison encounters a square. The starting ceilings are
certified by the squares to either side. -/
theorem example_split : Nat.Prime 40949 ∧ Nat.Prime 59009 ∧ 40949*59009=2416359541 ∧
    ((98313-1)^2<4*2416359541 ∧ 4*2416359541≤98313^2) ∧
    ((240817-1)^2<24*2416359541 ∧ 24*2416359541≤240817^2) ∧
    ((581628-1)^2<140*2416359541 ∧ 140*2416359541≤581628^2) ∧
    sampleLabel 7 5 581628 2=581688 ∧ 581688^2=4*35*2416359541+8402^2 ∧
    Nat.gcd ((581688+8402)/2) 2416359541=59009 ∧
    (∀ (i : Fin 33) (t : ℕ), t^2≠(sampleLabel 1 1 98313 i)^2-4*2416359541) ∧
    (∀ (i : Fin 16) (t : ℕ), t^2≠(sampleLabel 3 2 240817 i)^2-24*2416359541) := by
  exact ⟨by norm_num,by norm_num,by decide +kernel,by decide +kernel,by decide +kernel,
    by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,no_square_ordinary,no_square_six⟩

end PrimeFactors.TwoInteriorTraceBatches
