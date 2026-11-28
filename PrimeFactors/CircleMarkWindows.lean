import PrimeFactors.CircleMarkAutocorrelation
import PrimeFactors.FilterSwapPhaseMoment

/-! Short lag windows for two opposite marked classes at one odd prime. -/
namespace PrimeFactors.CircleMarkWindows

open Finset CircleMarkAutocorrelation

/-- The positive distance to the nearer of the two nonzero correlation peaks. -/
def Separation (p : ℕ) (a : ℤ) (g : ℕ) : Prop :=
  0<g ∧ 2*g<p ∧ (g:ZMod p)^2=4*(a:ZMod p)

private theorem equal_in_half {p : ℕ} [Fact p.Prime] {g h : ℕ}
    (gp : 0<g) (gs : 2*g<p) (hs : 2*h<p)
    (eqn : (h:ZMod p)^2=(g:ZMod p)^2) : h=g := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp eqn with same|neg
  · have eq := congrArg ZMod.val same
    simpa only [ZMod.val_natCast_of_lt (by omega : g<p),ZMod.val_natCast_of_lt (by omega : h<p)] using eq
  · have zero : ((h+g:ℕ):ZMod p)=0 := by push_cast; rw [neg,neg_add_cancel]
    have eq := congrArg ZMod.val zero
    rw [ZMod.val_natCast_of_lt (by omega),ZMod.val_zero] at eq
    omega

/-- Every nonzero square target has a unique distance in the first half-period. -/
theorem unique {p : ℕ} [hp : Fact p.Prime] (odd : p≠2) {a : ℤ}
    (square : legendreSym p a=1) : ∃! g, Separation p a g := by
  have nz : (a:ZMod p)≠0 := by
    intro bad
    rw [(legendreSym.eq_zero_iff p a).mpr bad] at square
    contradiction
  obtain ⟨r,hr⟩ := (isSquare_iff_exists_sq _).mp ((legendreSym.eq_one_iff p nz).mp square)
  have r0 : r≠0 := by rintro rfl; simp_all
  let z := 2*r
  have two : (2:ZMod p)≠0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  have zn : z≠0 := mul_ne_zero two r0
  have zr : z^2=4*(a:ZMod p) := by rw [hr]; dsimp [z]; ring
  have vz := ZMod.val_lt z
  have vp : 0<z.val := Nat.pos_of_ne_zero fun zero => zn (ZMod.val_injective _ (zero.trans ZMod.val_zero.symm))
  have parity := hp.out.odd_of_ne_two odd
  obtain ⟨v,hv⟩ := parity
  have ex : ∃ g, Separation p a g := by
    by_cases small : 2*z.val<p
    · exact ⟨z.val,vp,small,by simpa only [ZMod.natCast_zmod_val] using zr⟩
    · letI : NeZero z := ⟨zn⟩
      have neg := ZMod.val_neg_of_ne_zero z
      exact ⟨(-z).val,by omega,by omega,by simpa only [ZMod.natCast_zmod_val,neg_sq] using zr⟩
  obtain ⟨g,hg⟩ := ex
  exact ⟨g,hg,fun h hh => equal_in_half hg.1 hg.2.1 hh.2.1 (hh.2.2.trans hg.2.2.symm)⟩

/-- Every possible distance is realized on the same prime product by some
opposite-sign target. This is a statement across targets, at fixed primes. -/
theorem realizes {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (diff : p≠q) (op : p≠2) (oq : q≠2) {g : ℕ} (pos : 0<g) (small : 2*g<p) :
    ∃ a : ℤ, legendreSym p a=1 ∧ legendreSym q a= -1 ∧ Separation p a g := by
  have two : (2:ZMod p)≠0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  have g0 : (g:ZMod p)≠0 := by
    intro bad
    have eq := congrArg ZMod.val bad
    rw [ZMod.val_natCast_of_lt (by omega),ZMod.val_zero] at eq
    omega
  obtain ⟨b,ns⟩ := FiniteField.exists_nonsquare (F:=ZMod q) (by rwa [ZMod.ringChar_zmod_n])
  let e := ZMod.chineseRemainder ((Nat.coprime_primes hp.out hq.out).mpr diff)
  let w := e.symm (((g:ZMod p)/2)^2,b)
  let a : ℤ := w.val
  have back : (a:ZMod (p*q))=w := by simp [a]
  have eqn := congrArg e back
  rw [map_intCast] at eqn
  have both : ((a:ZMod p),(a:ZMod q))=(((g:ZMod p)/2)^2,b) := by
    simpa only [w,RingEquiv.apply_symm_apply] using eqn
  have P := congrArg Prod.fst both
  have Q := congrArg Prod.snd both
  dsimp only at P Q
  refine ⟨a,(legendreSym.eq_one_iff p (P ▸ pow_ne_zero 2 (div_ne_zero g0 two))).mpr ?_,
    (legendreSym.eq_neg_one_iff q).mpr (Q ▸ ns),pos,small,?_⟩
  · exact (isSquare_iff_exists_sq _).mpr ⟨_,P⟩
  · rw [P]; field_simp; ring

/-- Sum of lag overlaps with supplied natural weights. -/
noncomputable def weighted (n : ℕ) [NeZero n] (a : ℤ) (lags : Finset ℕ) (w : ℕ→ℕ) : ℕ :=
  ∑ h∈lags,w h*overlap n a (h:ℤ)

private theorem single {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q) (op : p≠2)
    {a : ℤ} (sp : legendreSym p a=1) (nq : legendreSym q a= -1) {g h : ℕ}
    (sep : Separation p a g) (lo : 0<h) (hi : 2*h<p) :
    overlap (p*q) a h=if h=g then q else 0 := by
  have nz : (h:ZMod p)≠0 := by
    intro bad
    have eq := congrArg ZMod.val bad
    rw [ZMod.val_natCast_of_lt (by omega),ZMod.val_zero] at eq
    omega
  have test : ((h:ZMod p)^2=4*(a:ZMod p)) ↔ h=g :=
    ⟨fun eq => equal_in_half sep.1 sep.2.1 hi (eq.trans sep.2.2.symm),fun eq => eq ▸ sep.2.2⟩
  rw [oriented diff op sp nq]
  simp only [Int.cast_natCast,if_neg nz,test]

/-- In the first positive half-period, precisely one lag can contribute.
This holds for a nonconsecutive selection and for arbitrary weights. -/
theorem menu {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q) (op : p≠2)
    {a : ℤ} (sp : legendreSym p a=1) (nq : legendreSym q a= -1) {g : ℕ}
    (sep : Separation p a g) (lags : Finset ℕ) (bounded : ∀ h∈lags, 0<h ∧ 2*h<p)
    (w : ℕ→ℕ) : weighted (p*q) a lags w=if g∈lags then w g*q else 0 := by
  have each (h : ℕ) (mem : h∈lags) : w h*overlap (p*q) a h=(if h=g then w h*q else 0) := by
    rw [single diff op sp nq sep (bounded h mem).1 (bounded h mem).2]
    simp only [mul_ite,mul_zero]
  rw [weighted,sum_congr rfl each,sum_ite_eq']

/-- An ordinary rectangular prefix reports only whether it reached the first
exceptional lag. The triangular weighting reports its position once reached. -/
theorem prefix_windows {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q) (op : p≠2)
    {a : ℤ} (sp : legendreSym p a=1) (nq : legendreSym q a= -1) {g : ℕ}
    (sep : Separation p a g) (L : ℕ) (short : 2*L<p) :
    weighted (p*q) a (Icc 1 L) (fun _ => 1)=(if g≤L then q else 0) ∧
    weighted (p*q) a (Icc 1 L) (fun h => L+1-h)=(L+1-g)*q := by
  have bounded (h : ℕ) (mem : h∈Icc 1 L) : 0<h ∧ 2*h<p := by
    obtain ⟨lo,hi⟩ := mem_Icc.mp mem
    omega
  have pos := sep.1
  rw [menu diff op sp nq sep _ bounded,menu diff op sp nq sep _ bounded]
  simp only [mem_Icc,show 1≤g by omega,true_and,one_mul]
  by_cases hit : g≤L <;> simp [hit,show ¬g≤L → L+1-g=0 by omega]

/-- At the half-period the rectangular aggregate is always the same prime,
regardless of where the two marked classes lie. -/
theorem half_window {p q : ℕ} [hp : Fact p.Prime] [Fact q.Prime] (diff : p≠q) (op : p≠2)
    {a : ℤ} (sp : legendreSym p a=1) (nq : legendreSym q a= -1) :
    weighted (p*q) a (Icc 1 (p/2)) (fun _ => 1)=q := by
  obtain ⟨g,sep,_⟩ := unique op sp
  obtain ⟨v,hv⟩ := hp.out.odd_of_ne_two op
  have small := sep.2.1
  simpa only [if_pos (by omega : g≤p/2)] using
    (prefix_windows diff op sp nq sep (p/2) (by omega)).1

/-- Exactly this many possible distances are missed by a menu restricted to
the first half-period. Every one is attained by some target by `realizes`. -/
theorem missed_distances (p : ℕ) (lags : Finset ℕ) (sub : lags⊆Icc 1 (p/2)) :
    ((Icc 1 (p/2)) \ lags).card=p/2-lags.card := by
  rw [card_sdiff sub,Nat.card_Icc]
  omega

open FilterSwapPhaseMoment (correlation windowTotal triangle)

noncomputable def indicator (n : ℕ) [NeZero n] (a : ℤ) (x : ZMod n) : ℤ :=
  if x∈CircleBranchCount.marked n a then 1 else 0

private theorem indicator_lag (n : ℕ) [NeZero n] (a : ℤ) (h : ℕ) :
    correlation (indicator n a) (h•(1:ZMod n))=(overlap n a h:ℤ) := by
  let marks := CircleBranchCount.marked n a
  have eqn : marks.filter (fun x => x+((h:ℤ):ZMod n)∈marks) =
      univ.filter (fun x : ZMod n => x∈marks ∧ x+(h:ZMod n)∈marks) := by ext; simp
  rw [correlation,overlap,eqn,card_filter]
  push_cast
  apply sum_congr rfl
  intro x _
  simp only [indicator,marks,nsmul_eq_mul,mul_one]
  split_ifs <;> simp_all [marks]

/-- Across all starting residues, a window of width w has a constant first
moment. Its second moment changes only when w exceeds the shorter separation. -/
theorem spatial {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (diff : p≠q) (op : p≠2)
    {a : ℤ} (sp : legendreSym p a=1) (nq : legendreSym q a= -1) {g : ℕ}
    (sep : Separation p a g) (w : ℕ) (short : 2*w<p) :
    (∑ x,windowTotal (indicator (p*q) a) 1 w x)=(2*q*w:ℕ) ∧
    (∑ x,(windowTotal (indicator (p*q) a) 1 w x)^2)=(2*q*(w+(w-g)):ℕ) := by
  have zero : overlap (p*q) a 0=2*q := by
    rw [oriented diff op sp nq]; simp
  have pos := sep.1
  have diag := indicator_lag (p*q) a 0
  simp only [zero_nsmul,Nat.cast_zero,zero] at diag
  constructor
  · rw [FilterSwapPhaseMoment.first_moment]
    have eqn : (∑ x,indicator (p*q) a x)=correlation (indicator (p*q) a) 0 := by
      unfold correlation
      apply sum_congr rfl
      intro x _
      simp only [add_zero,indicator]
      split <;> decide
    rw [eqn,diag]
    push_cast
    ring
  · rw [FilterSwapPhaseMoment.second_moment,triangle]
    simp_rw [indicator_lag]
    simp only [Nat.cast_zero,zero]
    have each (j : ℕ) (hj : j∈range w) :
        ((w:ℤ)-1-j)*(overlap (p*q) a (j+1:ℕ):ℤ) =
        (if j=g-1 then ((w:ℤ)-g)*q else 0) := by
      have lt := mem_range.mp hj
      rw [single diff op sp nq sep (by omega : 0<j+1) (by omega)]
      by_cases e : j=g-1
      · have g_eq : g=j+1 := by omega
        rw [if_pos e,←g_eq,if_pos rfl,g_eq]
        push_cast
        ring
      · simp [e,show j+1≠g by omega]
    rw [sum_congr rfl each,sum_ite_eq']
    simp only [mem_range]
    by_cases hit : g≤w
    · rw [if_pos (by omega : g-1<w)]
      simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_sub hit,Nat.cast_ofNat]
      ring
    · rw [if_neg (by omega : ¬g-1<w),Nat.sub_eq_zero_of_le (by omega)]
      push_cast
      ring

/-- On modulus 39 the targets 14 and 17 have distances two and four.
Their width-four ordinary totals agree, and their tapered totals differ. -/
theorem controls :
    (weighted 39 14 (Icc 1 4) (fun _ => 1)=3 ∧
      weighted 39 17 (Icc 1 4) (fun _ => 1)=3) ∧
    (weighted 39 14 (Icc 1 4) (fun h => 5-h)=9 ∧
      weighted 39 17 (Icc 1 4) (fun h => 5-h)=3) := by
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have A := prefix_windows (p:=13) (q:=3) (a:=14) (g:=2) (by decide) (by decide)
    (by rw [jacobiSym.legendreSym.to_jacobiSym]; norm_num)
    (by rw [jacobiSym.legendreSym.to_jacobiSym]; norm_num)
    (by unfold Separation; decide) 4 (by decide)
  have B := prefix_windows (p:=13) (q:=3) (a:=17) (g:=4) (by decide) (by decide)
    (by rw [jacobiSym.legendreSym.to_jacobiSym]; norm_num)
    (by rw [jacobiSym.legendreSym.to_jacobiSym]; norm_num)
    (by unfold Separation; decide) 4 (by decide)
  exact ⟨⟨A.1,B.1⟩,A.2,B.2⟩

end PrimeFactors.CircleMarkWindows
