import PrimeFactors.MarginalTraceWidth
import PrimeFactors.WeightedTracePrefix
import PrimeFactors.GapStride

/-! Identify the actual weighted sum of a divisor pair among the tested labels. -/
namespace PrimeFactors.MarginalTraceWidth
open Real

theorem ordered_offsets (r o a b : ℕ) (pos : 0 < (offsets r o a b).length) :
    StrictMono (offset r o a b) := by
  let xs := offsets r o a b
  have sorted : xs.Pairwise (· < ·) := List.Pairwise.filter _ List.pairwise_lt_range
  have bounded (i : ℕ) (hi : i < xs.length) : xs[i] < 24 := by
    have h : xs[i] ∈ xs := List.getElem_mem hi
    exact List.mem_range.mp (List.mem_filter.mp h).1
  intro i j ij
  have il := Nat.mod_lt i pos
  have jl := Nat.mod_lt j pos
  change 24*(i/xs.length) + (xs[i%xs.length]?).getD 0 <
    24*(j/xs.length) + (xs[j%xs.length]?).getD 0
  rw [List.getElem?_eq_getElem il, List.getElem?_eq_getElem jl]
  simp only [Option.getD_some]
  have ord : i/xs.length ≤ j/xs.length := Nat.div_le_div_right ij.le
  rcases ord.eq_or_lt with same|diff
  · have di := Nat.mod_add_div i xs.length
    have dj := Nat.mod_add_div j xs.length
    rw [same] at di ⊢
    have comp : i%xs.length < j%xs.length := by omega
    exact Nat.add_lt_add_left (List.pairwise_iff_getElem.mp sorted _ _ il jl comp) _
  · have bi := bounded (i%xs.length) il
    dsimp only [xs] at bi diff ⊢
    omega

/-- An allowed label above the public starting ceiling occurs in the first H
search steps exactly when it is below the first omitted label. -/
theorem admitted_iff {s f r a b H : ℕ} (lo : f≤s)
    (pass : s.gcd 24=(a+b*r).gcd 24) :
    s < f+offset r (f%24) a b H ↔ ∃ i<H, s=f+offset r (f%24) a b i := by
  let d := s-f
  let xs := offsets r (f%24) a b
  have fd : f+d=s := by dsimp [d]; omega
  have ok : d%24 ∈ xs := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr (Nat.mod_lt _ (by decide)),?_⟩
    apply beq_iff_eq.mpr
    rw [((Nat.mod_modEq f 24).add (Nat.mod_modEq d 24)).gcd_eq,fd,pass]
  have inside := List.idxOf_lt_length_iff.mpr ok
  let idx := xs.idxOf (d%24) + xs.length*(d/24)
  have pos : 0<xs.length := by omega
  have found : offset r (f%24) a b idx=d := by
    change 24*((xs.idxOf (d%24) + xs.length*(d/24))/xs.length) +
      (xs[(xs.idxOf (d%24) + xs.length*(d/24))%xs.length]?).getD 0 = d
    rw [Nat.add_mul_div_left _ _ pos, Nat.add_mul_mod_self_left,
      Nat.div_eq_of_lt inside,Nat.mod_eq_of_lt inside,List.getElem?_idxOf ok]
    simpa only [Nat.zero_add,Option.getD_some,add_comm (24*(d/24))] using Nat.mod_add_div d 24
  have mono := ordered_offsets r (f%24) a b pos
  constructor
  · intro lt
    refine ⟨idx,?_,by omega⟩
    apply (mono.lt_iff_lt).mp
    omega
  · rintro ⟨i,lt,rfl⟩
    exact Nat.add_lt_add_left (mono lt) _

theorem sum_allowed {p q : ℕ} (a b : ℕ) (unit : p.Coprime 6) :
    (a*p+b*q).gcd 24=(a+b*((p*q)%24)).gcd 24 := by
  have p24 := (unit.pow_right 3).coprime_dvd_right (by decide : 24∣6^3)
  have sq := (square_mod_twentyfour unit).mul_left a
  have rel : p*(a*p+b*q) ≡ a+b*((p*q)%24) [MOD 24] := by
    rw [show p*(a*p+b*q)=a*p^2+b*(p*q) by ring]
    simpa only [mul_one] using sq.add ((Nat.mod_modEq (p*q) 24).symm.mul_left b)
  exact (Nat.Coprime.gcd_mul_left_cancel (a*p+b*q) p24).symm.trans rel.gcd_eq

/-- The sums belonging to an actual divisor pair are consecutive in the
admitted list up to the precise open factor interval. -/
theorem factor_band_iff {p q a b H : ℕ} {j : ℝ} (pp : 0<p) (qp : 0<q) (ap : 0<a)
    (jp : 0<j) (weights : j^4=(a:ℝ)*b) (pu : p.Coprime 6) :
    let n := p*q
    let u := productRoot n
    let r : Fin 24 := ⟨n%24,Nat.mod_lt _ (by decide)⟩
    let f := ⌈2*j^2*u^2⌉₊
    let e := endpoint u j (height r u j a b H)
    let c := j^2*u^2/a
    (c/e < p ∧ (p:ℝ) < c*e) ↔ ∃ i<H, a*p+b*q = f+offset r (f%24) a b i := by
  let u := productRoot (p*q)
  let r : Fin 24 := ⟨p*q%24,Nat.mod_lt _ (by decide)⟩
  let f := ⌈2*j^2*u^2⌉₊
  let h := height r u j a b H
  let S := a*p+b*q
  have ppos : (0:ℝ)<p := by exact_mod_cast pp
  have qpos : (0:ℝ)<q := by exact_mod_cast qp
  have apos : (0:ℝ)<a := by exact_mod_cast ap
  have up : 0<u := by dsimp [u,productRoot]; positivity
  have usq : u^4=(p:ℝ)*q := by
    rw [show u^4=(u^2)^2 by ring,show u^2=√((p*q:ℕ):ℝ) from sq_sqrt (sqrt_nonneg _),
      sq_sqrt (by positivity),Nat.cast_mul]
  have hs : (S:ℝ) = (a:ℝ)*p+b*q := by norm_cast
  have s0 : 2*j^2*u^2≤S := by
    apply le_of_sq_le_sq _ (by positivity)
    rw [show (2*j^2*u^2)^2=4*j^4*u^4 by ring,weights,usq,hs]
    nlinarith only [sq_nonneg ((a:ℝ)*p-b*q)]
  have fa : f≤S := Nat.ceil_le.mpr s0
  have eqh : 2*j^2*u^2+h = (f:ℝ)+offset r (f%24) a b H := by
    dsimp only [h,height,f]; ring
  have hpos : 0≤h := by
    dsimp only [h,height]; linarith only [Nat.le_ceil (2*j^2*u^2),
      (show (0:ℝ)≤offset r (f%24) a b H by positivity)]
  have quad : (a:ℝ)*p^2+j^4*u^4/a = (S:ℝ)*p := by
    rw [weights,usq,hs]; field_simp; ring
  change _ ↔ ∃ i<H, S=f+offset r (f%24) a b i
  rw [←band_iff up jp hpos apos,quad,eqh,mul_lt_mul_iff_of_pos_right ppos,←Nat.cast_add,Nat.cast_lt]
  exact admitted_iff fa (sum_allowed a b pu)

/-- For multiplier six, an actual divisor in the band gives a square and
one of the two factors from the positive-root gcd within sixteen tests. -/
theorem six_band_iff {p q : ℕ} (pp : 0<p) (qp : 0<q) (unit : (p*q).Coprime 6) :
    let n := p*q
    let u := productRoot n
    let r : Fin 24 := ⟨n%24,Nat.mod_lt _ (by decide)⟩
    let f := ⌈2*sixRoot^2*u^2⌉₊
    let e := endpoint u sixRoot (height r u sixRoot 3 2 16)
    let c := sixRoot^2*u^2/3
    (c/e < p ∧ (p:ℝ) < c*e) ↔ ∃ i<16,
      let S := f+offset r (f%24) 3 2 i
      let d := (S^2-24*n).sqrt
      S=3*p+2*q ∧ S^2=24*n+d^2 ∧ (n.gcd ((S+d)/2)=p ∨ n.gcd ((S+d)/2)=q) := by
  have jp : 0<sixRoot := lt_of_lt_of_le zero_lt_one six_root_bounds.1
  have weights : sixRoot^4=((3:ℕ):ℝ)*((2:ℕ):ℝ) := by rw [six_root_bounds.2.2.2.2]; norm_num
  have band := factor_band_iff (H:=16) pp qp (by decide : 0<3) jp weights
    (unit.coprime_dvd_left (dvd_mul_right p q))
  dsimp only at band ⊢
  simp only [Nat.cast_ofNat] at band
  rw [band]
  constructor
  · rintro ⟨i, small, hit⟩
    refine ⟨i,small,hit.symm,?_,?_⟩
    · rw [←hit]
      have sq := multiplier_sum_square p q 3 2
      change (3*p+2*q)^2=24*(p*q)+(3*p).dist (2*q)^2 at sq
      rw [sq,Nat.add_sub_cancel_left,Nat.sqrt_eq']
    · exact WeightedTracePrefix.shared_gcd rfl (a:=3) (b:=2) (by decide) unit.symm hit.symm
  · rintro ⟨i,small,hit,_,_⟩
    exact ⟨i,small,hit.symm⟩

/-- Integer indices for locations z+M*k in a closed interval. -/
noncomputable def closedIndices (z : ℤ) (M : ℕ) (l h : ℝ) : Finset ℤ :=
  Finset.Icc ⌈(l-z)/M⌉ ⌊(h-z)/M⌋

/-- Integer indices for locations z+M*k in an open interval. -/
noncomputable def openIndices (z : ℤ) (M : ℕ) (l h : ℝ) : Finset ℤ :=
  Finset.Ioo ⌊(l-z)/M⌋ ⌈(h-z)/M⌉

theorem mem_closedIndices {z k : ℤ} {M : ℕ} {l h : ℝ} (mp : 0<M) :
    k∈closedIndices z M l h ↔ l≤(z:ℝ)+k*M ∧ (z:ℝ)+k*M≤h := by
  have pos : (0:ℝ)<M := by exact_mod_cast mp
  simp only [closedIndices,Finset.mem_Icc,Int.ceil_le,Int.le_floor,
    div_le_iff₀ pos,le_div_iff₀ pos,sub_le_iff_le_add',le_sub_iff_add_le']

theorem mem_openIndices {z k : ℤ} {M : ℕ} {l h : ℝ} (mp : 0<M) :
    k∈openIndices z M l h ↔ l<(z:ℝ)+k*M ∧ (z:ℝ)+k*M<h := by
  have pos : (0:ℝ)<M := by exact_mod_cast mp
  simp only [openIndices,Finset.mem_Ioo,Int.floor_lt,Int.lt_ceil,
    div_lt_iff₀ pos,lt_div_iff₀ pos,sub_lt_iff_lt_add',lt_sub_iff_add_lt']

private theorem compare_progressions (z : ℤ) {M : ℕ} (mp : 0<M) {a b l h : ℝ}
    (span : a≤b) (margin : b-a+2*M<h-l) :
    (closedIndices z M a b).card < (openIndices z M l h).card := by
  have pos : (0:ℝ)<M := by exact_mod_cast mp
  apply more_sites (div_le_div_of_nonneg_right (sub_le_sub_right span z) pos.le)
  convert (div_lt_div_iff_of_pos_right pos).mpr margin using 1 <;> field_simp

/-- Every individual residue progression makes the same choice, even when
its modulus is large.  Closed endpoints favor the losing interval in both
comparisons. The product slice in `target` also guarantees feasibility. -/
theorem progression_choice {n M : ℕ} (z : ℤ) (mp : 0<M) (cap : M≤2^500)
    (unit : n.Coprime 6) (lo : 9/16*(2^1024:ℝ)^2≤n) :
    let u := productRoot n
    let r : Fin 24 := ⟨n%24,Nat.mod_lt _ (by decide)⟩
    let e := endpoint u 1 (height r u 1 1 1 16)
    let f := endpoint u 1 (height r u 1 1 1 33)
    let y := endpoint u sixRoot (height r u sixRoot 3 2 16)
    let c := sixRoot^2/3*u^2
    if n%24=11 ∨ n%24=23 then
      (closedIndices z M (c/y) (c*y)).card < (openIndices z M (u^2/f) (u^2/e)).card
    else
      (closedIndices z M (u^2/f) (u^2/e)).card < (openIndices z M (c/y) (c*y)).card := by
  dsimp only
  let u := productRoot n
  let r : Fin 24 := ⟨n%24,Nat.mod_lt _ (by decide)⟩
  have up : 0≤u := sqrt_nonneg _
  have low : (2:ℝ)^511≤u := by
    apply le_of_sq_le_sq _ up
    apply le_of_sq_le_sq _ (sq_nonneg _)
    rw [show u^2=√(n:ℝ) from sq_sqrt (sqrt_nonneg _),sq_sqrt (Nat.cast_nonneg n)]
    exact le_trans (by norm_num) lo
  have big : 100000≤u := le_trans (by norm_num) low
  have capR : (M:ℝ)≤(2:ℝ)^500 := by exact_mod_cast cap
  have small : 2*(M:ℝ) ≤ u/20 := by linarith only [capR,low]
  split
  next reg =>
    have h := exceptional_width (u:=u) big reg
    apply compare_progressions z mp h.1
    linarith only [h.2,small]
  next reg =>
    have finite : ∀ v : Fin 24, (v:ℕ).Coprime 6 → ¬((v:ℕ)=11 ∨ (v:ℕ)=23) → step v≤12 := by decide +kernel
    have ru : (r:ℕ).Coprime 6 := by
      change (n%24).gcd 6=1
      rw [Nat.gcd_comm, Nat.gcd_rec, Nat.mod_mod_of_dvd _ (by decide : 6∣24), ←Nat.gcd_rec, Nat.gcd_comm]
      exact unit
    have H := actual_heights r ru u
    have gain := length_margin big H (by exact_mod_cast finite r ru reg)
    apply compare_progressions z mp (ordinary_span big H)
    linarith only [gain,small,up]

end PrimeFactors.MarginalTraceWidth
