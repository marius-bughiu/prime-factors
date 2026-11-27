import PrimeFactors.FareyParentSufficient
import PrimeFactors.ConvergentGcdThreshold
import PrimeFactors.PowerImageWidth

/-! Rigidity of ordinary convergent hits near a chosen rational anchor. The endpoints
of a public interval for the hidden deficit give a certificate using integers only. -/
namespace PrimeFactors.PowerRatioAnchor

set_option exponentiation.threshold 4096

abbrev Occurs (N E F : ℕ) : Prop := ∃ i, (E:ℚ)/F=((E:ℝ)/N).convergent i

/-- Two multiples of g within a distance strictly below g coincide. -/
theorem multiples {g x y M : ℕ} (gx : g∣x) (gy : g∣y)
    (lower : x≤y+M) (upper : y≤x+M) (small : M<g) : x=y := by
  rcases lt_trichotomy x y with h|h|h
  · have := Nat.le_of_dvd (Nat.sub_pos_of_lt h) (Nat.dvd_sub gy gx)
    omega
  · exact h
  · have := Nat.le_of_dvd (Nat.sub_pos_of_lt h) (Nat.dvd_sub gx gy)
    omega

/-- The interval [L,U] contains N−F. Its endpoint tests bound the distance of dE
from cF for every possible F. A successful Euclidean probe then fixes F exactly. -/
theorem fixed {N E F c d L U M : ℕ} (ep : 0<E) (fp : 0<F) (fn : F≤N)
    (lo : L≤N-F) (hi : N-F≤U)
    (left : d*E≤c*(N-U)+M) (right : c*(N-L)≤d*E+M)
    (budget : N*M^2≤E*(N-U)*L) (hit : Occurs N E F) : d*E=c*F := by
  have fl : N-U≤F := by omega
  have fu : F≤N-L := by omega
  have necessary := ConvergentGcdThreshold.necessary ep fp fn hit
  have ng := budget.trans ((Nat.mul_le_mul (Nat.mul_le_mul_left E fl) lo))
  have small : M<E.gcd F := by
    by_contra! bad
    have h := Nat.mul_le_mul_left N (Nat.pow_le_pow_left bad 2)
    exact (not_le_of_gt (ng.trans_lt necessary)) h
  exact multiples (dvd_mul_of_dvd_right (Nat.gcd_dvd_left E F) d)
    (dvd_mul_of_dvd_right (Nat.gcd_dvd_right E F) c)
    (left.trans (Nat.add_le_add_right (Nat.mul_le_mul_left c fl) M))
    ((Nat.mul_le_mul_left c fu).trans right) small

/-- For a reduced positive anchor small enough for its Farey cylinder to cover the
offset interval, the single test dE=cF is both necessary and sufficient. -/
theorem hit_iff {N E F c d L U M : ℕ} (ep : 0<E) (fp : 0<F) (fn : F<N)
    (cp : 0<c) (dp : 0<d) (cop : c.Coprime d) (lo : L≤N-F) (hi : N-F≤U)
    (left : d*E≤c*(N-U)+M) (right : c*(N-L)≤d*E+M)
    (budget : N*M^2≤E*(N-U)*L) (short : c*U*(2*d)<N) :
    Occurs N E F ↔ d*E=c*F := by
  refine ⟨fixed ep fp fn.le lo hi left right budget,?_⟩
  intro eq
  obtain ⟨_,db,det⟩ := FareyParentSufficient.parent_spec cp dp cop
  apply FareyParentSufficient.sufficient ep fp fn dp db (by simpa [Nat.mul_comm] using eq.symm) det
  exact (Nat.mul_le_mul (Nat.mul_le_mul_left c hi) (by omega)).trans_lt short

private theorem scale {N E L U M : ℕ} (room : 2*N≤3*(N-U)) (height : 3*M^2≤2*E*L) :
    N*M^2≤E*(N-U)*L := by
  apply Nat.le_of_mul_le_mul_left _ (by decide : 0<2)
  calc
    2*(N*M^2) = (2*N)*M^2 := by ring
    _ ≤ (3*(N-U))*M^2 := Nat.mul_le_mul_right _ room
    _ = (N-U)*(3*M^2) := by ring
    _ ≤ (N-U)*(2*E*L) := Nat.mul_le_mul_left _ height
    _ = 2*(E*(N-U)*L) := by ring

private theorem deficit_bounds {p q N F : ℕ} (product : N=p*q) (width : 2^2047≤N)
    (eq : N=F+(p+q-1)) (pw : p<2^1024) (qw : q<2^1024) :
    2^1024≤N-F ∧ N-F≤2^1025 := by
  have ag : 4*N≤(p+q)^2 := by
    rw [product]
    exact_mod_cast (show (4:ℤ)*(p*q)≤(p+q)^2 by nlinarith only [sq_nonneg ((p:ℤ)-q)])
  have lo : 2^1024≤N-F := by
    by_contra! lt
    have small := Nat.pow_le_pow_left (show p+q≤2^1024 by omega) 2
    have large := Nat.mul_le_mul_left 4 width
    omega
  have hi : N-F≤2^1025 := by omega
  exact ⟨lo,hi⟩

/-- For any two 1024-bit factors with a full 2048-bit product, trying N−k as an
exponent for any k≤2^1535 recovers the predecessor product precisely when k was
already the correct factor-sum deficit. Primality is unnecessary. -/
theorem near_product {p q k : ℕ} (pp : 1<p) (qp : 1<q) (pw : p<2^1024) (qw : q<2^1024)
    (width : 2^2047≤p*q) (radius : k≤2^1535) :
    Occurs (p*q) (p*q-k) ((p-1)*(q-1)) ↔ k=p+q-1 := by
  let N := p*q
  let E := N-k
  let F := (p-1)*(q-1)
  change 2^2047≤N at width
  have eq : N=F+(p+q-1) := PowerImageWidth.offset pp.le qp.le
  have fp : 0<F := Nat.mul_pos (by omega) (by omega)
  have fn : F<N := by omega
  obtain ⟨lo,hi⟩ := deficit_bounds (p:=p) (q:=q) rfl width eq pw qw
  have e : 3*2^2045≤E := by dsimp only [E]; omega
  have scalar := Nat.mul_le_mul_right (2^1024) (Nat.mul_le_mul_left 2 e)
  have base : 3*((2^1535:ℕ)^2)=2*(3*2^2045)*2^1024 := by decide +kernel
  have budget : N*(2^1535)^2≤E*(N-2^1025)*2^1024 := scale (by omega) (base.le.trans scalar)
  have rule := hit_iff (c:=1) (d:=1) (M:=2^1535) (by omega : 0<E)
    fp fn (by decide) (by decide) (by decide) lo hi
    (by simp only [Nat.one_mul]; dsimp only [E]; omega)
    (by simp only [Nat.one_mul]; dsimp only [E]; omega) budget (by omega)
  change Occurs N E F ↔ _
  simp only [Nat.one_mul] at rule
  rw [rule]
  dsimp only [E]
  omega

private theorem ratio_budget {N E c d L U : ℕ} (dp : 0<d) (es : c*N≤2*d*E)
    (fs : N≤2*(N-U)) (size : 4*c*d*U^2≤N*L) :
    N*(c*U)^2≤E*(N-U)*L := by
  apply Nat.le_of_mul_le_mul_left _ (by positivity : 0<4*d)
  calc
    4*d*(N*(c*U)^2) = (c*N)*(4*c*d*U^2) := by ring
    _ ≤ (2*d*E)*(N*L) := Nat.mul_le_mul es size
    _ ≤ (2*d*E)*(2*(N-U)*L) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right L fs)
    _ = 4*d*(E*(N-U)*L) := by ring

/-- Every floor(cN/d) with 1≤c≤d≤2^509 misses on every full-width input. Both the
rational multiplier and its prime factors can depend on N; no coprimality is assumed. -/
theorem rounded_excluded {p q c d : ℕ} (pp : 1<p) (qp : 1<q)
    (pw : p<2^1024) (qw : q<2^1024) (width : 2^2047≤p*q)
    (cp : 0<c) (cd : c≤d) (small : d≤2^509) :
    ¬ Occurs (p*q) (c*(p*q)/d) ((p-1)*(q-1)) := by
  let N := p*q
  let E := c*N/d
  let F := (p-1)*(q-1)
  change 2^2047≤N at width
  have eq : N=F+(p+q-1) := PowerImageWidth.offset pp.le qp.le
  obtain ⟨lo,hi⟩ := deficit_bounds (p:=p) (q:=q) rfl width eq pw qw
  have fp : 0<F := Nat.mul_pos (by omega) (by omega)
  have fn : F≤N := by omega
  have dp := cp.trans_le cd
  have cn := Nat.le_mul_of_pos_left N cp
  have ep : 0<E := Nat.div_pos (by omega) dp
  let r := c*N%d
  have mod : r+d*E=c*N := Nat.mod_add_div _ _
  have rd : r<d := Nat.mod_lt _ dp
  have de : d≤d*E := Nat.le_mul_of_pos_right d ep
  have es : c*N≤2*d*E := by nlinarith only [mod,rd,de]
  have smallcd := Nat.mul_le_mul (cd.trans small) small
  have numeric : 4*((2^509:ℕ)*2^509)*(2^1025)^2≤2^2047*2^1024 := by decide +kernel
  have size : 4*c*d*(2^1025)^2≤N*2^1024 := calc
    _ = 4*(c*d)*(2^1025)^2 := by ring
    _ ≤ 4*(2^509*2^509)*(2^1025)^2 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 smallcd)
    _ ≤ _ := numeric.trans (Nat.mul_le_mul_right _ width)
  have budget := ratio_budget dp es (by omega : N≤2*(N-2^1025)) size
  have u : 2^1025≤N := by omega
  have l : 2^1024≤N := by omega
  have back : c*N=c*(N-2^1025)+c*2^1025 := by
    rw [←Nat.mul_add,Nat.sub_add_cancel u]
  have large : d≤c*2^1024 := small.trans (by
    exact (by decide : (2:ℕ)^509≤2^1024).trans (Nat.le_mul_of_pos_left _ cp))
  have lower : c*(N-2^1024)+c*2^1024=c*N := by
    rw [←Nat.mul_add,Nat.sub_add_cancel l]
  have lt : c*(N-2^1024)<d*E := by omega
  intro hit
  have ev := fixed ep fp fn lo hi (by omega : d*E≤c*(N-2^1025)+c*2^1025)
    (by omega : c*(N-2^1024)≤d*E+c*2^1025) budget hit
  have fu := Nat.mul_le_mul_left c (show F≤N-2^1024 by omega)
  omega

/-- Away from the anchor other true upper rows can occur. At 437=19·23 and E=264
the recovered ratio is 2/3, although k=173 differs from the true deficit 41. -/
theorem outside_example : Occurs 437 (437-173) ((19-1)*(23-1)) ∧ 173≠19+23-1 := by
  refine ⟨?_,by decide⟩
  exact FareyParentSufficient.sufficient (a:=2) (b:=3) (c:=1) (d:=2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end PrimeFactors.PowerRatioAnchor
