import PrimeFactors.MonotoneDivisorSampling
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! We count proper gcds of the difference of two independent draws
using residues modulo a semiprime. For independent identically distributed draws with decreasing
positive-integer masses, uniform residues attain the largest possible rate. -/

namespace PrimeFactors.DifferenceSampling
open Finset

private theorem telescope (f g : ℕ → ℝ) (k : ℕ) (bound : ∀ j<k, f (j+1)≤g j) :
    ∑ j ∈ range (k+1), (f j-g j) ≤ f 0-g k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    have earlier := ih (fun j h => bound j (by omega))
    linarith only [earlier,bound k (by omega)]

/-- Folding consecutive ordered rows to their column sums is contractive on
vectors of total sum zero. Within each row an arbitrary common order suffices. -/
theorem fold (k m : ℕ) (x : ℕ → ℕ → ℝ)
    (separated : ∀ j<k, ∃ t : ℝ, ∀ r<m, x (j+1) r≤t ∧ t≤x j r)
    (centered : ∑ r ∈ range m, ∑ j ∈ range (k+1), x j r = 0) :
    ∑ r ∈ range m, (∑ j ∈ range (k+1), x j r)^2 ≤
    ∑ j ∈ range (k+1), ∑ r ∈ range m, (x j r)^2 := by
  by_cases one : k=0
  · subst k
    simp
  let A r := ∑ j ∈ range (k+1), x j r
  let u r := max (A r) 0
  let v r := max (-A r) 0
  have split (r) : A r = u r-v r ∧ (A r)^2=(u r)^2+(v r)^2 := by
    by_cases h : 0 ≤ A r
    · simp [u,v,max_eq_left h,max_eq_right (neg_nonpos.mpr h)]
    · simp [u,v,max_eq_right (le_of_not_ge h),max_eq_left (neg_nonneg.mpr (le_of_not_ge h))]
  have equal : ∑ r ∈ range m, u r = ∑ r ∈ range m, v r := by
    have h : ∑ r ∈ range m, (u r-v r) = 0 := by
      simpa only [←(split _).1] using (show ∑ r ∈ range m, A r=0 from centered)
    rwa [sum_sub_distrib,sub_eq_zero] at h
  let F j := ∑ r ∈ range m, x j r*u r
  let G j := ∑ r ∈ range m, x j r*v r
  have boundary : ∀ j<k, F (j+1) ≤ G j := by
    intro j hj
    obtain ⟨t,bt⟩ := separated j hj
    calc
      _ ≤ ∑ r ∈ range m, t*u r := sum_le_sum fun r hr =>
        mul_le_mul_of_nonneg_right (bt r (mem_range.mp hr)).1 (le_max_right ..)
      _ = ∑ r ∈ range m, t*v r := by simp only [←mul_sum,equal]
      _ ≤ _ := sum_le_sum fun r hr =>
        mul_le_mul_of_nonneg_right (bt r (mem_range.mp hr)).2 (le_max_right ..)
  have expansion : ∑ j ∈ range (k+1), (F j-G j) = ∑ r ∈ range m, (A r)^2 := calc
    _ = ∑ j ∈ range (k+1), ∑ r ∈ range m, x j r * A r := by
      apply sum_congr rfl
      intro j _
      unfold F G
      rw [←sum_sub_distrib]
      apply sum_congr rfl
      intro r _
      rw [←mul_sub,←(split r).1]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro r _
      rw [←sum_mul,sq]
  have bound := telescope F G k boundary
  rw [expansion] at bound
  let E j := ∑ r ∈ range m, (x j r)^2
  have endpoints : E 0 + E k ≤ ∑ j ∈ range (k+1), E j := by
    rw [sum_range_succ]
    exact add_le_add_right (single_le_sum (f:=E) (fun j _ => sum_nonneg (fun _ _ => sq_nonneg _))
      (mem_range.mpr (Nat.pos_of_ne_zero one))) _
  have energy : 2*(F 0-G k) ≤ E 0+E k+∑ r ∈ range m, (A r)^2 := by
    unfold F G E
    rw [←sum_sub_distrib,mul_sum,←sum_add_distrib,←sum_add_distrib]
    apply sum_le_sum
    intro r _
    nlinarith only [(split r).2,sq_nonneg (x 0 r-u r),sq_nonneg (x k r+v r)]
  change ∑ r ∈ range m, (A r)^2 ≤ ∑ j ∈ range (k+1), E j
  linarith only [bound,endpoints,energy]

/-- Probability of equal residues for independently selected entries of weight w. -/
noncomputable def collision (n m : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range n, w i * ∑ j ∈ range n, if i%m=j%m then w j else 0

private theorem by_blocks (k m : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ range (k*m), f i = ∑ h ∈ range k, ∑ r ∈ range m, f (h*m+r) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.succ_mul,sum_range_add,sum_range_succ,ih]

private theorem residueSum (k m i : ℕ) (hm : 0<m) (w : ℕ → ℝ) :
    (∑ j ∈ range (k*m), if i%m=j%m then w j else 0) =
    ∑ h ∈ range k, w (h*m+i%m) := by
  rw [by_blocks]
  apply sum_congr rfl
  intro h _
  calc
    _ = ∑ r ∈ range m, if i%m=r then w (h*m+r) else 0 := by
      apply sum_congr rfl
      intro r hr
      rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (mem_range.mp hr)]
    _ = _ := by rw [sum_ite_eq,if_pos (mem_range.mpr (Nat.mod_lt _ hm))]

theorem collision_squares (k m : ℕ) (hm : 0<m) (w : ℕ → ℝ) :
    collision (k*m) m w = ∑ r ∈ range m, (∑ h ∈ range k, w (h*m+r))^2 := by
  unfold collision
  simp_rw [residueSum k m _ hm w]
  rw [by_blocks,sum_comm]
  apply sum_congr rfl
  intro r hr
  simp only [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt (mem_range.mp hr)]
  rw [←sum_mul,sq]

private theorem diag (n : ℕ) (hn : 0<n) (w : ℕ → ℝ) :
    collision n n w = ∑ r ∈ range n, (w r)^2 := by simpa using collision_squares 1 n hn w

private theorem centered_sq (n : ℕ) (w : ℕ → ℝ) (a : ℝ) :
    ∑ i ∈ range n, (w i-a)^2 =
    (∑ i ∈ range n, (w i)^2) - 2*a*(∑ i ∈ range n, w i) + n*a^2 := by
  simp_rw [show ∀ x : ℝ, (x-a)^2=x^2-2*a*x+a^2 by intro x; ring]
  rw [sum_add_distrib,sum_sub_distrib,←mul_sum]
  simp

/-- Excess residue collision probability cannot increase when the modulus is
replaced by a divisor. The weights have total mass one. -/
theorem excess (k m : ℕ) (hk : 0<k) (hm : 0<m) (w : ℕ → ℝ) (decr : Antitone w)
    (total : ∑ i ∈ range (k*m), w i=1) :
    collision (k*m) m w-1/m ≤ collision (k*m) (k*m) w-1/(k*m:ℕ) := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  let n := (l+1)*m
  let X (h r : ℕ) := w (h*m+r)-1/(n:ℝ)
  let A (r : ℕ) := ∑ h ∈ range (l+1), w (h*m+r)
  have mp : (0:ℝ)<m := by exact_mod_cast hm
  have kp : (0:ℝ)<(l+1:ℕ) := by positivity
  have np : (0:ℝ)<n := by exact_mod_cast Nat.mul_pos hk hm
  have rowMean : ((l+1:ℕ):ℝ)*(1/(n:ℝ))=1/(m:ℝ) := by
    dsimp only [n]
    rw [Nat.cast_mul]
    field_simp
  have col (r : ℕ) : (∑ h ∈ range (l+1), X h r) = A r-1/(m:ℝ) := by
    simp only [X,A,sum_sub_distrib,sum_const,card_range,nsmul_eq_mul,rowMean]
  have tsum : ∑ r ∈ range m, A r=1 := by
    unfold A
    rw [sum_comm,←by_blocks,total]
  have sep : ∀ j<l, ∃ t : ℝ, ∀ r<m, X (j+1) r ≤ t ∧ t ≤ X j r := by
    intro j _
    refine ⟨w ((j+1)*m)-1/(n:ℝ),fun r hr => ?_⟩
    constructor
    · exact sub_le_sub_right (decr (Nat.le_add_right ..)) _
    · apply sub_le_sub_right
      apply decr
      rw [Nat.succ_mul]
      omega
  have cm : ∑ r ∈ range m, ∑ j ∈ range (l+1), X j r = 0 := by
    simp only [col,sum_sub_distrib,tsum,sum_const,card_range,nsmul_eq_mul]
    field_simp
  have contraction := fold l m X sep cm
  simp only [col,centered_sq,tsum,mul_one] at contraction
  have xe : (∑ j ∈ range (l+1), ∑ r ∈ range m, (X j r)^2) =
      (∑ i ∈ range n, (w i)^2)-2*(1/(n:ℝ))+n*(1/(n:ℝ))^2 := by
    unfold X
    rw [←by_blocks (l+1) m (fun i => (w i-1/(n:ℝ))^2),centered_sq,total,mul_one]
  have reciprocal (v : ℝ) (hv : 0<v) : v*(1/v)^2=1/v := by field_simp; ring
  rw [xe,reciprocal m mp,reciprocal n np] at contraction
  rw [collision_squares _ _ hm,diag _ (Nat.mul_pos hk hm)]
  change (∑ r ∈ range m, (A r)^2)-1/m ≤ (∑ i ∈ range n, (w i)^2)-1/(n:ℝ)
  linarith only [contraction]

/-- A proper gcd with the absolute difference of the two residue representatives. -/
def Proper (n i j : ℕ) : Prop :=
  n.gcd ((j:ℤ)-i).natAbs≠1 ∧ n.gcd ((j:ℤ)-i).natAbs≠n

noncomputable instance (n i j : ℕ) : Decidable (Proper n i j) := Classical.propDecidable _

noncomputable def probability (n : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range n, w i * ∑ j ∈ range n, if Proper n i j then w j else 0

private theorem indicator {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (i j : ℕ) (v : ℝ) : (if Proper (p*q) i j then v else 0) =
    (if i%p=j%p then v else 0)+(if i%q=j%q then v else 0)-
    2*(if i%(p*q)=j%(p*q) then v else 0) := by
  have iffmod (m : ℕ) : m ∣ ((j:ℤ)-i).natAbs ↔ i%m=j%m := by
    rw [←Int.natCast_dvd,←Nat.modEq_iff_dvd]
    rfl
  have both : i%(p*q)=j%(p*q) ↔ i%p=j%p ∧ i%q=j%q :=
    (Nat.modEq_and_modEq_iff_modEq_mul ((Nat.coprime_primes pp qp).mpr ne)).symm
  simp only [Proper,ne_eq,←Nat.coprime_iff_gcd_eq_one,Nat.coprime_mul_iff_left,
    pp.coprime_iff_not_dvd,qp.coprime_iff_not_dvd,Nat.gcd_eq_left_iff_dvd,iffmod,both]
  by_cases a : i%p=j%p <;> by_cases b : i%q=j%q <;> (simp [a,b]; try ring)

theorem inclusion_exclusion {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (w : ℕ → ℝ) : probability (p*q) w =
    collision (p*q) p w+collision (p*q) q w-2*collision (p*q) (p*q) w := by
  unfold probability collision
  simp_rw [indicator pp qp ne _ _ _,sum_sub_distrib,sum_add_distrib,←mul_sum,
    mul_sub,mul_add,show ∀ a b : ℝ, a*(2*b)=2*(a*b) by intro a b; ring]
  rw [sum_sub_distrib,sum_add_distrib,←mul_sum]

private theorem rate_eq {p q : ℕ} (hp : 0<p) (hq : 0<q) :
    (1:ℝ)/p+1/q-2/(p*q:ℕ)=(p+q-2:ℝ)/(p*q:ℕ) := by
  rw [Nat.cast_mul]
  have pp : (0:ℝ)<p := by exact_mod_cast hp
  have qp : (0:ℝ)<q := by exact_mod_cast hq
  field_simp
  ring

/-- Sharp finite probability bound, with ordinary iid weights on the residue
representatives 0,...,pq-1. Relabeling them 1,...,pq preserves every difference. -/
theorem iid_bound {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    (w : ℕ → ℝ) (decr : Antitone w) (nonneg : ∀ i<p*q, 0≤w i)
    (normal : ∑ i ∈ range (p*q), w i=1) :
    0≤probability (p*q) w ∧ probability (p*q) w≤(p+q-2:ℝ)/(p*q:ℕ) := by
  constructor
  · apply sum_nonneg
    intro i hi
    apply mul_nonneg (nonneg i (mem_range.mp hi)) (sum_nonneg ?_)
    intro j hj
    split
    · exact nonneg j (mem_range.mp hj)
    · exact le_rfl
  · have small := excess q p qp.pos pp.pos w decr (by simpa only [Nat.mul_comm q p] using normal)
    rw [Nat.mul_comm q p] at small
    have large := excess p q pp.pos qp.pos w decr normal
    rw [inclusion_exclusion pp qp ne,←rate_eq pp.pos qp.pos]
    simp only [div_eq_mul_inv,one_mul] at small large ⊢
    linarith only [small,large]

private theorem uniform_collision (k m : ℕ) (hk : 0<k) (hm : 0<m) :
    collision (k*m) m (fun _ => 1/(k*m:ℕ)) = 1/(m:ℝ) := by
  rw [collision_squares k m hm]
  simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_mul]
  have kp : (0:ℝ)<k := by exact_mod_cast hk
  have mp : (0:ℝ)<m := by exact_mod_cast hm
  field_simp
  ring

theorem uniform_attains {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q) :
    probability (p*q) (fun _ => 1/(p*q:ℕ)) = (p+q-2:ℝ)/(p*q:ℕ) := by
  rw [inclusion_exclusion pp qp ne,uniform_collision p q pp.pos qp.pos]
  have forp := uniform_collision q p qp.pos pp.pos
  rw [Nat.mul_comm q p] at forp
  have diag := uniform_collision 1 (p*q) (by decide) (Nat.mul_pos pp.pos qp.pos)
  simp only [one_mul] at diag
  rw [forp,diag,←rate_eq pp.pos qp.pos]
  ring

theorem uniform_77 : probability 77 (fun _ => 1/77) = 16/77 := by
  have h := uniform_attains (p:=7) (q:=11) (by decide) (by decide) (by decide)
  norm_num at h ⊢
  exact h

end PrimeFactors.DifferenceSampling

namespace PrimeFactors.DifferenceSampling
open Finset

/-- Nonnegative countable weights at indices 0,1,... represent draws of positive
integers 1,2,... . This common shift cancels in their difference. -/
noncomputable def residueMass (n : ℕ) (w : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑' j, w (j*n+r)

private def splitEquiv (n : ℕ) [NeZero n] : Fin n × ℕ ≃ ℕ :=
  (Equiv.prodComm _ _).trans (Nat.divModEquiv n).symm

private theorem fiberSummable {n : ℕ} (hn : 0<n) {w : ℕ → ℝ}
    (hw : Summable w) (r : ℕ) : Summable fun j => w (j*n+r) := by
  apply hw.comp_injective (i:=fun j => j*n+r)
  intro a b eq
  exact Nat.eq_of_mul_eq_mul_right hn (Nat.add_right_cancel eq)

private theorem regroup {n : ℕ} (hn : 0<n) {w : ℕ → ℝ} (hw : Summable w) :
    ∑' i, w i = ∑ r ∈ range n, residueMass n w r := by
  haveI : NeZero n := ⟨hn.ne'⟩
  let E := splitEquiv n
  have h := E.summable_iff.mpr hw
  calc
    _ = ∑' z : Fin n × ℕ, w (E z) := (E.tsum_eq w).symm
    _ = ∑' r : Fin n, ∑' j : ℕ, w (E (r,j)) := h.tsum_prod
    _ = _ := by rw [tsum_fintype]; exact Fin.sum_univ_eq_sum_range (residueMass n w) n

/-- The folded countable law has total mass one and is nonincreasing. -/
theorem folded_law {n : ℕ} (hn : 0<n) {w : ℕ → ℝ} (decr : Antitone w)
    (pos : ∀ i, 0≤w i) (norm : HasSum w 1) :
    Antitone (residueMass n w) ∧ (∀ i, 0≤residueMass n w i) ∧
    ∑ r ∈ range n, residueMass n w r = 1 := by
  refine ⟨?_, fun i => tsum_nonneg (fun j => pos _), (regroup hn norm.summable).symm.trans norm.tsum_eq⟩
  intro a b ab
  exact Summable.tsum_le_tsum (fun j => decr (Nat.add_le_add_left ab (j*n)))
    (fiberSummable hn norm.summable b) (fiberSummable hn norm.summable a)

/-- Changing either representative by multiples of the modulus preserves the proper gcd. -/
theorem proper_mod (n i j : ℕ) : Proper n i j ↔ Proper n (i%n) (j%n) := by
  let d := ((j:ℤ)-i).natAbs
  let d' := (((j%n:ℕ):ℤ)-(i%n:ℕ)).natAbs
  have same {m : ℕ} (mn : m∣n) : m∣d ↔ m∣d' := by
    dsimp only [d,d']
    rw [←Int.natCast_dvd,←Int.natCast_dvd,←Nat.modEq_iff_dvd,←Nat.modEq_iff_dvd]
    simp only [Nat.ModEq,Nat.mod_mod_of_dvd _ mn]
  have eq : n.gcd d=n.gcd d' := by
    apply Nat.dvd_antisymm
    · exact Nat.dvd_gcd (Nat.gcd_dvd_left ..)
        ((same (Nat.gcd_dvd_left ..)).mp (Nat.gcd_dvd_right ..))
    · exact Nat.dvd_gcd (Nat.gcd_dvd_left ..)
        ((same (Nat.gcd_dvd_left ..)).mpr (Nat.gcd_dvd_right ..))
  change (_ ∧ _) ↔ (_ ∧ _)
  change (n.gcd d≠1 ∧ n.gcd d≠n) ↔ (n.gcd d'≠1 ∧ n.gcd d'≠n)
  rw [eq]

/-- The mass of each ordered pair in the independent product law. -/
noncomputable def joint (w : ℕ → ℝ) (z : ℕ × ℕ) : ℝ := w z.1*w z.2

theorem joint_law {w : ℕ → ℝ} (pos : ∀ i, 0≤w i) (norm : HasSum w 1) :
    HasSum (joint w) 1 := by
  simpa only [one_mul] using norm.mul norm
    (norm.summable.mul_of_nonneg norm.summable pos pos)

noncomputable def infiniteProbability (n : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑' z : ℕ × ℕ, if Proper n z.1 z.2 then joint w z else 0

/-- Equality between the probability of the actual countable gcd event and the
finite residue expression. This step does not require monotone weights. -/
theorem regroup_joint {n : ℕ} (hn : 0<n) {w : ℕ → ℝ} (pos : ∀ i, 0≤w i)
    (law : HasSum w 1) : infiniteProbability n w = probability n (residueMass n w) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  let hit (z : ℕ × ℕ) := if Proper n z.1 z.2 then joint w z else 0
  have jointPos (z : ℕ × ℕ) : 0 ≤ joint w z := mul_nonneg (pos _) (pos _)
  have hitS : Summable hit := Summable.of_nonneg_of_le
    (fun z => by dsimp only [hit]; split <;> first | exact jointPos z | exact le_rfl)
    (fun z => by dsimp only [hit]; split <;> first | exact le_rfl | exact jointPos z)
    (joint_law pos law).summable
  let E := (Equiv.prodProdProdComm (Fin n) (Fin n) ℕ ℕ).trans
    (Equiv.prodCongr (splitEquiv n) (splitEquiv n))
  have reindexed := E.summable_iff.mpr hitS
  have part (r : Fin n × Fin n) : (∑' j : ℕ × ℕ, hit (E (r,j))) =
      if Proper n r.1 r.2 then residueMass n w r.1 * residueMass n w r.2 else 0 := by
    have point (j : ℕ × ℕ) : Proper n ((E (r,j)).1) ((E (r,j)).2) ↔ Proper n r.1 r.2 := by
      change Proper n (j.1*n+r.1) (j.2*n+r.2) ↔ Proper n r.1 r.2
      rw [proper_mod n (j.1*n+r.1) (j.2*n+r.2)]
      simp only [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt r.1.isLt,Nat.mod_eq_of_lt r.2.isLt]
    by_cases valid : Proper n r.1 r.2
    · simp only [if_pos valid]
      have sw := fiberSummable hn law.summable (r.1:ℕ)
      have tw := fiberSummable hn law.summable (r.2:ℕ)
      have mult := sw.tsum_mul_tsum tw (sw.mul_of_nonneg tw (fun _ => pos _) (fun _ => pos _))
      refine (tsum_congr (fun j => ?_)).trans mult.symm
      exact if_pos ((point j).mpr valid)
    · simp only [if_neg valid]
      exact (tsum_congr fun j => if_neg (valid ∘ (point j).mp)).trans tsum_zero
  calc
    infiniteProbability n w = ∑' z, hit (E z) := (E.tsum_eq hit).symm
    _ = ∑' r : Fin n × Fin n, ∑' j : ℕ × ℕ, hit (E (r,j)) := reindexed.tsum_prod
    _ = ∑ r : Fin n × Fin n, if Proper n r.1 r.2 then
          residueMass n w r.1*residueMass n w r.2 else 0 := by simp only [part,tsum_fintype]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      unfold probability
      simp only [mul_sum,mul_ite,mul_zero]
      exact (Fin.sum_univ_eq_sum_range (fun i =>
        ∑ j : Fin n, if Proper n i j then residueMass n w i*residueMass n w j else 0) n).trans
        (sum_congr rfl (fun i _ => Fin.sum_univ_eq_sum_range (fun j =>
          if Proper n i j then residueMass n w i*residueMass n w j else 0) n))

/-- A countable probability mass function used as an iid pair of draws. The
event includes a direct gcd of the absolute difference, and probability is a
single convergent sum over the entire ordered product space. -/
theorem countable_iid_bound {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ne : p≠q)
    {w : ℕ → ℝ} (decr : Antitone w) (pos : ∀ i, 0≤w i) (norm : HasSum w 1) :
    0 ≤ infiniteProbability (p*q) w ∧ infiniteProbability (p*q) w≤(p+q-2:ℝ)/(p*q:ℕ) := by
  have hn := Nat.mul_pos pp.pos qp.pos
  obtain ⟨d,h,z⟩ := folded_law hn decr pos norm
  rw [regroup_joint hn pos norm]
  exact iid_bound pp qp ne _ d (fun r _ => h r) z

end PrimeFactors.DifferenceSampling
