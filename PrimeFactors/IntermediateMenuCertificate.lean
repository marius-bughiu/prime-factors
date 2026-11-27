import PrimeFactors.IntermediateBlockCutoff
import PrimeFactors.LcmConvergentObstruction
import PrimeFactors.ProductDeficitBand

/-! Replaying a finite public exponent menu can certify the absence of any upper intermediate
row for a whole interval of possible integer totients. This verifier never needs the factors. -/
namespace PrimeFactors.IntermediateMenuCertificate

open IntermediateBlockCutoff (locateInterval retain)
open IntermediateTotientObstruction (Hit rowAt)
open LcmConvergentObstruction (prefixLCM)

def excludesInteger (N E i t : ℕ) : Bool :=
  match rowAt i t E N ⟨0,1⟩ ⟨1,0⟩ with
  | none => true
  | some z => E*z.b%z.a != 0

/-- The cardinality of the coefficient interval, with zero for an empty window. -/
def windowWidth (N E L H : ℕ) : ℕ :=
  match locateInterval N E L H with
  | none => 0
  | some w => w.hi+1-w.lo

/-- Check all coefficients in the unique possible window, including both endpoints. -/
noncomputable def goodWindow (N E L H : ℕ) : Bool :=
  match locateInterval N E L H with
  | none => true
  | some w => (List.range (w.hi+1-w.lo)).all fun k => excludesInteger N E w.index (w.lo+k)

/-- A positive integer F in the specified band is ruled out by the Boolean certificate. -/
theorem excludes {N E L H F : ℕ} (ep : 0<E) (lp : 0<L) (hp : 0<H) (cap : H≤2*L)
    (fn : F≤N) (lo : L≤N-F) (hi : N-F<H) (ok : goodWindow N E L H=true) : ¬Hit N E F := by
  rintro ⟨i,t,z,found,bp,eq⟩
  have ap : 0<z.a := by
    have pos := Nat.mul_pos ep bp
    rw [eq] at pos
    exact Nat.pos_of_mul_pos_right pos
  obtain ⟨w,win,idx,bot,top⟩ := retain lp hp cap fn lo hi ap found eq
  simp only [goodWindow,win,List.all_eq_true] at ok
  have k : t-w.lo∈List.range (w.hi+1-w.lo) := List.mem_range.mpr (by omega)
  have bad := ok _ k
  rw [Nat.add_sub_of_le bot,idx] at bad
  simp [excludesInteger,found,eq] at bad

/-- Run the positive prefix LCMs once, adding each newly reached eligible value once.
The finite public gate is exactly the one used in the benchmark. -/
def profile (N : ℕ) : ℕ → ℕ × List ℕ
  | 0 => (1,if 1≤N ∧ 4*N≤(1+1)^2 then [1] else [])
  | j+1 =>
    let (old,values) := profile N j
    let E := old.lcm (j+1)
    (E,if E≠old ∧ E≤N ∧ 4*N≤(E+1)^2 then E::values else values)

theorem profile_value (N j : ℕ) : (profile N j).1=prefixLCM j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [profile,prefixLCM,←ih]

/-- Every qualifying index is represented, including a repeated LCM after its original
insertion. Coverage is over the indices themselves, independent of the number of repeats. -/
theorem profile_mem {N j k : ℕ} (lim : j≤k) (en : prefixLCM j≤N)
    (gate : 4*N≤(prefixLCM j+1)^2) : prefixLCM j ∈ (profile N k).2 := by
  induction k generalizing j with
  | zero =>
    have jo : j=0 := by omega
    subst j
    change 1 ∈ (if 1≤N ∧ 4*N≤(1+1)^2 then [1] else [])
    rw [if_pos ⟨en,gate⟩]
    exact List.mem_cons_self
  | succ k ih =>
    simp only [profile]
    by_cases jk : j≤k
    · have already := ih jk en gate
      split <;> simp_all
    have jo : j=k+1 := by omega
    subst j
    change prefixLCM (k+1) ∈
      (if (profile N k).1.lcm (k+1)≠(profile N k).1 ∧
        (profile N k).1.lcm (k+1)≤N ∧ 4*N≤((profile N k).1.lcm (k+1)+1)^2
       then (profile N k).1.lcm (k+1)::(profile N k).2 else (profile N k).2)
    rw [profile_value]
    change _ ∈ (if prefixLCM (k+1)≠prefixLCM k ∧ _ then _ else _)
    by_cases same : prefixLCM (k+1)=prefixLCM k
    · rw [if_neg (fun h => h.1 same),same]
      exact ih le_rfl (same ▸ en) (same ▸ gate)
    · rw [if_pos ⟨same,en,gate⟩]
      exact List.mem_cons_self

/-- Transfer a verified finite menu to every admissible 2048-bit prefix index and every
pair of odd factors of the advertised width. No primality certificate or private factors
are used for the input identification or to derive the bounds on its totient candidate. -/
theorem control {N A L H : ℕ} (lower : 2^2047≤N) (upper : N<2^2048)
    (ap : 0<A) (even : Even A) (hl : ProductDeficitBand.lower N A=L)
    (hh : ProductDeficitBand.upper N A=H)
    (ok : ((profile N 1432).2.all (fun E => goodWindow N E L H))=true)
    {p q j : ℕ} (product : p*q=N) (po : Odd p) (qo : Odd q)
    (pl : A≤p) (ql : A≤q) (pu : p<2*A) (qu : q<2*A)
    (fits : prefixLCM j≤N) (gate : 4*N≤(prefixLCM j+1)^2) :
    ¬ Hit N (prefixLCM j) ((p-1)*(q-1)) := by
  have mem := profile_mem ((LcmConvergentObstruction.admissible lower upper).1 fits) fits gate
  have win := (List.all_eq_true.mp ok) _ mem
  have band := ProductDeficitBand.contains ap even po qo pl ql pu qu
  rw [product,hl,hh] at band
  have eq := PowerImageWidth.offset (ap.trans_le pl) (ap.trans_le ql)
  rw [product] at eq
  have lp : 0<L := by
    rw [←hl,ProductDeficitBand.lower]
    exact (by omega : 0<2*A+1).trans_le (le_max_left ..)
  have cap := ProductDeficitBand.dyadic (N:=N) (A:=A)
  rw [hl,hh] at cap
  exact excludes (LcmConvergentObstruction.prefix_pos _) lp (by omega) cap (by omega)
    (by omega) (by omega) win

/-- On the small positive benchmark, the verifier rejects the no-integer claim.
The single surviving row gives the exact integer 102060 from the public exponent. -/
theorem positive_control : windowWidth 102709 2520 641 656=1 ∧
    goodWindow 102709 2520 641 656=false ∧
    rowAt 3 1 2520 102709 ⟨0,1⟩ ⟨1,0⟩=some ⟨2,81⟩ ∧
    2520*81=2*102060 := by decide +kernel

end PrimeFactors.IntermediateMenuCertificate
