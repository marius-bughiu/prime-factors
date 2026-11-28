import PrimeFactors.FloorSquareShift
import PrimeFactors.GaussianMidpointScreen
import PrimeFactors.Fermat

/-! All dyadic sum readings above the square root, expressed as
classes of candidate midpoints with exact lower endpoints. -/
namespace PrimeFactors.CeilingShiftCandidateClasses
open FloorSquareShift Finset

def reading (n m : ℕ) := 2*m+twoPart (m^2-n)

private def step (r : ℕ) := if r%4=3 then 1 else if r%8=5 then 2 else 4
def distance (n : ℕ) := step (n%16)

def residueClass (r c : ℕ) : Prop :=
  if r%4=3 then c%2=0 else if r%8=5 then c%2=1 else c^2%16=r
private instance (r c : ℕ) : Decidable (residueClass r c) := by unfold residueClass; infer_instance

def Candidate (n C : ℕ) : Prop := residueClass (n%16) (C%16)

def Represented (n C : ℕ) : Prop :=
  ∃ m, ceilSqrt n≤m ∧ m<C ∧ reading n m=2*C

private def digit (r z : ℕ) := (z^2%16+16-r)%16
private def lowPart (r z : ℕ) := (digit r z).gcd 16

private theorem odd_res {n : ℕ} (hn : Odd n) : n%16%2=1 := by obtain ⟨a,ha⟩ := hn; omega

private theorem low {d : ℕ} (pos : 0<d) :
    (d%16).gcd 16≤twoPart d ∧ twoPart d ≡ (d%16).gcd 16 [MOD 16] ∧
    ((d%16).gcd 16<16 → twoPart d=(d%16).gcd 16) := by
  obtain ⟨j,h,odd,part⟩ := Nat.exists_eq_two_pow_mul_odd pos.ne'
  have term : d=h*2^j := part.trans (mul_comm _ _)
  rw [term,twoPart_odd_mul j odd]
  by_cases small : j<4
  · have table : ∀ i : Fin 4, ∀ v : Fin 16, v.val%2=1 →
        ((v.val*2^i.val)%16).gcd 16=2^i.val := by decide +kernel
    have vg := table ⟨j,small⟩ ⟨h%16,Nat.mod_lt _ (by decide)⟩ (odd_res odd)
    have md := (Nat.mod_modEq h 16).mul_right (2^j)
    change ((h%16*2^j)%16).gcd 16=2^j at vg
    rw [show (h%16*2^j)%16=(h*2^j)%16 from md] at vg
    simp only [vg,le_refl,Nat.ModEq.refl,implies_true,and_self]
  · have dv : 16∣2^j := Nat.pow_dvd_pow 2 (show 4≤j by omega)
    have hm := Nat.mod_eq_zero_of_dvd (dv.trans (dvd_mul_left _ h))
    rw [hm,Nat.gcd_zero_left]
    refine ⟨Nat.le_of_dvd (by positivity) dv,?_,by omega⟩
    exact (Nat.modEq_zero_iff_dvd.mpr dv).trans (Nat.modEq_zero_iff_dvd.mpr (dvd_refl 16)).symm

private theorem square_digit (n m : ℕ) (above : n≤m^2) :
    (m^2-n)%16=digit (n%16) (m%16) := by
  have md := (Nat.mod_modEq m 16).pow 2
  change (m%16)^2%16=m^2%16 at md
  unfold digit
  rw [md]
  omega

private theorem positive_gap {n m : ℕ} (ns : ∀ j : ℕ, n≠j^2) (lo : ceilSqrt n≤m) : n<m^2 :=
  (ceilSqrt_le_iff.mp lo).lt_of_ne (ns m)

private theorem necessity {n C m : ℕ} (odd : Odd n) (above : n<m^2) (eqn : reading n m=2*C) :
    m+distance n≤C ∧ Candidate n C := by
  have tab : ∀ r z c : Fin 16, r.val%2=1 →
      (2*z.val+lowPart r.val z.val)%16=2*c.val%16 →
      2*step r.val≤lowPart r.val z.val ∧ residueClass r.val c.val := by decide +kernel
  obtain ⟨min,mod,_⟩ := low (Nat.sub_pos_of_lt above)
  rw [square_digit n m above.le] at min mod
  change lowPart (n%16) (m%16)≤twoPart (m^2-n) at min
  change twoPart (m^2-n) ≡ lowPart (n%16) (m%16) [MOD 16] at mod
  change 2*m+twoPart (m^2-n)=2*C at eqn
  have con := ((Nat.mod_modEq m 16).mul_left 2).add mod.symm
  rw [eqn] at con
  have match' := con.trans ((Nat.mod_modEq C 16).mul_left 2).symm
  obtain ⟨stepLe,cl⟩ := tab ⟨n%16,Nat.mod_lt _ (by decide)⟩ ⟨m%16,Nat.mod_lt _ (by decide)⟩
    ⟨C%16,Nat.mod_lt _ (by decide)⟩ (odd_res odd) match'
  change 2*distance n≤lowPart (n%16) (m%16) at stepLe
  exact ⟨by omega,cl⟩

/-- The single nearest permitted distance gives an exact reading of every allowed
candidate, once that center is at least the ceiling square root. -/
theorem canonical {n C : ℕ} (odd : Odd n) (ns : ∀ j : ℕ, n≠j^2)
    (lo : ceilSqrt n+distance n≤C) (cl : Candidate n C) :
    reading n (C-distance n)=2*C := by
  let m := C-distance n
  have eqn : m+distance n=C := by dsimp [m]; omega
  have above := positive_gap ns (m:=m) (by omega)
  have tab : ∀ r z c : Fin 16, r.val%2=1 → residueClass r.val c.val →
      (z.val+step r.val)%16=c.val →
      lowPart r.val z.val=2*step r.val ∧ lowPart r.val z.val<16 := by decide +kernel
  have md := (Nat.mod_modEq m 16).add_right (distance n)
  rw [eqn] at md
  obtain ⟨value,small⟩ := tab ⟨n%16,Nat.mod_lt _ (by decide)⟩ ⟨m%16,Nat.mod_lt _ (by decide)⟩
    ⟨C%16,Nat.mod_lt _ (by decide)⟩ (odd_res odd) cl md
  have exactPart := (low (Nat.sub_pos_of_lt above)).2.2
  rw [square_digit n m above.le] at exactPart
  have t : twoPart (m^2-n)=2*distance n := (exactPart small).trans value
  change 2*m+twoPart (m^2-n)=2*C
  omega

/-- Includes every first-window boundary. A center at the ceiling is allowed. -/
theorem represented_iff {n C : ℕ} (odd : Odd n) (ns : ∀ j : ℕ, n≠j^2) :
    Represented n C ↔ ceilSqrt n+distance n≤C ∧ Candidate n C := by
  constructor
  · rintro ⟨m,lo,_,eqn⟩
    obtain ⟨cap,cl⟩ := necessity odd (positive_gap ns lo) eqn
    exact ⟨by omega,cl⟩
  · rintro ⟨lo,cl⟩
    have dp : 0<distance n := by unfold distance step; split <;> simp_all [ite_pos,ite_neg]
    exact ⟨C-distance n,by omega,by omega,canonical odd ns lo cl⟩

theorem classes (n C : ℕ) :
    distance n=(if n%4=3 then 1 else if n%8=5 then 2 else 4) ∧
    (Candidate n C ↔ if n%4=3 then C%2=0 else if n%8=5 then C%2=1 else C^2%16=n%16) := by
  have p := (Nat.mod_modEq C 16).pow 2
  have g : n%16%4=n%4 := by omega
  have h : n%16%8=n%8 := by omega
  have i : C%16%2=C%2 := by omega
  simp only [distance,step,Candidate,residueClass,g,h,i,show (C%16)^2%16=C^2%16 from p,iff_self,and_self]

/-- Every ordinary modulo-16 square survivor has an exactly-reading center
when its canonical index lies in the search interval. -/
theorem screen_candidate {n C : ℕ} (odd : Odd n) (screen : GaussianMidpointScreen.Screen 16 n C) :
    Candidate n C := by
  obtain ⟨z,eqn⟩ := screen
  have m := ((Nat.mod_modEq C 16).pow 2).trans eqn
  have res := (Nat.mod_modEq n 16).add ((Nat.mod_modEq z 16).pow 2)
  have ar := m.trans res.symm
  have tab : ∀ r c z : Fin 16, r.val%2=1 → c.val^2 ≡ r.val+z.val^2 [MOD 16] →
      residueClass r.val c.val := by decide +kernel
  exact tab ⟨n%16,Nat.mod_lt _ (by decide)⟩ ⟨C%16,Nat.mod_lt _ (by decide)⟩
    ⟨z%16,Nat.mod_lt _ (by decide)⟩ (odd_res odd) ar

open scoped Classical in
/-- Equality of the filtered lists, including the exact cutoff on the first few centers. -/
theorem screened_filter {n : ℕ} (odd : Odd n) (ns : ∀ j : ℕ, n≠j^2) (A : Finset ℕ) :
    (A.filter (fun C => GaussianMidpointScreen.Screen 16 n C ∧ Represented n C)) =
    A.filter (fun C => GaussianMidpointScreen.Screen 16 n C ∧ ceilSqrt n+distance n≤C) := by
  classical
  ext C
  simp only [mem_filter,represented_iff odd ns]
  constructor
  · exact fun h => ⟨h.1,h.2.1,h.2.2.1⟩
  · exact fun h => ⟨h.1,h.2.1,h.2.2,screen_candidate odd h.2.1⟩

/-- In every complete period, four of sixteen midpoint residues pass the ordinary
square screen, and all of them also meet the dyadic reading condition. -/
theorem class_sizes (n : ℕ) (odd : Odd n) :
    ((univ : Finset (Fin 16)).filter (fun c => residueClass (n%16) c.val)).card =
      (if n%8=1 then 4 else 8) ∧
    ((univ : Finset (Fin 16)).filter (fun c =>
      ∃ z : Fin 16, c.val^2%16=((n%16)+z.val^2)%16)).card=4 := by
  have tab : ∀ r : Fin 16, r.val%2=1 →
      ((univ : Finset (Fin 16)).filter (fun c => residueClass r.val c.val)).card=
        (if r.val%8=1 then 4 else 8) ∧
      ((univ : Finset (Fin 16)).filter (fun c =>
        ∃ z : Fin 16, c.val^2%16=(r.val+z.val^2)%16)).card=4 := by decide +kernel
  simpa only [show n%16%8=n%8 by omega] using tab ⟨n%16,Nat.mod_lt _ (by decide)⟩ (odd_res odd)

private theorem evaluated {n m C h j : ℕ} (odd : Odd h) (excess : m^2-n=h*2^j)
    (sum : 2*m+2^j=2*C) : reading n m=2*C := by
  rwa [reading,excess,twoPart_odd_mul j odd]

/-- The same reading and modulo-16 screen support a false and a true
candidate on 8509. The two neighboring squares reject the false one. -/
theorem controls :
    Nat.Prime 67 ∧ Nat.Prime 73 ∧ Nat.Prime 127 ∧
    8509=67*127 ∧ reading 8509 93=2*95 ∧ GaussianMidpointScreen.Screen 16 8509 95 ∧
    22^2<95^2-8509 ∧ 95^2-8509<23^2 ∧
    reading 8509 95=2*97 ∧ 97^2-8509=30^2 ∧
    9271=73*127 ∧ reading 9271 99=2*100 ∧ 100^2-9271=27^2 := by
  refine ⟨by norm_num,by norm_num,by norm_num,by norm_num,?_,⟨2,by norm_num [Nat.ModEq]⟩,
    by norm_num,by norm_num,?_,by norm_num,by norm_num,?_,by norm_num⟩
  · exact evaluated (j:=2) (h:=35) (by decide) (by norm_num) (by norm_num)
  · exact evaluated (j:=2) (h:=129) (by decide) (by norm_num) (by norm_num)
  · exact evaluated (j:=1) (h:=265) (by decide) (by norm_num) (by norm_num)

end PrimeFactors.CeilingShiftCandidateClasses
