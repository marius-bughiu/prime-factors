import PrimeFactors.AffineExcessSingle
import PrimeFactors.GapStride
import Mathlib.Tactic

/-! Removing integer dilations of the same multiplier-Fermat test. -/
namespace PrimeFactors.PrimitiveMultiplierTraces

open Finset

def start (n k : ℕ) := ceilSqrt (4*k*n)

def Primitive (k s : ℕ) : Prop := ∀ d : ℕ, d^2 ∣ k → d ∣ s → d ≤ 1

/-- Every positive multiplier row is an integer dilation of a primitive row. -/
theorem reduction (k s : ℕ) (kp : 0<k) :
    ∃ d k₀ s₀ : ℕ, 0<d ∧ 0<k₀ ∧ k=d^2*k₀ ∧ s=d*s₀ ∧ Primitive k₀ s₀ := by
  induction k using Nat.strong_induction_on generalizing s with
  | h k ih =>
    by_cases prim : Primitive k s
    · exact ⟨1,k,s,by decide,kp,by simp,by simp,prim⟩
    simp only [Primitive,not_forall,exists_prop,not_le] at prim
    obtain ⟨d,⟨k',hk⟩,⟨s',hs⟩,big⟩ := prim
    have kp' : 0<k' := Nat.pos_of_ne_zero (by rintro rfl; simp_all)
    have small : k'<k := by
      rw [hk]; exact (lt_mul_iff_one_lt_left kp').mpr (by nlinarith)
    obtain ⟨e,u,v,ep,up,ku,sv,prim'⟩ := ih k' small s' kp'
    exact ⟨d*e,u,v,Nat.mul_pos (by omega) ep,up,by rw [hk,ku]; ring,by rw [hs,sv]; ring,prim'⟩

/-- Distinct primitive rows of positive trace have distinct rational values
s²/k. Thus reducing in any order leads to the same representative. -/
theorem unique {k s l t : ℕ} (sp : 0<s) (tp : 0<t)
    (one : Primitive k s) (two : Primitive l t) (eq : k*t^2=l*s^2) : k=l ∧ s=t := by
  let g := s.gcd t
  let a := s/g
  let b := t/g
  have gp : 0<g := Nat.gcd_pos_of_pos_left t sp
  have sav : g*a=s := Nat.mul_div_cancel' (Nat.gcd_dvd_left s t)
  have tbv : g*b=t := Nat.mul_div_cancel' (Nat.gcd_dvd_right s t)
  have ac : a.Coprime b := Nat.coprime_div_gcd_div_gcd gp
  have eq' : k*b^2=l*a^2 := Nat.mul_left_cancel (Nat.pow_pos gp) (by
    calc g^2*(k*b^2) = k*(g*b)^2 := by ring
         _ = l*(g*a)^2 := by rw [tbv,sav,eq]
         _ = g^2*(l*a^2) := by ring)
  have h₁ : a^2 ∣ k := (ac.pow 2 2).dvd_of_dvd_mul_right (eq' ▸ dvd_mul_left _ _)
  have h₂ : b^2 ∣ l := (ac.symm.pow 2 2).dvd_of_dvd_mul_right (eq'.symm ▸ dvd_mul_left _ _)
  have a1 := one a h₁ (sav ▸ dvd_mul_left _ _)
  have b1 := two b h₂ (tbv ▸ dvd_mul_left _ _)
  have a' : a=1 := by
    rcases Nat.eq_zero_or_pos a with h|h
    · rw [h,mul_zero] at sav
      omega
    · omega
  have b' : b=1 := by
    rcases Nat.eq_zero_or_pos b with h|h
    · rw [h,mul_zero] at tbv
      omega
    · omega
  simp_all

theorem start_scaled_iff {n d k s : ℕ} (dp : 0<d) :
    start n (d^2*k) ≤ d*s ↔ start n k ≤ s := by
  simp only [start,ceilSqrt_le_iff, mul_pow]
  rw [show 4*(d^2*k)*n=d^2*(4*k*n) by ring]
  exact ⟨fun h => Nat.le_of_mul_le_mul_left h (Nat.pow_pos dp),
    Nat.mul_le_mul_left _⟩

/-- Removing a dilation keeps the row in the same complete consecutive prefix. -/
theorem contract {n d k s H K : ℕ} (dp : 0<d) (cap : d^2*k≤K)
    (lo : start n (d^2*k) ≤ d*s) (hi : d*s < start n (d^2*k)+H) :
    k≤K ∧ start n k≤s ∧ s<start n k+H := by
  have first := (start_scaled_iff (n:=n) (k:=k) dp).mpr (le_refl _)
  refine ⟨le_trans (Nat.le_mul_of_pos_left _ (Nat.pow_pos dp)) cap,
    (start_scaled_iff dp).mp lo, ?_⟩
  by_contra! h
  have z := Nat.mul_le_mul_left d h
  rw [Nat.mul_add] at z
  have := Nat.le_mul_of_pos_left H dp
  omega

/-- The higher discriminant is a square precisely when the lower one is,
including zero. -/
theorem square_iff {n d k s : ℕ} (dp : 0<d) :
    (∃ v : ℕ, (d*s)^2=v^2+4*(d^2*k)*n) ↔ ∃ u : ℕ, s^2=u^2+4*k*n := by
  constructor
  · rintro ⟨v,h⟩
    have dv : d^2∣v^2 := by
      apply (Nat.dvd_add_iff_left (show d^2∣4*(d^2*k)*n from ⟨4*k*n,by ring⟩)).mpr
      rw [←h,mul_pow]; exact dvd_mul_right _ _
    obtain ⟨u,hu⟩ := (Nat.pow_dvd_pow_iff two_ne_zero).mp dv
    exact ⟨u,Nat.mul_left_cancel (Nat.pow_pos dp) <| by
      calc d^2*s^2 = (d*s)^2 := (mul_pow _ _ _).symm
           _ = (d*u)^2+4*(d^2*k)*n := by rw [h,hu]
           _ = d^2*(u^2+4*k*n) := by ring⟩
  · rintro ⟨u,hu⟩
    exact ⟨d*u,by rw [mul_pow d s,hu]; ring⟩

/-- These are the actual half-trace gcds used after a square test. -/
theorem gcd_outcomes {d n s u : ℕ} (unit : d.Coprime n)
    (plus : 2∣s+u) (minus : 2∣s-u) :
    ((d*s+d*u)/2).gcd n=((s+u)/2).gcd n ∧
    ((d*s-d*u)/2).gcd n=((s-u)/2).gcd n := by
  rw [←Nat.mul_add,←Nat.mul_sub,Nat.mul_div_assoc d plus,Nat.mul_div_assoc d minus]
  exact ⟨unit.gcd_mul_left_cancel _,unit.gcd_mul_left_cancel _⟩

/-- Parity of the two square roots follows from the discriminant equation,
so the two half-trace gcds require no extra hypothesis on the input. -/
theorem hit_gcd {d n k s u : ℕ} (unit : d.Coprime n) (hit : s^2=u^2+4*k*n) :
    ((d*s+d*u)/2).gcd n=((s+u)/2).gcd n ∧
    ((d*s-d*u)/2).gcd n=((s-u)/2).gcd n := by
  have parity (x : ℕ) : x^2%2=x%2 := by
    rw [sq,Nat.mul_mod]
    rcases (show x%2=0 ∨ x%2=1 by omega) with h|h <;> rw [h]
  have hm : s^2=u^2+2*(2*k*n) := by rw [hit]; ring
  have hs := parity s
  have hu := parity u
  apply gcd_outcomes unit <;> omega

/-- The union of the residue images of all ordered factorisations k=ab.
The public residue pair stands for the two factors of n modulo m. -/
def Admits (m n k s : ℕ) : Prop :=
  ∃ a b u v : ℕ, a*b=k ∧ u*v ≡ n [MOD m] ∧ s ≡ a*u+b*v [MOD m]

/-- Every integer square has an admissible trace for the union of all
orientations. This also covers a square whose half-traces give trivial gcds. -/
theorem admits_of_square {m n k s z : ℕ} (kp : 0<k) (hit : s^2=z^2+4*k*n) :
    Admits m n k s := by
  obtain ⟨x,sum,prod⟩ := AffineExcessSingle.halves (H:=k*n) (by
    simpa only [←Nat.mul_assoc,add_comm] using hit)
  obtain ⟨a,b,⟨u,hu⟩,⟨v,hv⟩,kab⟩ := exists_dvd_and_dvd_of_dvd_mul
    (show k ∣ x*(x+z) from ⟨n,prod⟩)
  have uv : u*v=n := Nat.eq_of_mul_eq_mul_left kp <| calc
    k*(u*v) = (a*u)*(b*v) := by rw [kab]; ring
    _ = x*(x+z) := by rw [←hu,←hv]
    _ = k*n := prod
  have trace : s=a*u+b*v := by rw [←hu,←hv]; omega
  exact ⟨a,b,u,v,kab.symm,uv ▸ Nat.ModEq.refl _,trace ▸ Nat.ModEq.refl _⟩

/-- Form of the eight-residue wheel used by the comparison program. -/
theorem square_in_mod24_menu {n k s z : ℕ} (unit : n.Coprime 6) (kp : 0<k)
    (hit : s^2=z^2+4*k*n) :
    ∃ a b r : ℕ, a*b=k ∧ r∈[1,5,7,11,13,17,19,23] ∧ s ≡ (a+b*n)*r [MOD 24] := by
  obtain ⟨a,b,u,v,ab,uv,tr⟩ := admits_of_square (m:=24) kp hit
  have unitProd : (u*v).Coprime 6 := ((uv.of_dvd (by decide : 6 ∣ 24)).gcd_eq).trans unit
  have uc : u.Coprime 6 := unitProd.coprime_dvd_left (dvd_mul_right u v)
  have sq := square_mod_twentyfour uc
  have vu : v ≡ n*u [MOD 24] := calc
    v ≡ u^2*v [MOD 24] := by simpa using (sq.mul_right v).symm
    _ = (u*v)*u := by ring
    _ ≡ n*u [MOD 24] := uv.mul_right u
  have r := Nat.mod_modEq u 24
  have uc24 := (uc.pow_right 3).coprime_dvd_right (by decide : 24∣6^3)
  have finite : ∀ x : Fin 24, (x:ℕ).Coprime 24 → (x:ℕ)∈[1,5,7,11,13,17,19,23] := by
    decide +kernel
  refine ⟨a,b,u%24,ab,finite ⟨_,Nat.mod_lt _ (by decide)⟩ (r.gcd_eq.trans uc24),?_⟩
  calc s ≡ a*u+b*v [MOD 24] := tr
       _ ≡ a*u+b*(n*u) [MOD 24] := (Nat.ModEq.refl _).add (vu.mul_left b)
       _ = (a+b*n)*u := by ring
       _ ≡ (a+b*n)*(u%24) [MOD 24] := r.symm.mul_left _

theorem admits_scaled {m n k s : ℕ} (d : ℕ) (h : Admits m n k s) :
    Admits m n (d^2*k) (d*s) := by
  obtain ⟨a,b,u,v,hab,huv,hs⟩ := h
  exact ⟨d*a,d*b,u,v,by rw [←hab]; ring,huv,by
    simpa only [Nat.mul_add,Nat.mul_assoc] using hs.mul_left d⟩

/-- A wheel may use a different set of admissible labels in every lane.
If it accepts integer dilations, contracting an admissible square never
increases the number of earlier admissible labels. -/
theorem wheel_rank {n d k s : ℕ} (dp : 0<d) (P : ℕ→ℕ→Prop)
    [DecidablePred (P k)] [DecidablePred (P (d^2*k))]
    (lift : ∀ t, P k t → P (d^2*k) (d*t)) :
    ((Ico (start n k) s).filter (P k)).card ≤
      ((Ico (start n (d^2*k)) (d*s)).filter (P (d^2*k))).card := by
  apply card_le_card_of_injOn (fun z => d*z)
  · intro t ht
    obtain ⟨⟨lo,hi⟩,ok⟩ := (show (start n k≤t ∧ t<s) ∧ P k t by simpa using ht)
    simpa using (show (start n (d^2*k)≤d*t ∧ d*t<d*s) ∧ P (d^2*k) (d*t) from
      ⟨⟨(start_scaled_iff dp).mpr lo,Nat.mul_lt_mul_of_pos_left hi dp⟩,lift t ok⟩)
  · exact fun _ _ _ _ h => Nat.mul_left_cancel dp h

/-- In a lane divisible by four, the union of orientations admits one fixed
even residue in each period. Among any consecutive block of admitted rows,
at least one in thirteen (rounded down) therefore contracts by two. -/
theorem wheel_even_count (n h l length : ℕ) [DecidablePred (Admits 24 n (4*h))] :
    let rows := (Ico l (l+length)).filter (Admits 24 n (4*h))
    rows.card/13 ≤ (rows.filter (fun s => 2 ∣ s)).card := by
  classical
  let rows := (Ico l (l+length)).filter (Admits 24 n (4*h))
  let evenRows := rows.filter (fun s => 2 ∣ s)
  let oddRows := rows.filter (fun s => ¬ 2 ∣ s)
  let c := 2+2*(h*n)
  let initial := l+(c%24+24-l%24)%24
  have period : length/24 ≤ evenRows.card := by
    rw [← card_range (length/24)]
    apply card_le_card_of_injOn (fun i => initial+24*i)
    · intro i hi
      have cap := mem_range.mp hi
      have lower : l ≤ initial+24*i := by dsimp [initial]; omega
      have upper : initial+24*i<l+length := by dsimp [initial]; omega
      have residue : (initial+24*i)%24=c%24 := by dsimp [initial]; omega
      have accepted : Admits 24 n (4*h) (initial+24*i) := by
        refine ⟨2,2*h,1,n,by ring,by rw [one_mul],?_⟩
        change (initial+24*i)%24=(2*1+2*h*n)%24
        simpa only [c,mul_one,Nat.mul_assoc] using residue
      have even : 2 ∣ initial+24*i := by dsimp [c] at residue; omega
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Ico.mpr ⟨lower,upper⟩,accepted⟩,even⟩
    · intro i hi j hj eq
      change initial+24*i = initial+24*j at eq
      omega
  have oddBound : oddRows.card≤12*(length/24+1) := by
    rw [←card_range (12*(length/24+1))]
    apply card_le_card_of_injOn (fun s => (s-l)/2)
    · intro s hs
      obtain ⟨row,_⟩ := mem_filter.mp hs
      obtain ⟨lo,hi⟩ := mem_Ico.mp (mem_filter.mp row).1
      apply mem_range.mpr
      omega
    · intro x hx y hy eq
      obtain ⟨rx,ox⟩ := mem_filter.mp hx
      obtain ⟨ry,oy⟩ := mem_filter.mp hy
      obtain ⟨xl,_⟩ := mem_Ico.mp (mem_filter.mp rx).1
      obtain ⟨yl,_⟩ := mem_Ico.mp (mem_filter.mp ry).1
      change (x-l)/2 = (y-l)/2 at eq
      change ¬2 ∣ x at ox
      change ¬2 ∣ y at oy
      omega
  have partition : evenRows.card+oddRows.card=rows.card :=
    filter_card_add_filter_neg_card_eq_card (s:=rows) (fun s => 2 ∣ s)
  change rows.card / 13 ≤ evenRows.card
  omega

/-- Already the even traces on multiples of four give a uniform saving for
every product, including all endpoint roundings in the unfiltered menu. -/
theorem guaranteed (n K H : ℕ) :
    ∃ T : Finset (ℕ×ℕ), T.card=(K/4)*(H/2) ∧
      ∀ r∈T, 0<r.1 ∧ r.1≤K ∧ start n r.1≤r.2 ∧ r.2<start n r.1+H ∧ ¬Primitive r.1 r.2 := by
  let f (r : ℕ×ℕ) : ℕ×ℕ := (4*(r.1+1),2*((start n (4*(r.1+1))+1)/2+r.2))
  have inj : Function.Injective f := by
    rintro ⟨a,b⟩ ⟨c,e⟩ eq
    have h₁ := congrArg Prod.fst eq
    have h₂ := congrArg Prod.snd eq
    simp only [f] at h₁ h₂
    obtain rfl : a=c := by omega
    congr 1; omega
  refine ⟨((range (K/4)) ×ˢ (range (H/2))).image f, by simp [card_image_of_injective _ inj], ?_⟩
  intro r hr
  obtain ⟨⟨i,j⟩,h,rfl⟩ := mem_image.mp hr
  obtain ⟨hi,hj⟩ : i<K/4 ∧ j<H/2 := by simpa using h
  dsimp [f]
  refine ⟨by omega,by omega,by omega,by omega,?_⟩
  intro prim
  have wrong := prim 2 ⟨i+1,by ring⟩ ⟨_,rfl⟩
  omega

/-- A square and both gcds in two different multiplier lanes of the same input. -/
theorem example77 : start 77 1=18 ∧ start 77 4=36 ∧
    18^2=4^2+4*1*77 ∧ 36^2=8^2+4*4*77 ∧
    (11:ℕ).gcd 77=11 ∧ (22:ℕ).gcd 77=11 ∧ (7:ℕ).gcd 77=7 ∧ (14:ℕ).gcd 77=7 := by
  decide +kernel

end PrimeFactors.PrimitiveMultiplierTraces
