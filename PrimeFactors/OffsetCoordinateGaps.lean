import PrimeFactors.OffsetSquareWitness
import Mathlib.Tactic.LinearCombination

namespace PrimeFactors.OffsetCoordinateGaps

/-- Choose an integer e that is one modulo s² and zero modulo v².
The signed multiplier C = 1 - 2e uses both congruences at once. -/
theorem exists_projector {s v : ℤ} (cop : IsCoprime s v) :
    ∃ e u w : ℤ, e = v^2*u ∧ 1-e = s^2*w := by
  obtain ⟨w,u,h⟩ := (show IsCoprime (s^2) (v^2) from cop.pow_left.pow_right)
  exact ⟨v^2*u,u,w,rfl,by linear_combination -h⟩

/-- At prescribed factor residues p₀, q₀ modulo m, one congruence
determines the signed gap modulo 2m(sv)² for each proposed trace S. -/
theorem signed_gap {s v p q p₀ q₀ m e u w S : ℤ}
    (ev : e = v^2*u) (es : 1-e = s^2*w)
    (pr : m ∣ p-p₀) (qr : m ∣ q-q₀) (trace : S=p*s^2+q*v^2) :
    2*m*(s*v)^2 ∣ (p*s^2-q*v^2) -
      (p₀*s^2-q₀*v^2+(1-2*e)*(S-p₀*s^2-q₀*v^2)) := by
  obtain ⟨a,ha⟩ := pr
  obtain ⟨b,hb⟩ := qr
  refine ⟨u*a-w*b,?_⟩
  rw [trace]
  calc _ = 2*e*(p-p₀)*s^2-2*(1-e)*(q-q₀)*v^2 := by ring
       _ = _ := by rw [ha,hb,es,ev]; ring

/-- The discriminant increases with j throughout a positive chart. -/
theorem gap_band {T N k j low high z : ℤ}
    (base : 0 ≤ low+2*T*k) (left : low≤j) (right : j≤high)
    (square : z^2 = (j+2*T*k)^2-4*N*k^2) :
    (low+2*T*k)^2-4*N*k^2 ≤ z^2 ∧ z^2 ≤ (high+2*T*k)^2-4*N*k^2 := by
  have l : low+2*T*k≤j+2*T*k := by omega
  have r : j+2*T*k≤high+2*T*k := by omega
  exact ⟨by linarith only [square,pow_le_pow_left₀ base l 2],
    by linarith only [square,pow_le_pow_left₀ (base.trans l) r 2]⟩

/-- The chord between rounded-down endpoints stays below the positive
root of S²-P if the endpoint rise is at least the horizontal run. -/
theorem lower_chord {S P x d l r z : ℤ} (xd : 0≤x) (le : x≤d) (dpos : 0<d)
    (zp : 0≤z) (left : l^2 ≤ S^2-P) (right : r^2 ≤ (S+d)^2-P)
    (rise : d≤r-l) (hit : z^2=(S+x)^2-P) :
    d*l+(r-l)*x ≤ d*z := by
  have coef := pow_le_pow_left₀ dpos.le rise 2
  have e₁ := mul_nonneg (mul_nonneg dpos.le (sub_nonneg.mpr le)) (sub_nonneg.mpr left)
  have e₂ := mul_nonneg (mul_nonneg dpos.le xd) (sub_nonneg.mpr right)
  have e₃ := mul_nonneg (mul_nonneg xd (sub_nonneg.mpr le)) (sub_nonneg.mpr coef)
  have identity : (d*z)^2-(d*l+(r-l)*x)^2 =
      d*(d-x)*(S^2-P-l^2)+d*x*((S+d)^2-P-r^2)+x*(d-x)*((r-l)^2-d^2) := by
    linear_combination d^2*hit
  have square : (d*l+(r-l)*x)^2 ≤ (d*z)^2 := by linarith only [identity,e₁,e₂,e₃]
  exact le_of_not_gt fun wrong => (not_lt_of_ge square)
    (pow_lt_pow_left₀ wrong (mul_nonneg dpos.le zp) (by decide : 2≠0))

/-- An integer positive form meeting the support bound is at least the
ceiling root. This is also valid when the constant is a perfect square. -/
theorem ceil_support {a b S P z c : ℤ} (bp : 0≤b) (ab : b≤a) (sp : 0≤S)
    (zs : z≤S) (hit : z^2=S^2-P)
    (ceil : c≤0 ∨ (c-1)^2<(a^2-b^2)*P) : b*z ≤ a*S-c := by
  have pos : 0≤a*S-b*z := by
    linarith only [mul_le_mul_of_nonneg_left zs bp,mul_le_mul_of_nonneg_right ab sp]
  have identity : (a*S-b*z)^2-(a^2-b^2)*P=(b*S-a*z)^2 := by
    linear_combination (b^2-a^2)*hit
  rcases ceil with nonpos | ceil
  · omega
  by_contra! bad
  have sq := pow_le_pow_left₀ pos (show a*S-b*z≤c-1 by omega) 2
  nlinarith only [identity,sq,ceil,sq_nonneg (b*S-a*z)]

/-- Both endpoints of the projected band can be computed by integer
square roots. The common factor g permits reducing the chord slope. -/
theorem chord_strip {S P x d l r z a b g c : ℤ} (xd : 0≤x) (le : x≤d)
    (dpos : 0<d) (zp : 0≤z) (sp : 0≤S) (zs : z≤S+x)
    (left : l^2≤S^2-P) (right : r^2≤(S+d)^2-P) (hit : z^2=(S+x)^2-P)
    (gp : 0<g) (run : d=g*b) (rise : r-l=g*a) (ab : b≤a)
    (ceil : c≤0 ∨ (c-1)^2<(a^2-b^2)*P) :
    b*l ≤ b*z-a*x ∧ b*z-a*x ≤ a*S-c := by
  have bp : 0<b := (mul_pos_iff_of_pos_left gp).mp (run ▸ dpos)
  have wide : d≤r-l := by rw [run,rise]; exact mul_le_mul_of_nonneg_left ab gp.le
  have lo := lower_chord xd le dpos zp left right wide hit
  have hi := ceil_support bp.le ab (add_nonneg sp xd) zs hit ceil
  rw [rise,run] at lo
  have product : g*(b*l)≤g*(b*z-a*x) := by linarith only [lo]
  exact ⟨le_of_not_gt (fun wrong => (not_lt_of_ge product) (mul_lt_mul_of_pos_left wrong gp)),
    by linarith only [hi]⟩

/-- A winning position gives an oriented signed gap in the computed
progression. The sign is determined by which coordinate belongs to p. -/
theorem parity_chart_of_hit {p q T j k f : ℕ} (pp : p.Prime) (qp : q.Prime)
    (ne : p≠q) (po : Odd p) (qo : Odd q) (kp : 0<k) (jk : j.Coprime k)
    (hit : CompleteOffsetSearch.probe (p*q) T j k=some f) :
    ∃ s v : ℕ, 0<s ∧ 0<v ∧ s.Coprime v ∧ k=s*v ∧
      ∃ z e u w : ℤ, e=v^2*u ∧ 1-e=s^2*w ∧
        z^2=((j:ℤ)+2*T*k)^2-4*((p:ℤ)*q)*k^2 ∧
        (4:ℤ)*k^2 ∣ z-((s:ℤ)^2-v^2+(1-2*e)*(j+2*(T:ℤ)*k-s^2-v^2)) ∧
        (2:ℤ) ∣ (j:ℤ)+2*T*k-s^2-v^2 := by
  obtain ⟨s,v,sp,vp,prim,ks,sum⟩ := OffsetSquareWitness.exists_vector_of_hit pp qp ne kp jk hit
  have cop : IsCoprime (s:ℤ) (v:ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr (by simpa using prim)
  obtain ⟨e,u,w,ev,es⟩ := exists_projector cop
  have tr : (j:ℤ)+2*T*k=(p:ℤ)*s^2+(q:ℤ)*v^2 := by exact_mod_cast sum
  obtain ⟨a,ha⟩ := po
  obtain ⟨b,hb⟩ := qo
  have hp : (p:ℤ)=2*a+1 := by exact_mod_cast ha
  have hq : (q:ℤ)=2*b+1 := by exact_mod_cast hb
  have pr : (2:ℤ) ∣ (p:ℤ)-1 := ⟨a,by omega⟩
  have qr : (2:ℤ) ∣ (q:ℤ)-1 := ⟨b,by omega⟩
  refine ⟨s,v,sp,vp,prim,ks,(p:ℤ)*s^2-q*v^2,e,u,w,ev,es,?_,?_,?_⟩
  · rw [tr,ks]; push_cast; ring
  · have h := signed_gap ev es pr qr tr
    rw [ks] at h ⊢
    push_cast
    simpa only [one_mul,show (2:ℤ)*2=4 by decide] using h
  · refine ⟨(a:ℤ)*s^2+b*v^2,?_⟩
    rw [tr,hp,hq]; ring

/-- The smaller prime carries coordinate four. Here the signed gap is
negative, so taking only the positive square root as residue would miss it. -/
theorem negative_gap_example :
    (257:ℤ)*4^2-457*3^2 = -1 ∧
    ((4:ℤ)^2-3^2+(1-2*81)*(8225-4^2-3^2)) % (4*12^2) = 575 ∧
    CompleteOffsetSearch.probe 117449 342 17 12 = some 257 := by decide +kernel

end PrimeFactors.OffsetCoordinateGaps
