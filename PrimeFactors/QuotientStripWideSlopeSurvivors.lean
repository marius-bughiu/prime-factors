import PrimeFactors.QuotientStripWideSlopeGeometry
import PrimeFactors.QuotientStripTailCover

namespace PrimeFactors.QuotientStripWideSlopeGeometry
namespace Band

/-- The stationary center and band length exist for each permissible ratio. -/
theorem of_scale {s r u v : ℝ} (rp : 1≤r) (vp : 7≤v) (low : 5*v≤4*u)
    (high : 3*u≤4*v) (cap : 2^11*v≤r) (lo : r^3≤2*s) (hi : s≤2*r^3) :
    Band s r u v (Real.sqrt (v*s^2/u)) (s/(4*v*r)) := by
  have R : 0<r := by linarith
  have V : 0<v := by linarith
  have U : 0<u := by linarith
  have S : 0<s := by nlinarith only [lo,pow_pos R 3]
  refine ⟨rp,vp,low,high,cap,lo,hi,Real.sqrt_pos.mpr (by positivity),by positivity,?_,?_⟩
  · rw [Real.sq_sqrt (by positivity)]
    field_simp
  · field_simp

/-- Any reduced direction meeting the ordinary chord certificate on this strip
has exactly the designated numerator and denominator. -/
theorem selected {s r t L a b : ℝ} {u v p q : ℕ}
    (G : Band s r (u:ℝ) (v:ℝ) t L)
    (low : t-L≤a) (ab : a≤b) (high : b≤t)
    (pr : u.Coprime v) (pq : p.Coprime q) (qp : 0<q) (cap : (q:ℝ)≤r)
    (certificate : |(p:ℝ)-q*(s^2/(a*b))|≤1/r) : p=u ∧ q=v := by
  obtain ⟨rp,vp,_,_,_⟩ := G.basic
  have Q : 0<(q:ℝ) := by exact_mod_cast qp
  have V : 0<v := by exact_mod_cast vp
  let α := s^2/(a*b)
  have sl := G.chord_slope low ab high
  have err : 0≤v*α-u ∧ v*α-u<7/(8*r) := by simpa [α,mul_div_assoc] using sl
  have fit := abs_le.mp certificate
  change -(1/r)≤p-q*α ∧ p-q*α≤1/r at fit
  have vl : (v:ℝ)*(1/r) ≤ 1/16 := by
    rw [← mul_div_assoc, div_le_iff₀ rp]
    nlinarith only [G.cap,vp]
  have ql : (q:ℝ)*(7/(8*r)) ≤ 7/8 := by
    rw [← mul_div_assoc,div_le_iff₀ (by positivity)]
    linarith
  have x := mul_le_mul_of_nonneg_left fit.1 vp.le
  have y := mul_le_mul_of_nonneg_left fit.2 vp.le
  have z := mul_le_mul_of_nonneg_left err.1 Q.le
  have w := mul_lt_mul_of_pos_left err.2 Q
  have same : p*v=q*u := by
    have h : (p:ℝ)*v < q*u+1 := by nlinarith only [y,w,ql,vl]
    have k : (q:ℝ)*u < p*v+1 := by nlinarith only [x,z,vl]
    have h' : p*v<q*u+1 := by exact_mod_cast h
    have k' : q*u<p*v+1 := by exact_mod_cast k
    omega
  have repr : (p:ℚ)/q=u/v := (div_eq_div_iff (by positivity) (by positivity)).mpr (by
    exact_mod_cast (same.trans (Nat.mul_comm q u)))
  have EQ := Rat.div_int_inj (a:=(p:ℤ)) (b:=(q:ℤ)) (c:=(u:ℤ)) (d:=(v:ℤ))
    (by exact_mod_cast qp) (by exact_mod_cast V) (by simpa using pq) (by simpa using pr)
    (by simpa using repr)
  exact_mod_cast EQ

/-- Two labels in any prescribed residue modulo 24 occur on the actual
weighted endpoint intervals, with strictly positive discriminants. The
integer progression of full strips is supplied separately. -/
theorem band_survivors {s r u v t L : ℝ} (G : Band s r u v t L)
    (A B : ℕ→ℝ) (k : ℕ) (c : ℤ)
    (blocks : ∀i≤k, t-L≤A i ∧ B i-A i=2*r-1 ∧ B i≤t)
    (next : ∀i<k, A (i+1)=B i+1)
    (first : A 0≤t-L+2*r) (last : t-4*r≤B k) :
    ∃ z : ℤ, z ≡ c [ZMOD 24] ∧
      ∀ w ∈ ({z,z+24} : Finset ℤ), 0<(w:ℝ)^2-4*u*v*s^2 ∧
        ∃i≤k, F s u v (B i)-pad s v (A i) (B i)≤w ∧ (w:ℝ)≤F s u v (A i) := by
  obtain ⟨rp,vp,_,up,sp⟩ := G.basic
  let j : ℤ := ⌈(2*u*t+1-(c:ℝ))/24⌉
  let z : ℤ := c+24*j
  have zlow := Int.le_ceil ((2*u*t+1-(c:ℝ))/24)
  have zhi := Int.ceil_lt_add_one ((2*u*t+1-(c:ℝ))/24)
  change _≤(j:ℝ) at zlow
  change (j:ℝ)<_ at zhi
  have room : 2*u*t+1 ≤ (z:ℝ) ∧ (z:ℝ)+24 ≤ 2*u*t+64 := by
    dsimp only [z]; push_cast; constructor <;> linarith
  refine ⟨z,?_,?_⟩
  · rw [Int.modEq_iff_dvd]
    exact ⟨-j,by dsimp only [z]; ring⟩
  intro w hw
  have mem : w=z ∨ w=z+24 := by simpa using hw
  have bounds : 2*u*t+1 ≤ (w:ℝ) ∧ (w:ℝ) ≤ 2*u*t+64 := by
    rcases mem with rfl|rfl <;> push_cast <;> constructor <;> linarith [room.1,room.2]
  have nonneg : 0 ≤ 2*u*t := mul_nonneg (by positivity) G.tp.le
  have sq := mul_self_lt_mul_self nonneg (by linarith only [bounds.1] : 2*u*t < (w:ℝ))
  have id := congrArg (fun m : ℝ => 4*u*m) G.atCenter
  change 4*u*(u*t^2)=4*u*(v*s^2) at id
  refine ⟨by nlinarith only [id,sq],?_⟩
  have low : F s u v (B k)-pad s v (A k) (B k) ≤ w := by
    have ht := G.last_height last (blocks k le_rfl).2.2
    have ba := blocks k le_rfl
    have ab : A k≤B k := by linarith [ba.2.1,G.rp]
    have ap := (G.slope_at ba.1 (ab.trans ba.2.2)).1
    have bp := ap.trans_le ab
    have pd : 0≤pad s v (A k) (B k) := by unfold pad; positivity
    linarith only [ht,pd,bounds.1]
  refine QuotientStripTailCover.chain_cover (lo:=fun i => F s u v (B i)-pad s v (A i) (B i))
    (hi:=fun i => F s u v (A i)) k (w:ℝ) (bounds.2.trans
      (G.first_height (blocks 0 (Nat.zero_le _)).1 first)) low ?_
  intro i ik
  change F s u v (B i)-pad s v (A i) (B i) ≤ F s u v (A (i+1))
  rw [next i ik]
  obtain ⟨a,b,c'⟩ := blocks i ik.le
  exact G.adjacent a b c'

end Band
end PrimeFactors.QuotientStripWideSlopeGeometry
