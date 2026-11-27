import PrimeFactors.RectangularFullWidth
import PrimeFactors.WeightWindowOverlap

/-! Every positive row in the balanced rectangle is an integer square
multiple of a row with coprime coordinates. -/
namespace PrimeFactors.RectangularRowNormalization
open Finset RectangularFullWidth
set_option exponentiation.threshold 4096

def Hit (N B H k : ℕ) (primitive : Bool) : Prop :=
  0<k ∧ ∃ x y : ℕ, 0<y ∧ y≤B ∧ x≤H ∧ y^2=x^2+k*N ∧ (primitive=true → x.Coprime y)

noncomputable def hits (N B H K : ℕ) (primitive : Bool) : Finset ℕ := by
  classical exact (Icc 1 K).filter (fun k => Hit N B H k primitive)

theorem normalize {p q B H k : ℕ} (pp : p.Prime) (qp : q.Prime) (lt : p<q)
    (short : H<p) (box : B<p*q) (h : Hit (p*q) B H k false) :
    ∃ k₀ g : ℕ, Hit (p*q) B H k₀ true ∧ 0<g ∧ k=g^2*k₀ := by
  obtain ⟨kp,x,y,yp,yb,xh,row,_⟩ := h
  have xp : 0<x := by
    by_contra! zero
    have dy : p*q∣y^2 := ⟨k,by rw [row,show x=0 by omega]; simp [mul_comm]⟩
    have py := pp.dvd_of_dvd_pow ((dvd_mul_right p q).trans dy)
    have qy := qp.dvd_of_dvd_pow ((dvd_mul_left q p).trans dy)
    have impossible := ((Nat.coprime_primes pp qp).mpr lt.ne).mul_dvd_of_dvd_of_dvd py qy
    exact (Nat.not_dvd_of_pos_of_lt yp (yb.trans_lt box)) impossible
  let g := x.gcd y
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ xp
  have gx : g∣x := Nat.gcd_dvd_left ..
  have gy : g∣y := Nat.gcd_dvd_right ..
  have small := ((Nat.le_of_dvd xp gx).trans xh).trans_lt short
  have unit : g.Coprime (p*q) := (pp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt gp small)).symm.mul_right
    (qp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt gp (small.trans lt))).symm
  obtain ⟨u,eu⟩ := gx
  obtain ⟨v,ev⟩ := gy
  have div : g^2∣k*(p*q) := by
    have dv : g^2∣y^2 := pow_dvd_pow_of_dvd (Nat.gcd_dvd_right x y) 2
    have du : g^2∣x^2 := pow_dvd_pow_of_dvd (Nat.gcd_dvd_left x y) 2
    rw [row] at dv
    exact (Nat.dvd_add_iff_right du).mpr dv
  obtain ⟨k₀,ek⟩ := (unit.pow_left 2).dvd_of_dvd_mul_right div
  have e : g^2*v^2=g^2*(u^2+k₀*(p*q)) := by
    rw [eu,ev,ek] at row
    convert row using 1 <;> ring
  have prim : u.Coprime v := by
    have gu : x/g=u := by rw [eu,Nat.mul_div_cancel_left _ gp]
    have gv : y/g=v := by rw [ev,Nat.mul_div_cancel_left _ gp]
    rw [←gu,←gv]
    exact Nat.coprime_div_gcd_div_gcd gp
  have vp : 0<v := Nat.pos_of_mul_pos_left (ev ▸ yp)
  have pos : 0<k₀ := Nat.pos_of_mul_pos_left (ek ▸ kp)
  have uv : u≤x := Nat.le_of_dvd xp ⟨g,by simpa [mul_comm] using eu⟩
  have vv : v≤y := Nat.le_of_dvd yp ⟨g,by simpa [mul_comm] using ev⟩
  exact ⟨k₀,g,⟨pos,u,v,vp,vv.trans yb,uv.trans xh,
    Nat.eq_of_mul_eq_mul_left (pow_pos gp 2) e,fun _ => prim⟩,gp,ek⟩

/-- All successful rows, including those a nonprimitive point can hit. -/
theorem count {p q B H K : ℕ} (pp : p.Prime) (qp : q.Prime) (lt : p<q)
    (short : H<p) (box : B<p*q) :
    (hits (p*q) B H K false).card ≤ (hits (p*q) B H K true).card*K.sqrt := by
  classical
  let prim := hits (p*q) B H K true
  have incl : hits (p*q) B H K false ⊆ (prim ×ˢ Icc 1 K.sqrt).image (fun z => z.2^2*z.1) := by
    intro k hk
    obtain ⟨rng,good⟩ := mem_filter.mp hk
    obtain ⟨k₀,g,h,gp,eq⟩ := normalize pp qp lt short box good
    have cap := (mem_Icc.mp rng).2
    have gc : g^2≤K := (Nat.le_mul_of_pos_right (g^2) h.1).trans (eq ▸ cap)
    have kc : k₀≤K := (Nat.le_mul_of_pos_left k₀ (pow_pos gp 2)).trans (eq ▸ cap)
    apply mem_image.mpr
    refine ⟨(k₀,g),mem_product.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨h.1,kc⟩,h⟩,
      mem_Icc.mpr ⟨gp,Nat.le_sqrt'.mpr gc⟩⟩,eq.symm⟩
  exact (card_le_card incl).trans (card_image_le.trans (by simp [prim]))

theorem full_sqrt {N : ℕ} (lo : 2^2047≤N) (hi : N<2^2048) : (K N).sqrt ≤ 2^343 := by
  obtain ⟨_,_,_,b,_,_,_⟩ := dimensions lo hi
  have d : K N*N≤(B N)^2 := Nat.div_mul_le_self ..
  have sq := Nat.pow_le_pow_left b 2
  have scale := Nat.mul_le_mul_left (K N) lo
  have cap : K N ≤ 2^686 := by
    apply Nat.le_of_mul_le_mul_left (c:=2^2047) _ (by decide)
    calc
      2^2047*K N ≤ K N*N := by simpa only [mul_comm (2^2047)] using scale
      _ ≤ (B N)^2 := d
      _ ≤ (2^1366)^2 := sq
      _ ≤ 2^2047*2^686 := by decide +kernel
  exact (Nat.sqrt_le_sqrt cap).trans_eq (show (2^686:ℕ).sqrt=2^343 by
    rw [show (2:ℕ)^686=(2^343)^2 by decide +kernel,Nat.sqrt_eq'])

theorem primitive_cap {p q B H K : ℕ} (pp : p.Prime) (qp : q.Prime) (lt : p<q)
    (odd : 2<p) (upper : B+H<p*q) (small : H*B<p*q) :
    (hits (p*q) B H K true).card≤2 := by
  classical
  apply WeightWindowOverlap.primitive_count pp qp lt.ne (pp.odd_of_ne_two (by omega))
    (qp.odd_of_ne_two (by omega)) upper small
  intro k hk
  obtain ⟨_,kp,x,y,yp,yb,xh,row,prim⟩ := mem_filter.mp hk
  exact ⟨⟨x,y,kp,yp,xh,yb,prim rfl,row⟩⟩

/-- If two certified primitive rows each exceed one quarter of the entire
multiplier range, these are the only possible successful indices. -/
theorem only_two {p q B H K i j : ℕ} (pp : p.Prime) (qp : q.Prime) (lt : p<q)
    (odd : 2<p) (upper : B+H<p*q) (small : H*B<p*q) (short : H<p)
    (wi : Hit (p*q) B H i true) (wj : Hit (p*q) B H j true) (ne : i≠j)
    (ic : i≤K) (jc : j≤K) (il : K<4*i) (jl : K<4*j) :
    ∀ k≤K, Hit (p*q) B H k false → k=i ∨ k=j := by
  classical
  let s := hits (p*q) B H K true
  have member {r : ℕ} (h : Hit (p*q) B H r true) (cap : r≤K) : r∈s :=
    mem_filter.mpr ⟨mem_Icc.mpr ⟨h.1,cap⟩,h⟩
  have incl : {i,j}⊆s := insert_subset (member wi ic) (singleton_subset_iff.mpr (member wj jc))
  have sz : s.card≤({i,j}:Finset ℕ).card := by
    simpa [s,ne] using (primitive_cap (K:=K) pp qp lt odd upper small)
  have eq := eq_of_subset_of_card_le incl sz
  intro k kc hit
  obtain ⟨v,g,good,gp,factor⟩ := normalize pp qp lt short (by omega) hit
  have vc := (Nat.le_mul_of_pos_left v (pow_pos gp 2)).trans (factor ▸ kc)
  have m := member good vc
  rw [←eq,mem_insert,mem_singleton] at m
  have g1 : g=1 := by
    by_contra! gn
    have h := Nat.pow_le_pow_left (show 2≤g by omega) 2
    have many := Nat.mul_le_mul_right v h
    rcases m with rfl|rfl <;> omega
  rw [g1,one_pow,one_mul] at factor
  rwa [factor]

end PrimeFactors.RectangularRowNormalization
