import PrimeFactors.TwelveResidueCollision

namespace PrimeFactors.TwelveImageSize
open Finset TwelveResidueCollision

set_option maxHeartbeats 800000

/-- A product-only normalized key. Requiring a unit mask excludes a pole over
either prime without naming the primes. -/
def Attainable {R : Type*} [CommRing R] (z : R) : Prop :=
  ∃ x : R, IsUnit (mask x) ∧ num x = z * den x

noncomputable def keys (R : Type*) [CommRing R] [Fintype R] : Finset R := by
  classical exact univ.filter Attainable

private theorem mem_keys {R : Type*} [CommRing R] [Fintype R] {z : R} :
    z ∈ keys R ↔ Attainable z := by classical simp [keys]

private theorem map_attainable {R S : Type*} [CommRing R] [CommRing S]
    (e : R →+* S) {z : R} (h : Attainable z) : Attainable (e z) := by
  obtain ⟨x, unit, eq⟩ := h
  refine ⟨e x, ?_, ?_⟩
  · simpa [mask,map_ofNat] using unit.map e
  · simpa [num,sextic,den,map_ofNat] using congrArg e eq

private theorem attainable_pair {R S : Type*} [CommRing R] [CommRing S] (u : R) (v : S) :
    Attainable (u,v) ↔ Attainable u ∧ Attainable v := by
  constructor
  · intro h
    exact ⟨map_attainable (RingHom.fst R S) h, map_attainable (RingHom.snd R S) h⟩
  · rintro ⟨⟨x,hx,px⟩,⟨y,hy,py⟩⟩
    refine ⟨(x,y), Prod.isUnit_iff.mpr ⟨hx,hy⟩, Prod.ext px py⟩

/-- Over two coprime moduli, the full product-only key set has exactly the
product of the local image sizes. The witnesses in the two fields can be
chosen independently and lifted by CRT. -/
theorem keys_crt {p q : ℕ} [NeZero p] [NeZero q] (h : p.Coprime q) :
    (keys (ZMod (p*q))).card = (keys (ZMod p)).card * (keys (ZMod q)).card := by
  classical
  let e := ZMod.chineseRemainder h
  have eq : (keys (ZMod (p*q))).image e = keys (ZMod p) ×ˢ keys (ZMod q) := by
    ext v
    rw [mem_image, mem_product, mem_keys, mem_keys, ← attainable_pair]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact map_attainable e.toRingHom (mem_keys.mp hz)
    · intro hv
      exact ⟨e.symm v,mem_keys.mpr (map_attainable e.symm.toRingHom hv),e.apply_symm_apply v⟩
  rw [←card_product, ←eq, card_image_of_injective _ e.injective]

private theorem char108 {p : ℕ} [Fact p.Prime] (big : 864<p) : (108:ZMod p) ≠ 0 := by
  exact_mod_cast (show ((108:ℕ):ZMod p) ≠ 0 by
    rw [Ne,ZMod.natCast_zmod_eq_zero_iff_dvd]
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega))

def value {K : Type*} [Field K] (x : K) := num x / den x

theorem prime_keys {p : ℕ} [Fact p.Prime] (big : 864<p) :
    keys (ZMod p) = (regulars p).image value := by
  ext z
  rw [mem_keys,mem_image]
  constructor
  · rintro ⟨x,u,h⟩
    have reg := isUnit_iff_ne_zero.mp u
    exact ⟨x,mem_filter.mpr ⟨mem_univ _,reg⟩,
      (div_eq_iff ((regular_iff (char108 big) x).mp reg).1).mpr h⟩
  · rintro ⟨x,hx,rfl⟩
    have reg := (mem_filter.mp hx).2
    exact ⟨x,isUnit_iff_ne_zero.mpr reg,
      ((div_eq_iff ((regular_iff (char108 big) x).mp reg).1).mp rfl)⟩

theorem regulars_eq_twelve_keys {p : ℕ} [Fact p.Prime] (big : 864<p) :
    (regulars p).card = 12 * (keys (ZMod p)).card := by
  classical
  rw [prime_keys big]
  calc
    _ = ∑ z ∈ (regulars p).image value, ((regulars p).filter (fun y => value y=z)).card :=
      card_eq_sum_card_image value (regulars p)
    _ = ∑ _z ∈ (regulars p).image value, 12 := by
      apply sum_congr rfl
      intro z hz
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
      rw [←regular_fiber big hx]
      congr 1
      ext y
      simp only [mem_filter,and_congr_right_iff]
      intro hy
      have dx := ((regular_iff (char108 big) x).mp (mem_filter.mp hx).2).1
      have dy := ((regular_iff (char108 big) y).mp (mem_filter.mp hy).2).1
      exact (div_eq_div_iff dy dx).trans eq_comm
    _ = _ := by simp [Nat.mul_comm]

/-- The five distinct residues 0, ±1 and ±3 always vanish on the mask. -/
theorem five_exceptions {p : ℕ} [Fact p.Prime] (big : 864<p) :
    5 ≤ (univ.filter fun x : ZMod p => mask x=0).card := by
  classical
  let s : Finset ℕ := {0,2,3,4,6}
  have card : s.card=5 := by decide
  rw [←card]
  apply card_le_card_of_injOn (fun a : ℕ => (a:ZMod p)-3)
  · intro a ha
    simp only [s,mem_insert,mem_singleton] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl <;> simp [mask] <;> ring_nf <;> simp
  · intro a ha b hb eq
    have bounded (v : ℕ) (hv : v∈s) : v<p := by
      simp only [s,mem_insert,mem_singleton] at hv
      omega
    have v := congrArg ZMod.val (sub_left_inj.mp eq)
    simpa [ZMod.val_natCast_of_lt (bounded a ha),ZMod.val_natCast_of_lt (bounded b hb)] using v

/-- The exact prime-field image size follows from five through thirteen
exceptions and divisibility of the regular count by twelve. -/
theorem prime_image_size {p : ℕ} [Fact p.Prime] (big : 864<p) :
    (keys (ZMod p)).card = (p-5)/12 := by
  have total := filter_card_add_filter_neg_card_eq_card (s:=univ) (fun x : ZMod p => mask x=0)
  change _ + (regulars p).card = _ at total
  simp only [card_univ,ZMod.card] at total
  have upper := exceptions (p:=p)
  have lower := five_exceptions big
  have reg := regulars_eq_twelve_keys big
  omega

/-- For distinct prime factors the product-only image cardinal is the product
of the two rounded prime quotients. -/
theorem product_image_size {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : 864<p) (hq : 864<q) (different : p≠q) :
    (keys (ZMod (p*q))).card = ((p-5)/12)*((q-5)/12) := by
  rw [keys_crt ((Nat.coprime_primes Fact.out Fact.out).mpr different),
    prime_image_size hp, prime_image_size hq]

def offset (p : ℕ) : ℕ := 5 + (p-5)%12

private theorem expand_prime {p : ℕ} (big : 864<p) :
    p = 12*((p-5)/12)+offset p := by unfold offset; omega

private theorem offset_cases {p : ℕ} [Fact p.Prime] (big : 864<p) :
    offset p=5 ∨ offset p=7 ∨ offset p=11 ∨ offset p=13 := by
  have cop : p.Coprime 12 := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  have modcop : (p%12).Coprime 12 := by
    change (p%12).gcd 12=1
    rw [←Nat.gcd_rec, Nat.gcd_comm]
    exact cop
  have residues : ∀ r : Fin 12, (r:ℕ).Coprime 12 →
      (r:ℕ)=1 ∨ (r:ℕ)=5 ∨ (r:ℕ)=7 ∨ (r:ℕ)=11 := by decide +kernel
  have fact := residues ⟨p%12,Nat.mod_lt p (by decide)⟩ modcop
  change p%12=1 ∨ p%12=5 ∨ p%12=7 ∨ p%12=11 at fact
  unfold offset
  omega

/-- All ordered offset pairs allowed by the product residue. -/
def cases (r : ℕ) : List (ℕ × ℕ) :=
  if r=1 then [(5,5),(7,7),(11,11),(13,13)] else
  if r=5 then [(5,13),(7,11),(11,7),(13,5)] else
  if r=7 then [(5,11),(7,13),(11,5),(13,7)] else
  if r=11 then [(5,7),(7,5),(11,13),(13,11)] else []

theorem cases_bound (r : ℕ) : (cases r).length≤4 := by
  unfold cases
  split_ifs <;> decide

private theorem admissible {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : 864<p) (hq : 864<q) : (offset p,offset q)∈cases ((p*q)%12) := by
  have rp : p%12=offset p%12 := by have h:=expand_prime hp; omega
  have rq : q%12=offset q%12 := by have h:=expand_prime hq; omega
  rw [Nat.mul_mod,rp,rq,←Nat.mul_mod]
  rcases offset_cases hp with h|h|h|h <;> rcases offset_cases hq with k|k|k|k <;>
    rw [h,k] <;> decide

/-- The public weighted sum when the count and offsets are supplied. -/
def trace (n count e f : ℕ) : ℕ := n+e*f-144*count

theorem exact_trace {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : 864<p) (hq : 864<q) (different : p≠q) :
    trace (p*q) (keys (ZMod (p*q))).card (offset p) (offset q) =
    p*offset q + q*offset p := by
  rw [trace,product_image_size hp hq different]
  apply Nat.sub_eq_of_eq_add
  have a := expand_prime hp
  have b := expand_prime hq
  nlinarith only [congrArg₂ (·*·) a b, congrArg (·*offset q) a, congrArg (·*offset p) b]

/-- The larger root of the weighted quadratic, followed by one gcd. -/
def candidate (n count : ℕ) (offsets : ℕ × ℕ) : ℕ :=
  let (e,f) := offsets
  let t := trace n count e f
  n.gcd ((t + (t^2-4*e*f*n).sqrt)/2)

private theorem bigger_root (a b : ℕ) :
    ((a+b)+((a+b)^2-4*a*b).sqrt)/2=max a b := by
  have ordered (x y : ℕ) (le : x≤y) :
      ((x+y)+((x+y)^2-4*x*y).sqrt)/2=y := by
    obtain ⟨z,rfl⟩ := Nat.exists_eq_add_of_le le
    have disc : (x+(x+z))^2-4*x*(x+z)=z^2 := by
      apply Nat.sub_eq_of_eq_add
      ring
    rw [disc,Nat.sqrt_eq']
    omega
  rcases le_total a b with h|h
  · rw [max_eq_right h,ordered a b h]
  · rw [max_eq_left h]
    convert ordered b a h using 1
    ring_nf

/-- One of the at most four product-only quadratic gcds recovers a prime
factor once the exact image count is available. -/
theorem recovers_prime {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : 864<p) (hq : 864<q) (different : p≠q) :
    ∃ ef ∈ cases ((p*q)%12),
      candidate (p*q) (keys (ZMod (p*q))).card ef = p ∨
      candidate (p*q) (keys (ZMod (p*q))).card ef = q := by
  refine ⟨(offset p,offset q),admissible hp hq,?_⟩
  simp only [candidate,exact_trace hp hq different]
  rw [show 4*offset p*offset q*(p*q) = 4*(p*offset q)*(q*offset p) by ring,
    bigger_root]
  have cop (r : ℕ) [Fact r.Prime] (big : 864<r) : r.Coprime (offset r) :=
    (Fact.out : r.Prime).coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (by unfold offset; omega) (by unfold offset; omega))
  rcases le_total (p*offset q) (q*offset p) with h|h
  · right
    rw [max_eq_right h,Nat.mul_comm p q,Nat.gcd_mul_left,(cop p hp).gcd_eq_one,Nat.mul_one]
  · left
    rw [max_eq_left h,Nat.gcd_mul_left,(cop q hq).gcd_eq_one,Nat.mul_one]

/-- Distinct products of offset pairs allowed by the public product residue.
Swapping the offsets leaves the quadratic unchanged. -/
def weights (r : ℕ) : List ℕ :=
  if r=1 then [25,49,121,169] else
  if r=5 then [65,77] else
  if r=7 then [55,91] else
  if r=11 then [35,143] else []

theorem weights_bound (r : ℕ) : (weights r).length ≤ if r=1 then 4 else 2 := by
  unfold weights
  split_ifs <;> decide

def candidateFromWeight (n count w : ℕ) : ℕ := candidate n count (w,1)

theorem recover_from_count {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : 864<p) (hq : 864<q) (different : p≠q) :
    ∃ w ∈ weights ((p*q)%12),
      candidateFromWeight (p*q) (keys (ZMod (p*q))).card w = p ∨
      candidateFromWeight (p*q) (keys (ZMod (p*q))).card w = q := by
  obtain ⟨⟨e,f⟩,mem,rec⟩ := recovers_prime hp hq different
  have table (r : ℕ) : ∀ i∈cases r, i.1*i.2∈weights r := by
    unfold cases weights
    split_ifs <;> decide
  refine ⟨e*f,table _ (e,f) mem,?_⟩
  simpa [candidateFromWeight,candidate,trace,Nat.mul_assoc] using rec

/-- Certificate for the bounded count and the public recovering weight. -/
theorem example_image_781447 : (keys (ZMod 781447)).card=5329 := by
  haveI pp : Fact (Nat.Prime 881) := ⟨by norm_num⟩
  haveI pq : Fact (Nat.Prime 887) := ⟨by norm_num⟩
  exact product_image_size (p:=881) (q:=887) (by decide) (by decide) (by decide)

/-- A small arithmetic receipt validates a candidate without reducing a
square root by kernel computation. -/
theorem checked_weight {n k w t d g : ℕ} (ht : n+w-144*k=t)
    (hd : t^2-4*w*n=d^2) (hg : n.gcd ((t+d)/2)=g) :
    candidateFromWeight n k w = g := by
  simpa only [candidateFromWeight,candidate,trace,Nat.mul_one,ht,hd,Nat.sqrt_eq'] using hg

theorem example_factor_781447 : candidateFromWeight 781447 5329 55=881 ∧
    Nat.Prime 881 ∧ Nat.Prime 887 ∧ 881*887=781447 := by
  refine ⟨?_,by norm_num,by norm_num,by decide⟩
  exact checked_weight (t:=14126) (d:=5256) (by decide) (by decide) (by decide)

end PrimeFactors.TwelveImageSize
