import PrimeFactors.MixedPrefixWords

/-! A carry predictor sees the leading product word and the trailing 1023 bits.
The high correction and the final choice from its menu can use the full product. -/

namespace PrimeFactors.MixedPrefixPopulation

open Finset LowBitsCarryMenu

set_option exponentiation.threshold 65536

/-- The raw word includes the mandatory leading 1. -/
def headWord (h n : ℕ) : ℕ := n/2^(2047-h)

/-- Exactly h bits following the leading 1 are free on a 2048-bit product. -/
theorem prefix_bounds {h n : ℕ} (hc : h≤2047) (lo : 2^2047≤n) (hi : n<2^2048) :
    2^h≤headWord h n ∧ headWord h n<2^h+2^h := by
  have powId : (2:ℕ)^h * 2^(2047-h)=2^2047 := by rw [←pow_add,Nat.add_sub_of_le hc]
  have double : (2:ℕ)^2048=2^2047+2^2047 := by decide +kernel
  unfold headWord
  exact ⟨(Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (powId ▸ lo),
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (by rwa [add_mul,powId,←double])⟩

/-- Each proposed lower carry can succeed at any upper correction, including an
incidental proper factor from the probe. -/
def Accepted (h : ℕ) (menu : ℕ → ℕ → Finset ℤ) (z : ℕ×ℕ) : Prop :=
  let n := z.1*z.2
  z.1.Prime ∧ z.2.Prime ∧ z.1≠z.2 ∧ 2^1023≤z.1 ∧ z.1<2^1024 ∧ 2^1023≤z.2 ∧ z.2<2^1024 ∧
  2^2047≤n ∧ n<2^2048 ∧
  ∃ k∈menu (headWord h n) (n%2^1023), ∃ a f, PredictedTraceCarries.probe n (2^704) a k=some f

private theorem cap_card {w : ℤ} (nz : w≠0) (small : w.natAbs<2^1406) :
    w.divisorsAntidiag.card ≤ 2*(5*2^176) := by
  have τ : w.natAbs.divisors.card ≤ 5*2^176 := by
    apply (Nat.pow_le_pow_iff_left (by decide : 336≠0)).mp
    exact (UniformDivisorCount.below_power_two (Int.natAbs_pos.mpr nz) small).le.trans (by decide +kernel)
  have ac : w.natAbs.divisorsAntidiagonal.card=w.natAbs.divisors.card := by rw [←Nat.map_div_right_divisors,card_map]
  rcases le_total 0 w with hp|hn
  · conv_lhs => rw [show w=(w.natAbs:ℤ) by rw [Int.natCast_natAbs,abs_of_nonneg hp]]
    rw [Int.divisorsAntidiag_natCast,card_disjUnion,card_map,card_map,ac,two_mul]; omega
  · conv_lhs => rw [show w= -(w.natAbs:ℤ) by rw [Int.natCast_natAbs,abs_of_nonpos hn,neg_neg]]
    rw [Int.divisorsAntidiag_neg_natCast,card_disjUnion,card_map,card_map,ac,two_mul]; omega

/-- A finite union bound for a menu of overlapping possibilities. -/
private theorem cover {α β : Type*} [DecidableEq α] {S : Finset α} (keys : Finset β)
    (R : β → α → Prop) (bound : ℕ) (covered : ∀ x∈S, ∃ i∈keys, R i x)
    (local_bound : ∀ i∈keys, ∀ V : Finset α, (∀ x∈V, x∈S ∧ R i x) → V.card≤bound) :
    S.card≤keys.card*bound := by
  classical
  let row (i : β) := S.filter (R i)
  have sub : S⊆keys.biUnion row := by
    intro x hx; obtain ⟨i,mem,h⟩ := covered x hx; exact mem_biUnion.mpr ⟨i,mem,mem_filter.mpr ⟨hx,h⟩⟩
  exact (card_le_card sub).trans (card_biUnion_le_card_mul keys row bound fun i hi =>
    local_bound i hi _ fun _ hx => mem_filter.mp hx)

private def low (n : ℕ) := n%2^1023

private def Word (h H c : ℕ) (z : ℕ×ℕ) : Prop :=
  headWord h (z.1*z.2)=H ∧ low (z.1*z.2)=c

/-- The signed displacements in any actual allocation of a proper hit reduce to
the residues of the two primes, regardless of which anchor produced the hit. -/
private theorem signed_of_lift {D p q : ℕ} {w : ℤ} (nz : w≠0) (hit : Lift D p q w) :
    ∃ t∈w.divisorsAntidiag, (p:ℤ)≡t.1 [ZMOD D] ∧ (q:ℤ)≡t.2 [ZMOD D] := by
  obtain ⟨a,b,hw⟩ := hit
  exact ⟨(_, _),(Int.prodMk_mem_divisorsAntidiag nz).mpr hw.symm,
    Int.modEq_iff_dvd.mpr ⟨-a,by ring⟩,Int.modEq_iff_dvd.mpr ⟨-b,by ring⟩⟩

private theorem tally {h J : ℕ} (menu : ℕ → ℕ → Finset ℤ) (hc : h≤2047)
    (slots : ∀ H∈Ico (2^h) (2^h+2^h), ∀ c<2^1023, Odd c → (menu H c).card≤J)
    (cap : ∀ H∈Ico (2^h) (2^h+2^h), ∀ c<2^1023, Odd c → ∀ k∈menu H c,
      (output c (2^704) k).natAbs<2^1406)
    (fiber : ∀ (H c : ℕ) (t : ℤ×ℤ) (V : Finset (ℕ×ℕ)),
      (∀ z∈V, Accepted h menu z ∧ Word h H c z ∧
        (z.1:ℤ)≡t.1 [ZMOD (2:ℤ)^704] ∧ (z.2:ℤ)≡t.2 [ZMOD (2:ℤ)^704]) → V.card≤2^108)
    (S : Finset (ℕ×ℕ)) (hit : ∀ z∈S, Accepted h menu z) :
    S.card≤2^h*2^1023*(J*(5*2^176*2^108)) := by
  let heads := Ico (2^h) (2^h+2^h)
  let tails := range (2^1022)
  have coords {z : ℕ×ℕ} (hz : Accepted h menu z) :
      headWord h (z.1*z.2)∈heads ∧ ∃ b∈tails, low (z.1*z.2)=2*b+1 := by
    obtain ⟨pp,qp,_,pl,_,ql,_,nl,nh,_⟩ := hz
    have po := pp.odd_of_ne_two (lt_of_lt_of_le (by decide +kernel : 2<2^1023) pl).ne'
    have qo := qp.odd_of_ne_two (lt_of_lt_of_le (by decide +kernel : 2<2^1023) ql).ne'
    obtain ⟨m,hm⟩ := po.mul qo
    let n := z.1*z.2
    have eq := Nat.mod_add_div n (2^1023)
    have double : (2:ℕ)^1023=2*(2^1022) := by decide +kernel
    rw [double,Nat.mul_assoc] at eq
    have lt := Nat.mod_lt n (Nat.two_pow_pos 1023)
    refine ⟨mem_Ico.mpr (prefix_bounds hc nl nh),low n/2,?_,?_⟩
    · apply mem_range.mpr; dsimp [low]; omega
    · change n%2^1023=2*(n%2^1023/2)+1; dsimp [n] at *; omega
  have bundle (H : ℕ) (hH : H∈heads) (b : ℕ) (hb : b∈tails) (V : Finset (ℕ×ℕ))
      (hs : ∀ z∈V, Accepted h menu z ∧ Word h H (2*b+1) z) :
      V.card≤J*(2*(5*2^176)*2^108) := by
    let c := 2*b+1
    have clt : c<2^1023 := by have h := mem_range.mp hb; dsimp [c]; omega
    have parity : Odd c := ⟨b,rfl⟩
    have w {z : ℕ×ℕ} (hz : Accepted h menu z) (word : Word h H c z) :
        ∃ k∈menu H c, Lift (2^704) z.1 z.2 (output c (2^704) k) := by
      obtain ⟨pp,qp,ne,_,_,_,_,_,_,k,mem,a,f,probe⟩ := hz
      rw [word.1,show z.1*z.2%2^1023=c from word.2] at mem
      refine ⟨k,mem,?_⟩
      rw [←word.2]; unfold low
      rw [output_mod (by decide +kernel) (by decide +kernel : (2:ℕ)^704∣2^1023)]
      exact lift_of_probe pp qp ne probe
    have nz (k : ℤ) : output c (2^704) k≠0 := by
      obtain ⟨b,hb⟩ := parity
      unfold output
      rw [hb]; push_cast; omega
    apply (cover (menu H c) (fun k z => Lift (2^704) z.1 z.2 (output c (2^704) k)) _ (fun z hz => w (hs z hz).1 (hs z hz).2) ?_).trans
      (Nat.mul_le_mul_right _ (slots H hH c clt parity))
    intro k hk S hS
    let y := output c (2^704) k
    apply (cover y.divisorsAntidiag (fun t z => (z.1:ℤ)≡t.1 [ZMOD (2:ℤ)^704] ∧ (z.2:ℤ)≡t.2 [ZMOD (2:ℤ)^704]) _
      (fun z hz => by simpa only [Nat.cast_pow,Nat.cast_ofNat] using signed_of_lift (nz k) (hS z hz).2) ?_).trans
      (Nat.mul_le_mul_right _ (cap_card (nz k) (cap H hH c clt parity k hk)))
    intro t _ V' hv
    exact fiber H c t V' fun z hz => ⟨(hs z (hS z (hv z hz).1).1).1,(hs z (hS z (hv z hz).1).1).2,(hv z hz).2⟩
  have all := cover (S:=S) (heads ×ˢ tails) (fun (v : ℕ×ℕ) z => Word h v.1 (2*v.2+1) z)
    (J*(2*(5*2^176)*2^108)) (fun z hz => by
      obtain ⟨H,b,hb,eq⟩ := coords (hit z hz)
      exact ⟨(_,b),mem_product.mpr ⟨H,hb⟩,rfl,eq⟩) (fun v hv V hV =>
      bundle v.1 (mem_product.mp hv).1 v.2 (mem_product.mp hv).2 V (fun z hz => ⟨hit z (hV z hz).1,(hV z hz).2⟩))
  rw [card_product,show heads.card=2^h by simp [heads],show tails.card=2^1022 by simp [tails]] at all
  exact all.trans_eq (by ring)

/-- Successes of any predictor using just the two product words. The public menu
may contain J options per observation. The proof counts both displacement signs
and all upper carries, and charges the odd low words and the possible prefixes. -/
theorem at_704 {h J pop : ℕ} {S : Finset (ℕ×ℕ)} (menu : ℕ → ℕ → Finset ℤ)
    (bitsLo : 640≤h) (bitsHi : h≤711) (jp : 0<J)
    (den : 2^2046<21000000*pop)
    (slots : ∀ H∈Ico (2^h) (2^h+2^h), ∀ c<2^1023, Odd c → (menu H c).card≤J)
    (cap : ∀ H∈Ico (2^h) (2^h+2^h), ∀ c<2^1023, Odd c → ∀ k∈menu H c,
      (output c (2^704) k).natAbs<2^1406)
    (hits : ∀ z∈S, Accepted h menu z) : 2^(712-h)*S.card<J*pop := by
  have width : 2*2^(2047-h)≤MixedPrefixWords.D^2 := calc
    _ ≤ 2*2^1407 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
    _ = _ := by decide +kernel
  have count := tally menu (by omega) slots cap (fun H c t V hs =>
    MixedPrefixWords.word_card V (Nat.two_pow_pos (2047-h)) width (fun z hz => by
      obtain ⟨accepted,word,pr,qr⟩ := hs z hz
      obtain ⟨pp,qp,_,pl,ph,ql,qh,_⟩ := accepted
      refine ⟨pl,?_,ql,?_,pp.odd_of_ne_two (lt_of_lt_of_le (by decide +kernel : 2<2^1023) pl).ne',
        qp.odd_of_ne_two (lt_of_lt_of_le (by decide +kernel : 2<2^1023) ql).ne',word.1,word.2,?_,?_⟩
      · exact (show (2:ℕ)^1024=2*MixedPrefixWords.Q by decide +kernel) ▸ ph
      · exact (show (2:ℕ)^1024=2*MixedPrefixWords.Q by decide +kernel) ▸ qh
      · simpa only [MixedPrefixWords.D,Nat.cast_pow,Nat.cast_ofNat] using pr
      · simpa only [MixedPrefixWords.D,Nat.cast_pow,Nat.cast_ofNat] using qr)) S hits
  have sumPow : (2:ℕ)^(712-h)*2^h=2^712 := by
    rw [←pow_add,Nat.sub_add_cancel (by omega)]
  have numer : 2^(712-h)*S.card*21000000 ≤ J*2^2046 := calc
    _ ≤ 2^(712-h)*(2^h*2^1023*(J*(5*2^176*2^108)))*21000000 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ count)
    _ = J*((2^(712-h)*2^h)*2^1023*(5*2^176*2^108)*21000000) := by ac_rfl
    _ ≤ _ := by rw [sumPow]; exact Nat.mul_le_mul_left _ (by decide +kernel)
  have strict := numer.trans_lt (Nat.mul_lt_mul_of_pos_left den jp)
  exact Nat.lt_of_mul_lt_mul_right (by simpa only [mul_left_comm J 21000000,mul_comm 21000000,←mul_assoc] using strict)

/-- The first 640 variable bits and the last 1023 bits together, at radix 2^704. -/
theorem at_640_bits {J pop : ℕ} {S : Finset (ℕ×ℕ)} (menu : ℕ → ℕ → Finset ℤ)
    (jp : 0<J) (den : 2^2046<21000000*pop)
    (slots : ∀ H∈Ico (2^640) (2^640+2^640), ∀ c<2^1023, Odd c → (menu H c).card≤J)
    (cap : ∀ H∈Ico (2^640) (2^640+2^640), ∀ c<2^1023, Odd c → ∀ k∈menu H c,
      (output c (2^704) k).natAbs<2^1406)
    (hits : ∀ z∈S, Accepted 640 menu z) : 2^72*S.card<J*pop :=
  at_704 menu (by decide) (by decide) jp den slots cap hits

end PrimeFactors.MixedPrefixPopulation
