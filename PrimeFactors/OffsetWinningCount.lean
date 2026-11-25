import PrimeFactors.CompleteOffsetWork
import PrimeFactors.OffsetSquareWitness
import PrimeFactors.OffsetShortVectors

namespace PrimeFactors.OffsetWinningCount
open Finset CompleteOffsetSearch CompleteOffsetWork

/-- Distinct sharp primitive positions at which the public probe returns a proper divisor. -/
noncomputable def winners (N : ℕ) : Finset (ℕ × ℕ) :=
  (slots N.sqrt (N-N.sqrt^2)).filter fun z => (probe N N.sqrt z.1 z.2).isSome

theorem mem_winners {N j k : ℕ} : (j,k) ∈ winners N ↔
    (j,k) ∈ slots N.sqrt (N-N.sqrt^2) ∧ (probe N N.sqrt j k).isSome := by
  exact mem_filter

private theorem indices_card {p q T : ℕ} (s : Finset (ℕ × ℕ)) (P : ℕ × ℕ → Prop)
    (witness : ∀ z∈s, ∃ v : ℕ × ℕ, P v ∧ z.2=v.1*v.2 ∧
      z.1+2*T*z.2=p*v.1^2+q*v.2^2)
    (few : ∀ a : Finset (ℕ × ℕ), (∀ x∈a, P x) → a.card≤2) : s.card≤2 := by
  classical
  let coords (z : ↥s) := Classical.choose (witness z.val z.property)
  have spec (z : ↥s) : P (coords z) ∧ z.val.2=(coords z).1*(coords z).2 ∧
      z.val.1+2*T*z.val.2=p*(coords z).1^2+q*(coords z).2^2 :=
    Classical.choose_spec (witness z.val z.property)
  have inj : Function.Injective coords := by
    intro x y eq
    obtain ⟨_,kx,jx⟩ := spec x
    obtain ⟨_,ky,jy⟩ := spec y
    rw [eq] at kx jx
    have k := kx.trans ky.symm
    rw [k] at jx
    exact Subtype.ext (Prod.ext (Nat.add_right_cancel (jx.trans jy.symm)) k)
  have bound := few (s.attach.image coords) (by
    intro x hx
    obtain ⟨z,_,rfl⟩ := mem_image.mp hx
    exact (spec z).1)
  simpa only [card_image_of_injective _ inj,card_attach] using bound

theorem has_winner {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p<q)
    (balance : q≤2*p) (large : 17≤p) : 0<(winners (p*q)).card := by
  obtain ⟨j,k,short,domain,found⟩ := complete_balanced pp qp ord balance large
  apply card_pos.mpr
  refine ⟨(j,k),mem_filter.mpr ⟨sharp_iff.mpr ⟨short,domain⟩,?_⟩⟩
  rcases found with hit|hit <;> simp [hit]

/-- For a balanced distinct prime pair the entire region has one or two
successful slots. One picks the orientation of the first weight by p. -/
theorem one_or_two {p q : ℕ} (pp : p.Prime) (qp : q.Prime) (ord : p<q)
    (balance : q≤2*p) (large : 17≤p) :
    1≤(winners (p*q)).card ∧ (winners (p*q)).card≤2 := by
  refine ⟨has_winner pp qp ord balance large,?_⟩
  let T := (p*q).sqrt
  let h := p*q-T^2
  obtain ⟨root,off,_⟩ := balanced_parameters pp qp ord balance large
  change T^2+h=p*q at root
  change 0<h at off
  have det : (p:ℤ)*q-(T:ℤ)^2=h := by
    have eq : (T:ℤ)^2+h=(p:ℤ)*q := by exact_mod_cast root
    linarith only [eq]
  obtain ⟨i,oi⟩ := pp.odd_of_ne_two (by omega)
  have odd : Odd (p:ℤ) := ⟨(i:ℤ),by exact_mod_cast oi⟩
  apply indices_card (p:=p) (q:=q) (T:=T) _ (OffsetShortVectors.Short p T q h)
  · rintro ⟨j,k⟩ hz
    obtain ⟨slot,found⟩ := mem_filter.mp hz
    obtain ⟨short,dom⟩ := sharp_iff.mp slot
    change (probe (p*q) T j k).isSome = true at found
    obtain ⟨f,hit⟩ := Option.isSome_iff_exists.mp found
    obtain ⟨s,v,sp,_,cop,ks,form⟩ := OffsetSquareWitness.exists_vector_of_hit pp qp ord.ne
      dom.2.2.1 dom.2.2.2.2 hit
    refine ⟨(s,v),⟨sp,cop,?_⟩,ks,form⟩
    have eq : (j:ℤ)+2*(T:ℤ)*k=(p:ℤ)*s^2+(q:ℤ)*v^2 := by exact_mod_cast form
    have kz : (k:ℤ)=(s:ℤ)*v := by exact_mod_cast ks
    have val : ReducedOffsetMinimum.Q p T q s v=(j:ℤ) := by
      unfold ReducedOffsetMinimum.Q
      rw [kz] at eq
      linarith only [eq]
    change 3*(ReducedOffsetMinimum.Q p T q s v)^2≤4*(h:ℤ)
    rw [val]
    exact_mod_cast short
  · exact OffsetShortVectors.card_le_two odd (by exact_mod_cast pp.pos) (by exact_mod_cast off) det

/-- The count and the cost of a uniform draw, with exactly 2,048 input bits.
The inequality is written without division and holds for each individual input. -/
theorem target_fraction {N p q : ℕ} (pair : p*q=N) (pp : p.Prime) (qp : q.Prime)
    (distinct : p≠q) (pbits : 2^1023≤p ∧ p<2^1024) (qbits : 2^1023≤q ∧ q<2^1024)
    (size : 2^2047≤N) :
    1≤(winners N).card ∧ (winners N).card≤2 ∧
      2^1018*(winners N).card<(slots N.sqrt (N-N.sqrt^2)).card := by
  have large : 17≤(2:ℕ)^1023 := by decide +kernel
  have twice : (2:ℕ)^1024=2*2^1023 := by decide +kernel
  have bounds (a b : ℕ) (pair' : a*b=N) (pa : a.Prime) (pb : b.Prime) (ord : a<b)
      (bal : b≤2*a) (lo : 17≤a) : 1≤(winners N).card ∧ (winners N).card≤2 ∧ N.sqrt^2<N := by
    obtain ⟨_,hp,_⟩ := balanced_parameters pa pb ord bal lo
    have two := one_or_two pa pb ord bal lo
    rw [pair'] at hp two
    exact ⟨two.1,two.2,by omega⟩
  have result : 1≤(winners N).card ∧ (winners N).card≤2 ∧ N.sqrt^2<N := by
    rcases lt_or_gt_of_ne distinct with ord|ord
    · exact bounds p q pair pp qp ord (by omega) (by omega)
    · exact bounds q p ((Nat.mul_comm ..).trans pair) qp pp ord (by omega) (by omega)
  have cost := target_work size result.2.2
  have scale : (2:ℕ)^1018*2=2^1019 := by decide +kernel
  exact ⟨result.1,result.2.1,((Nat.mul_le_mul_left (2^1018) result.2.1).trans_eq scale).trans_lt cost⟩

/-- The upper bound is attained. Both distinct public slots pass the sharp
cutoff for 1891 and the probes return its two different primes. -/
theorem two_winners_example :
    1891=31*61 ∧ (1891:ℕ).sqrt=43 ∧ 1891-43^2=42 ∧
    (3*6^2≤4*42 ∧ InSchedule 43 42 6 1 ∧ probe 1891 43 6 1=some 31) ∧
    (3*7^2≤4*42 ∧ InSchedule 43 42 7 6 ∧ probe 1891 43 7 6=some 61) := by
  unfold InSchedule probe
  decide +kernel

end PrimeFactors.OffsetWinningCount
