import PrimeFactors.HighWordSuffixRanking

/-! A whole-number stop test for high-word and remainder ranking. The
certificate bounds all later rows using their maximum number of
admissible half-gap residues and the count achieved by an earlier row. -/

namespace PrimeFactors.WordRankingTail
open Finset PrimeFactors.HighWordSumRanking PrimeFactors.HighWordSuffixRanking

/-- A whole-number test that an interval of admissible half-gaps at
nonnegative squared distance d from the top of the product word has
diameter strictly below H. -/
def shortDiameter (w d H : ℕ) : Prop := w<H^2 ∨ (w-H^2)^2<4*H^2*d

/-- Two genuine gaps with spacing H force the larger square to use at
least H²+2Hv of the available width, where v is the smaller gap. -/
theorem diameter {x B n w u d H v t : ℕ} (depth : d≤u^2-(n+w))
    (cert : shortDiameter w d H) (hv : v∈gaps x B n w u) (ht : t∈gaps x B n w u) :
    t<v+H := by
  obtain ⟨_,_,_,_,top,_⟩ := mem_gaps.mp hv
  obtain ⟨_,_,_,bot,_,_⟩ := mem_gaps.mp ht
  have dl : d≤v^2 := by omega
  by_contra! bad
  have far := Nat.pow_le_pow_left bad 2
  have use : H^2+2*H*v≤w := by nlinarith only [far,top,bot]
  rcases cert with hw|hw
  · omega
  · have lin : 2*H*v≤w-H^2 := by omega
    have square := Nat.pow_le_pow_left lin 2
    have weighted := Nat.mul_le_mul_left (4*H^2) dl
    nlinarith only [square,weighted,hw]

/-- Group the points into blocks of P consecutive integers beginning at
their minimum. The block number and residue identify each point. -/
theorem count_in_span {S R : Finset ℕ} {P K c : ℕ} (pp : 0<P)
    (res : ∀ v∈S, v%P∈R) (multiplicity : R.card≤K)
    (short : ∀ v∈S, ∀ t∈S, t<v+P*(c/K)) : S.card≤c := by
  classical
  by_cases live : S.Nonempty
  · let l := S.min' live
    have lm : l∈S := S.min'_mem _
    have lower (v) (hv : v∈S) : l≤v := S.min'_le _ hv
    have image : S.card≤(R ×ˢ range (c/K)).card := by
      apply card_le_card_of_injOn (fun t => (t%P,(t-l)/P))
      · intro t ht
        apply mem_product.mpr
        refine ⟨res t ht,mem_range.mpr ((Nat.div_lt_iff_lt_mul pp).mpr ?_)⟩
        have span := short l lm t ht
        have ll := lower t ht
        rw [Nat.mul_comm (c/K) P]
        omega
      · intro t ht v hv eqs
        have rr : t%P=v%P := congrArg Prod.fst eqs
        have bb : (t-l)/P=(v-l)/P := congrArg Prod.snd eqs
        have tlo := lower t ht
        have vlo := lower v hv
        have res' : (t-l)%P=(v-l)%P := Nat.ModEq.add_right_cancel' l
          (by simpa only [Nat.sub_add_cancel tlo,Nat.sub_add_cancel vlo] using rr)
        have tdiv := Nat.mod_add_div (t-l) P
        have vdiv := Nat.mod_add_div (v-l) P
        rw [res',bb] at tdiv
        omega
    rw [card_product,card_range] at image
    exact (image.trans (Nat.mul_le_mul_right _ multiplicity)).trans (Nat.mul_div_le c K)
  · simp [Finset.not_nonempty_iff_eq_empty.mp live]

/-- Upper bound on a later midpoint before either of its roots is taken.
The bound K may count classes at just u or all residues of all later rows. -/
theorem no_improvement {x B n w u j P c K : ℕ} (f : ℕ→ℕ→Bool)
    (pp : 0<P) (later : j≤u)
    (multiplicity : ((range P).filter (fun r => f (u%P) r)).card≤K)
    (cert : shortDiameter w (j^2-(n+w)) (P*(c/K))) :
    (options x B n w P f u).card≤c := by
  have depth := Nat.sub_le_sub_right (Nat.pow_le_pow_left later 2) (n+w)
  refine count_in_span (S:=options x B n w P f u) (R:=(range P).filter (fun r => f (u%P) r)) pp ?_ multiplicity ?_
  · intro v hv
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ pp),(mem_filter.mp hv).2⟩
  · intro v hv t ht
    exact diameter depth cert (mem_filter.mp hv).1 (mem_filter.mp ht).1

/-- A bound for *all* later midpoints using one period of the public test
and one integer inequality. It applies independently of the size of B. -/
theorem tail {x B n w j P c K : ℕ} (f : ℕ→ℕ→Bool) (pp : 0<P)
    (per : ∀ s<P, ((range P).filter (fun r => f s r)).card≤K)
    (cert : shortDiameter w (j^2-(n+w)) (P*(c/K))) :
    ∀ u≥j, (options x B n w P f u).card≤c :=
  fun _ hu => no_improvement f pp hu (per _ (Nat.mod_lt _ pp)) cert

/-- Periodic table used by the suffix search, including the parity of odd factors. -/
def compatible (m σ s r : ℕ) : Bool :=
  decide (r%2=(s+1)%2) && productSuffix m σ s r

private theorem with_parity {x B n w P m σ u : ℕ} (evenP : 2∣P) :
    options x B n w P (compatible m σ) u = options x B n w P (productSuffix m σ) u := by
  ext v
  simp only [options,mem_filter,compatible,Bool.and_eq_true,decide_eq_true_eq]
  apply and_congr_right
  intro member
  have req := (mem_gaps.mp member).2.2.2.2.2
  have red (t : ℕ) : t%P≡t [MOD 2] := (show t%P≡t [MOD P] from Nat.mod_mod ..).of_dvd evenP
  have g : (v%P)%2=v%2 := red v
  have mid : (u%P+1)%2=(u+1)%2 := (red u).add_right 1
  simp only [g,mid,req,true_and]

/-- For a product remainder, the same stop certificate bounds the number
of actual sorted odd integer pairs in every remaining midpoint. -/
theorem suffix_pairs {x B n w j P m σ c K : ℕ} (pp : 0<P) (evenP : 2∣P) (period : m∣P)
    (per : ∀ s<P, ((range P).filter (fun r => compatible m σ s r)).card≤K)
    (cert : shortDiameter w (j^2-(n+w)) (P*(c/K))) :
    ∀ u≥j, (suffixPairs x B n w m σ u).card≤c := by
  intro u later
  rw [←options_card_pairs period,←with_parity evenP]
  exact tail _ pp per cert u later

end PrimeFactors.WordRankingTail
