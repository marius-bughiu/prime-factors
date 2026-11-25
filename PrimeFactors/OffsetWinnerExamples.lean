import PrimeFactors.OffsetShortVectors
import PrimeFactors.OffsetSquareWitness
import PrimeFactors.GroupedOffsetRowExamples
import PrimeFactors.EuclideanHeightExample

namespace PrimeFactors.OffsetWinnerExamples
open CompleteOffsetSearch ReducedOffsetMinimum

/-- The factors are supplied as inputs to this retrospective diagnostic. -/
structure Control where
  N : ℕ
  T : ℕ
  p : ℕ
  q : ℕ
  s : ℕ
  v : ℕ

def Control.h (c : Control) := c.N-c.T^2
def Control.k (c : Control) := c.s*c.v
def Control.j (c : Control) := c.p*c.s^2+c.q*c.v^2-2*c.T*c.k
private def Control.d (c : Control) := Nat.dist (c.p*c.s^2) (c.q*c.v^2)

private def cutoff : ℕ := 2^512

private structure Valid (c : Control) : Prop where
  pair : c.p*c.q=c.N
  distinct : c.p≠c.q
  det : (c.p:ℤ)*c.q-(c.T:ℤ)^2=c.h
  hp : 0<c.h
  positive : 0<c.s
  cop : c.s.Coprime c.v
  norm : Q c.p c.T c.q c.s c.v=c.j
  jp : 0<c.j
  narrow : 4*c.h≤3*(cutoff)^2
  thin : c.j*cutoff<c.h
  short : 3*c.j^2≤4*c.h
  kp : 0<c.k
  prim : c.j.Coprime c.k
  cap : c.k≤c.T*c.j/c.h+1
  split : c.j+2*c.T*c.k=c.p*c.s^2+c.q*c.v^2
  gap : (c.j+2*c.T*c.k)^2=4*c.k^2*c.N+c.d^2
  gcdProper : 1<c.N.gcd ((c.j+2*c.T*c.k-c.d)/2) ∧ c.N.gcd ((c.j+2*c.T*c.k-c.d)/2)<c.N
  gcdLabel : c.N.gcd ((c.j+2*c.T*c.k-c.d)/2)=c.p ∨ c.N.gcd ((c.j+2*c.T*c.k-c.d)/2)=c.q

/-- The given position lies in the public schedule and actually returns a
factor. When the published labels are prime, every successful position in
that schedule is the one displayed here. -/
def Control.Receipt (c : Control) : Prop :=
  c.N.sqrt=c.T ∧ c.p*c.q=c.N ∧ 3*c.j^2≤4*c.h ∧ InSchedule c.T c.h c.j c.k ∧
  (probe c.N c.T c.j c.k=some c.p ∨ probe c.N c.T c.j c.k=some c.q) ∧
  (c.p.Prime → c.q.Prime → ∀ j k f, 3*j^2≤4*c.h → InSchedule c.T c.h j k →
      probe c.N c.T j k=some f → j=c.j ∧ k=c.k)

private theorem verify {c : Control} (sq : c.N.sqrt=c.T) (data : Valid c) : c.Receipt := by
  have loose : c.j ≤ (4*c.h).sqrt := Nat.le_sqrt'.mpr (by linarith only [data.short])
  refine ⟨sq,data.pair,data.short,⟨data.jp,loose,data.kp,data.cap,data.prim⟩,?_,?_⟩
  · have gap := data.gap
    have good : 4*c.k^2*c.N≤(c.j+2*c.T*c.k)^2 := by omega
    have sub : (c.j+2*c.T*c.k)^2-4*c.k^2*c.N=c.d^2 := by omega
    have actual : probe c.N c.T c.j c.k=some (c.N.gcd ((c.j+2*c.T*c.k-c.d)/2)) := by
      unfold probe
      dsimp only
      rw [sub,Nat.sqrt_eq']
      simp only [good,data.gcdProper,and_self,if_true]
    exact data.gcdLabel.elim (fun eq => Or.inl (actual.trans (congrArg some eq)))
      (fun eq => Or.inr (actual.trans (congrArg some eq)))
  · intro pp qp j k f short dom hit
    rw [←data.pair] at hit
    obtain ⟨s,v,_,_,cop,kv,label⟩ := OffsetSquareWitness.exists_vector_of_hit pp qp data.distinct
      dom.2.2.1 dom.2.2.2.2 hit
    have low : j≤cutoff := by
      have powers : j^2≤(cutoff)^2 := by linarith only [short,data.narrow]
      exact (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp powers
    have norm : Q c.p c.T c.q s v=(j:ℤ) := by
      unfold Q
      rw [kv] at label
      zify at label
      linarith only [label]
    have eq := OffsetShortVectors.unique_of_thin (x:=(c.s,c.v)) (y:=(s,v)) (J:=((cutoff:ℕ):ℤ))
      data.det (by exact_mod_cast data.hp) data.positive data.cop cop
      (data.norm.symm ▸ (show (0:ℤ)<c.j by exact_mod_cast data.jp))
      (by change Q c.p c.T c.q s v≤(cutoff:ℤ);rw [norm];exact_mod_cast low) (by
        change Q c.p c.T c.q c.s c.v*((cutoff:ℕ):ℤ)<c.h
        rw [data.norm]
        exact_mod_cast data.thin)
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    exact OffsetSquareWitness.indices_unique kv label rfl data.split

/-- Composing a control receipt with independent proofs of primality
characterizes every winning slot at the product's floor square root. -/
theorem winning_iff {c : Control} (receipt : c.Receipt) (pp : c.p.Prime) (qp : c.q.Prime) (j k : ℕ) :
    (3*j^2≤4*c.h ∧ InSchedule c.N.sqrt c.h j k ∧ ∃ f, probe c.N c.N.sqrt j k=some f) ↔
      j=c.j ∧ k=c.k := by
  obtain ⟨sq,_,short,dom,hit,unique⟩ := receipt
  rw [sq]
  constructor
  · rintro ⟨small,allowed,f,found⟩
    exact unique pp qp _ _ _ small allowed found
  · rintro ⟨rfl,rfl⟩
    exact ⟨short,dom,hit.elim (fun found => ⟨_,found⟩) (fun found => ⟨_,found⟩)⟩

def fresh : Control where
  N := ChebyshevQuarticScale.fresh
  T := GroupedOffsetRowExamples.fresh.T
  p := 155437199607556058012532697390816360200993450617775861977793885503041330648186435254461734869213045968256605640509036134253515311588040219325256786085481113217401073894164916964759494475637984845596500869609803951359509506709556269999261634541514057554539876849500776006036129784966133839608344624969272353567
  q := 161270605735527305106073331997188600389811486601036205205001425727786078300416814134106878399348029233962121752237344825423608369752978864046063434777553854865105371574916603604640605082441946447462046466208739893141681020415078708986222758892913779726834240750726240518693682341337270830209012662338065799537
  s := 59796909413026583010934277627880488944570117627284600892095993157351959395753
  v := 58705475657627045530828896969557490432125000803799478848303511880439625805987

private theorem fresh_data : Valid fresh := by
  constructor <;> decide +kernel

theorem fresh_receipt : fresh.Receipt :=
  verify (c:=fresh) (show fresh.N.sqrt=fresh.T from GroupedOffsetRowExamples.fresh_row.1) fresh_data

def crossed : Control where
  N := ChebyshevQuarticScale.crossed
  T := GroupedOffsetRowExamples.crossed.T
  p := EuclideanHeightExample.factorP
  q := EuclideanHeightExample.factorQ
  s := 20250098546238060458618583279339591586138973429101159848688925434831977317344
  v := 16861514544862843961171934008863255439044078779118846437587148217859649587439

private theorem crossed_data : Valid crossed := by
  constructor <;> decide +kernel

theorem crossed_receipt : crossed.Receipt :=
  verify (c:=crossed) (show crossed.N.sqrt=crossed.T from GroupedOffsetRowExamples.crossed_row.1) crossed_data

end PrimeFactors.OffsetWinnerExamples
