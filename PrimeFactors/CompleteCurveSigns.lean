import PrimeFactors.ThreeNormCurves

/-! Information about the two prime residues gained from an exhaustive search
of a signed reduced curve. The equivalences charge the full bounded search. -/
namespace PrimeFactors.CompleteCurveSigns

open ThreeNormCurves

def targets : List ℤ := [-1,2,-2,3,-3,6,-6]

/-- Nonnegative square-test coordinates on the reduced curve; the inequalities
and the denominator gcd are public. -/
def onCurve (N : ℕ) (D : ℤ) : Prop :=
  ∃ x y : ℕ, (x:ℤ)^2-D*(y:ℤ)^2=multiplier N D*N ∧
    (x:ℤ)^2+(abs D)*(y:ℤ)^2≤heightFactor N D*N ∧ y.Coprime N

theorem curve_iff {N : ℕ} (np : 0<N) (odd : Odd N) (no3 : ¬3∣N) {D : ℤ}
    (d : D∈targets) : onCurve N D ↔ IsSquare (D:ZMod N) := by
  constructor
  · rintro ⟨x,y,n,_,cop⟩
    have z := congrArg (fun z:ℤ => (z:ZMod N)) n
    push_cast at z
    rw [ZMod.natCast_self,mul_zero] at z
    have eq := sub_eq_zero.mp z
    have unit := (ZMod.isUnit_iff_coprime y N).mpr cop
    have root : ((x:ZMod N)*(y:ZMod N)⁻¹)^2=D := by
      rw [mul_pow,eq,mul_assoc,←mul_pow,ZMod.mul_inv_of_unit _ unit,one_pow,mul_one]
    exact ⟨_,by simpa [pow_two] using root.symm⟩
  · rintro ⟨r,sq⟩
    have rr : r^2=D := by simpa [pow_two] using sq.symm
    have bounds : 0<(abs D) ∧ (abs D)≤6 ∧ ¬IsSquare (D:ℚ) := by
      rw [Rat.isSquare_intCast_iff]
      simp only [targets,List.mem_cons,List.not_mem_nil,or_false] at d
      rcases d with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
    obtain ⟨w⟩ := SmallDiscriminantLattice.exists_representation np odd bounds.1 bounds.2.1 bounds.2.2 r rr
    obtain ⟨u⟩ := normalize np odd no3 d rr w
    refine ⟨u.x.natAbs,u.y.natAbs,by simpa [Int.natCast_natAbs] using u.norm,
      by simpa [Int.natCast_natAbs] using u.height,?_⟩
    apply (ZMod.isUnit_iff_coprime ..).mp
    cases hy : u.y with
    | ofNat y => simpa [hy] using u.unit
    | negSucc y => simpa [hy] using u.unit.neg

/-- For a positive public Jacobi sign the two local signs agree. A full miss
forces them both negative. -/
theorem miss_iff_negative {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (cop : p.Coprime q) (odd : Odd (p*q)) (no3 : ¬3∣p*q) {D : ℤ}
    (d : D∈targets) (positive : jacobiSym D (p*q)=1) :
    ¬onCurve (p*q) D ↔ legendreSym p D= -1 ∧ legendreSym q D= -1 := by
  rw [curve_iff (Nat.mul_pos hp.out.pos hq.out.pos) odd no3 d]
  have eq := jacobiSym.mul_right' D hp.out.ne_zero hq.out.ne_zero
  rw [← jacobiSym.legendreSym.to_jacobiSym p,← jacobiSym.legendreSym.to_jacobiSym q,positive] at eq
  have both : IsSquare (D:ZMod (p*q)) ↔ IsSquare (D:ZMod p) ∧ IsSquare (D:ZMod q) := by
    let e := ZMod.chineseRemainder cop
    constructor
    · rintro ⟨a,ha⟩
      have h := congrArg e ha
      rw [map_intCast,map_mul] at h
      exact ⟨⟨_,congrArg Prod.fst h⟩,⟨_,congrArg Prod.snd h⟩⟩
    · rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩
      refine ⟨e.symm (a,b),e.injective ?_⟩
      rw [map_mul,map_intCast,e.apply_symm_apply]
      exact Prod.ext ha hb
  rw [both]
  have pair : legendreSym p D=legendreSym q D := by
    have h := jacobiSym.trichotomy D p
    rw [←jacobiSym.legendreSym.to_jacobiSym p] at h
    rcases h with h|h|h <;> rw [h] at eq ⊢ <;> omega
  constructor
  · intro miss
    by_cases pn : legendreSym p D= -1
    · exact ⟨pn,pair.symm.trans pn⟩
    exact False.elim <| miss ⟨not_not.mp (fun n => pn ((legendreSym.eq_neg_one_iff p).mpr n)),
      not_not.mp (fun n => pn (pair.trans ((legendreSym.eq_neg_one_iff q).mpr n)))⟩
  · rintro ⟨h,_⟩ ⟨sq,_⟩
    exact (legendreSym.eq_neg_one_iff p).mp h sq


/-- The eight possible residues of primes above three. -/
noncomputable def lanes : Finset ℕ := {1,5,7,11,13,17,19,23}

/-- Local negative-sign lanes. Each list is verified against the Jacobi symbol. -/
noncomputable def negativeLanes (D : ℤ) : Finset ℕ :=
  if D= -1 then {7,11,19,23} else if D=2 then {5,11,13,19}
  else if D= -2 then {5,7,13,23} else if D=3 then {5,7,17,19}
  else if D= -3 then {5,11,17,23} else if D=6 then {7,11,13,17}
  else if D= -6 then {13,17,19,23} else ∅

private theorem table {D : ℤ} (d : D∈targets) {r : ℕ} (mem : r∈lanes) :
    jacobiSym D r = if r∈negativeLanes D then -1 else 1 := by
  simp only [targets,List.mem_cons,List.not_mem_nil,or_false] at d
  simp only [lanes,Finset.mem_insert,Finset.mem_singleton] at mem
  rcases d with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [negativeLanes]

private theorem odd_of_lane {n : ℕ} (mem : n%24∈lanes) : Odd n := by
  simp only [lanes,Finset.mem_insert,Finset.mem_singleton] at mem
  exact Nat.odd_iff.mpr (by omega)

theorem sign_at_lane {n : ℕ} (mem : n%24∈lanes) {D : ℤ} (d : D∈targets) :
    jacobiSym D n = if n%24∈negativeLanes D then -1 else 1 := by
  have step : 4*D.natAbs ∣ 24 := by
    simp only [targets,List.mem_cons,List.not_mem_nil,or_false] at d
    rcases d with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have h := CharacterDivisorColumn.periodic (odd_of_lane mem)
    (odd_of_lane (n:=n%24) (by simpa using mem)) D
    ((Nat.mod_modEq n 24).symm.of_dvd step)
  exact h.trans (table d mem)

theorem prime_lane {p : ℕ} (pp : p.Prime) (lp : 3<p) : p%24∈lanes := by
  have odd := Nat.odd_iff.mp (pp.odd_of_ne_two (by omega))
  have nd : ¬3∣p := fun h => by have e := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pp).mp h; omega
  simp only [lanes,Finset.mem_insert,Finset.mem_singleton]
  omega

theorem four_lanes {D : ℤ} (d : D∈targets) : (negativeLanes D).card=4 := by
  simp only [targets,List.mem_cons,List.not_mem_nil,or_false] at d
  rcases d with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem two_lanes {D E : ℤ} (d : D∈targets) (e : E∈targets) (distinct : D≠E) :
    (negativeLanes D ∩ negativeLanes E).card=2 := by
  simp only [targets,List.mem_cons,List.not_mem_nil,or_false] at d e
  rcases d with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases e with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> first | contradiction | decide


private theorem product_lane {a b : ℕ} (aok : a%24∈lanes) (bok : b%24∈lanes) :
    (a*b)%24∈lanes := by
  rw [Nat.mul_mod]
  simp only [lanes,Finset.mem_insert,Finset.mem_singleton] at aok bok
  rcases aok with h|h|h|h|h|h|h|h <;>
    rcases bok with j|j|j|j|j|j|j|j <;> rw [h,j] <;> decide

private theorem no_three {n : ℕ} (h : n%24∈lanes) : ¬3∣n := by
  simp only [lanes,Finset.mem_insert,Finset.mem_singleton] at h
  omega

open RootableSignSpan

private def allMasks : List (Mask 3) :=
  [![1,0,0], ![0,1,0], ![1,1,0], ![0,0,1], ![1,0,1], ![0,1,1], ![1,1,1]]

private def fromBits (s : Fin 3 → Bit) : List ℤ :=
  ((allMasks.filter fun v => (s 0*v 0 + s 1*v 1 + s 2*v 2) == 0).take 3).map
    fun v => (if v 0=0 then 1 else -1)*(if v 1=0 then 1 else 2)*(if v 2=0 then 1 else 3)

private theorem menu_bits (N : ℕ) :
    ThreeRootTargets.menu N ThreeRootTargets.signed =
      fromBits (fun i => bit (jacobiSym (ThreeRootTargets.signed i) N)) := by
  change ((allMasks.filter fun v => publicRow N ThreeRootTargets.signed v == 0).take 3).map
    (word ThreeRootTargets.signed) = _
  simp only [fromBits, publicRow,row_apply,Fin.sum_univ_three,word,Fin.prod_univ_three,
    ThreeRootTargets.signed,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons]
  congr 1
  funext v
  rw [word,Fin.prod_univ_three]
  rfl

/-- Menu determined directly by the residue modulo 24. -/
noncomputable def menu24 (r : ℕ) := (targets.filter fun d => decide (r∉negativeLanes d)).take 3

theorem menu_eq {N : ℕ} (good : N%24∈lanes) :
    ThreeRootTargets.menu N ThreeRootTargets.signed=menu24 (N%24) := by
  rw [menu_bits]
  have gs (i : Fin 3) : ThreeRootTargets.signed i∈targets := by fin_cases i <;> decide
  simp only [sign_at_lane good (gs _)]
  simp only [lanes,Finset.mem_insert,Finset.mem_singleton] at good
  rcases good with h|h|h|h|h|h|h|h <;> rw [h] <;> decide +kernel

theorem selected_nonnegative {r : ℕ} {d : ℤ} (mem : d∈menu24 r) :
    d∈targets ∧ r∉negativeLanes d := by
  exact (List.mem_filter.mp (List.mem_of_mem_take mem)).imp_right of_decide_eq_true

/-- For any selected target, rootability is wholly determined by which lane
one of its two actual factors occupies. -/
theorem miss_iff_lane {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (cop : p.Coprime q) (lp : 3<p) (lq : 3<q) {D : ℤ}
    (sel : D∈ThreeRootTargets.menu (p*q) ThreeRootTargets.signed) :
    ¬onCurve (p*q) D ↔ p%24∈negativeLanes D ∧ q%24∈negativeLanes D := by
  have pl := prime_lane hp.out lp
  have ql := prime_lane hq.out lq
  have prod := product_lane pl ql
  rw [menu_eq prod] at sel
  obtain ⟨d,good⟩ := selected_nonnegative sel
  have pos : jacobiSym D (p*q)=1 := by simp [sign_at_lane prod d,good]
  rw [miss_iff_negative cop (odd_of_lane prod) (no_three prod) d pos,
    jacobiSym.legendreSym.to_jacobiSym, jacobiSym.legendreSym.to_jacobiSym,
    sign_at_lane pl d,sign_at_lane ql d]
  split_ifs <;> simp_all


private theorem same_signs : ∀ a∈lanes, ∀ b∈lanes, ∀ d∈menu24 ((a*b)%24),
    a∈negativeLanes d ↔ b∈negativeLanes d := by decide +kernel

theorem miss_iff_first {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (cop : p.Coprime q) (lp : 3<p) (lq : 3<q) {D : ℤ}
    (sel : D∈ThreeRootTargets.menu (p*q) ThreeRootTargets.signed) :
    ¬onCurve (p*q) D ↔ p%24∈negativeLanes D := by
  rw [miss_iff_lane cop lp lq sel]
  have pl := prime_lane hp.out lp
  have ql := prime_lane hq.out lq
  rw [menu_eq (product_lane pl ql),Nat.mul_mod] at sel
  exact ⟨And.left,fun h => ⟨h,(same_signs _ pl _ ql D sel).mp h⟩⟩

private theorem line : ∀ n∈lanes, ∀ a∈lanes, ∀ A∈menu24 n, ∀ B∈menu24 n,
    ∀ C∈menu24 n, A≠B → A≠C → B≠C → a∈negativeLanes A →
      (a∈negativeLanes B ↔ a∉negativeLanes C) := by decide +kernel

/-- Once A is proved empty, exactly one of B and C remains soluble.
In particular a single witness on B then certifies that the entire C can be
skipped, whereas emptiness of B proves existence on C. -/
theorem remaining {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (cop : p.Coprime q) (lp : 3<p) (lq : 3<q) {A B C : ℤ}
    (ha : A∈ThreeRootTargets.menu (p*q) ThreeRootTargets.signed)
    (hb : B∈ThreeRootTargets.menu (p*q) ThreeRootTargets.signed)
    (hc : C∈ThreeRootTargets.menu (p*q) ThreeRootTargets.signed)
    (ab : A≠B) (ac : A≠C) (bc : B≠C) (miss : ¬onCurve (p*q) A) :
    onCurve (p*q) B ↔ ¬onCurve (p*q) C := by
  have first := (miss_iff_first cop lp lq ha).mp miss
  have second := miss_iff_first cop lp lq hb
  have third := miss_iff_first cop lp lq hc
  have pl := prime_lane hp.out lp
  have prod := product_lane pl (prime_lane hq.out lq)
  rw [menu_eq prod] at ha hb hc
  have h := line _ prod _ pl _ ha _ hb _ hc ab ac bc first
  tauto


/-- A proved miss records true here. A single witnessed point records false. -/
noncomputable def after (D : ℤ) (miss : Bool) := if miss then negativeLanes D else lanes \ negativeLanes D

theorem recorded {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (cop : p.Coprime q) (lp : 3<p) (lq : 3<q) {D : ℤ}
    (sel : D∈ThreeRootTargets.menu (p*q) ThreeRootTargets.signed) (miss : Bool)
    (answer : miss = true ↔ ¬onCurve (p*q) D) :
    p%24∈after D miss ∧ q%24∈after D miss := by
  have pl := prime_lane hp.out lp
  have ql := prime_lane hq.out lq
  have first := (answer.trans (miss_iff_first cop lp lq sel))
  rw [menu_eq (product_lane pl ql),Nat.mul_mod] at sel
  have same := same_signs _ pl _ ql D sel
  cases miss <;> simp_all [after]

theorem two_after : ∀ d∈targets, ∀ e∈targets, d≠e → ∀ f g : Bool,
    (after d f ∩ after e g).card=2 := by decide +kernel

/-- Two independent observations, successes or complete failures, determine
the unordered pair of actual factor lanes when the product is not 1 mod 24. -/
theorem identified {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (cop : p.Coprime q) (lp : 3<p) (lq : 3<q) (n : (p*q)%24≠1) {A B : ℤ}
    (ha : A∈ThreeRootTargets.menu (p*q) ThreeRootTargets.signed)
    (hb : B∈ThreeRootTargets.menu (p*q) ThreeRootTargets.signed) (ab : A≠B)
    (f g : Bool) (ma : f=true ↔ ¬onCurve (p*q) A) (mb : g=true ↔ ¬onCurve (p*q) B) :
    after A f ∩ after B g = {p%24,q%24} := by
  obtain ⟨ap,aq⟩ := recorded cop lp lq ha f ma
  obtain ⟨bp,bq⟩ := recorded cop lp lq hb g mb
  have ql := prime_lane hq.out lq
  have prod := product_lane (prime_lane hp.out lp) ql
  rw [menu_eq prod] at ha hb
  have card := two_after A (selected_nonnegative ha).1 B (selected_nonnegative hb).1 ab f g
  have ne : p%24≠q%24 := by
    intro eq
    apply n
    rw [Nat.mul_mod,eq]
    exact (by decide : ∀ a∈lanes, a*a%24=1) _ ql
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le
  · simp [Finset.insert_subset_iff,ap,aq,bp,bq]
  · simp [card,ne]

/-- Choose the smaller residue from each possible factor pair. This is used
when the trial interval contains both factors. -/
noncomputable def scanLanes (r : ℕ) (S : Finset ℕ) : Finset ℕ := S.filter fun a => a≤(r*a)%24

private theorem companion : ∀ a∈lanes, ∀ b∈lanes,
    (a*b%24*a)%24=b ∧ (a*b%24*b)%24=a := by decide +kernel

theorem one_factor_lane {p q : ℕ} (pl : p%24∈lanes) (ql : q%24∈lanes)
    {S : Finset ℕ} (pm : p%24∈S) (qm : q%24∈S) :
    p%24∈scanLanes ((p*q)%24) S ∨ q%24∈scanLanes ((p*q)%24) S := by
  obtain ⟨atp,atq⟩ := companion _ pl _ ql
  simp only [scanLanes,Finset.mem_filter,Nat.mul_mod p q,pm,qm,atp,atq,true_and]
  exact le_total ..

/-- With different factor residues, trial division in a common factor
interval takes four residue progressions before observations, two after one
observation and one after two distinct observations. -/
theorem scan_counts : ∀ r∈lanes, r≠1 →
    (scanLanes r lanes).card=4 ∧ ∀ A∈menu24 r, ∀ f : Bool,
    (scanLanes r (after A f)).card=2 ∧ ∀ B∈menu24 r, A≠B → ∀ g : Bool,
    (scanLanes r (after A f ∩ after B g)).card=1 := by decide +kernel

/-- At product residue one the two factors have the same residue. Two
independent observations leave exactly two possible common residues. -/
theorem same_lane {p q : ℕ} (pl : p%24∈lanes) (ql : q%24∈lanes) (r : (p*q)%24=1) :
    p%24=q%24 := by
  have h := (companion _ pl _ ql).1
  rw [Nat.mul_mod p q] at r
  rw [r,one_mul,Nat.mod_mod] at h
  exact h


/-- Given two roots on a three-target line A*B*C=s², the third root can
be computed with a modular inverse. Its three-root readout is exactly one.
An additional independent root is needed for that readout to split N. -/
theorem derived_root {N : ℕ} {A B C r t : ZMod N} (s : (ZMod N)ˣ)
    (line : A*B*C=(s:ZMod N)^2) (ra : r^2=A) (tb : t^2=B) :
    let z := r*t*C*(↑s⁻¹:ZMod N)
    z^2=C ∧ r*t*z*(↑s⁻¹:ZMod N)=1 := by
  dsimp only
  have one : (A*B*C)*(↑s⁻¹:ZMod N)^2=1 := by
    rw [line,←mul_pow,Units.mul_inv,one_pow]
  constructor
  · calc
      _ = C*((A*B*C)*(↑s⁻¹:ZMod N)^2) := by rw [←ra,←tb]; ring
      _ = _ := by rw [one,mul_one]
  · calc
      _ = (A*B*C)*(↑s⁻¹:ZMod N)^2 := by rw [←ra,←tb]; ring
      _ = _ := one

/-- Project possible residues for one factor onto residues for the sum. -/
noncomputable def sumLanes (r : ℕ) (S : Finset ℕ) :=
  S.image fun a => (a+(r*a)%24)%24

theorem sum_mem {p q : ℕ} (pl : p%24∈lanes) (ql : q%24∈lanes)
    {S : Finset ℕ} (pm : p%24∈S) : (p+q)%24∈sumLanes ((p*q)%24) S := by
  refine Finset.mem_image.mpr ⟨p%24,pm,?_⟩
  rw [Nat.mul_mod p q,(companion _ pl _ ql).1,←Nat.add_mod]

/-- In each nontrivial product class two sign observations fix the factor
sum modulo 24. At product class seven the -3 observation alone fixes it. -/
theorem sum_counts : (∀ r∈lanes, r≠1 → ∀ A∈menu24 r, ∀ B∈menu24 r, A≠B →
    ∀ f g : Bool, (sumLanes r (after A f ∩ after B g)).card=1) ∧
    sumLanes 7 lanes={8,16} ∧ sumLanes 7 (after (-3) true)={16} ∧
    sumLanes 7 (after (-3) false)={8} := by decide +kernel

/-- On 77, the first negative answer is certified by enumerating a bounded
sum of squares. One point certifies the other answer. Neither step uses a
factor of the input. -/
theorem example_77 :
    ¬onCurve 77 (-1) ∧ onCurve 77 (-6) ∧
    after (-1) true ∩ after (-6) false = {7,11} ∧
    scanLanes (77%24) (after (-1) true ∩ after (-6) false) = {7} ∧
    77=7*11 ∧ Nat.Prime 7 ∧ Nat.Prime 11 := by
  refine ⟨?_,?_,by decide,by decide,by decide,by decide,by decide⟩
  · rintro ⟨x,y,n,_,_⟩
    norm_num [multiplier] at n
    have bound {x y : ℕ} (h : (x:ℤ)^2+(y:ℤ)^2=77) : x≤8 := by
      by_contra! bad
      have z : (9:ℤ)≤x := by exact_mod_cast bad
      nlinarith only [h,sq_nonneg (y:ℤ),sq_le_sq₀ (by decide : (0:ℤ)≤9) (Int.natCast_nonneg x) |>.mpr z]
    have h : (x:ℤ)^2+(y:ℤ)^2=77 := by linarith only [n]
    have hx := bound h
    have hy := bound (x:=y) (y:=x) (by linarith only [h])
    interval_cases x <;> interval_cases y <;> norm_num at h
  · exact ⟨10,3,by decide,by decide,by decide⟩

end PrimeFactors.CompleteCurveSigns
