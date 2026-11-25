# Signed gaps when the trace shares a factor with 24

Let $N=pq$ with distinct primes $p,q\ge5$. In a guessed oriented coordinate pair $(s,v)$, put $k=sv$, $S=ps^2+qv^2$, and $z=ps^2-qv^2$. The earlier reciprocal formula at modulus 24 requires an invertible trace. A linear relation also covers traces divisible by 2 or 3. It can discard entire trace progressions using only $N,s,v$. [Earlier signed-gap lift](lifting-a-signed-gap.md) · [Lean proofs](../PrimeFactors/OffsetUnitTrace.lean)

Choose integers $u,w$ with $e=v^2u$ and $1-e=s^2w$. Set $C=1-2e$, $H=s^2+Nv^2$ and $B=u-Nw$. Since $p^2\equiv1\pmod{24}$, $q\equiv Np\pmod{24}$. Consequently

$$
S\equiv Hp\pmod{24},\qquad z\equiv CS+2k^2 Bp\pmod{48k^2}.
$$

Indeed $z-CS=2k^2(up-wq)$. The identity $v^2B+wH=1$ makes the two residue equations jointly invertible in the unknown label $p$. If $R=(z-CS)/(2k^2)$ is integral, the exact test for a **local unit label** is $HR\equiv BS\pmod{24}$ together with $\gcd(v^2R+wS,24)=1$. Equivalently the linear congruence on the original variables is $Hz\equiv(s^2-Nv^2)S\pmod{48k^2}$. A label passing the test still has to satisfy the integer square and product equations. [Theorems `unit_trace`, `projector_identity`, `eliminate_label` and `gap_equation`](../PrimeFactors/OffsetUnitTrace.lean)

## A single progression and an optional exclusion

Write $g=\gcd(H,24)$, $f=24/g$, and $L=\operatorname{lcm}(2,f)$. A trace has any labels precisely when $\gcd(S,24)=g$. Write $S=gt$ on this progression, and choose $\alpha$ inverse to $H/g$ modulo $f$ (use zero for $f=1$). Then $p\equiv\alpha t\pmod f$. Incorporating oddness gives an affine representative $p_0(t)$ modulo $L$. Use $\alpha t$ if $f$ is even. If $f$ is odd, take $A$ even with $A\equiv\alpha\pmod f$ and use $At+f$.

The full label projection onto the signed gap has just one progression

$$
z\equiv CS+2k^2 Bp_0(t)\pmod{2k^2 L},
$$

with one additional exclusion when $3\nmid f$. In that case remove $z\equiv CS\pmod{6k^2}$. To see this, multiplication by $B$ permutes the remaining $24/L$ classes, since $24/L$ divides $g$ and $v^2 B+wH=1$. If $3\mid f$, the trace already fixes the nonzero factor label modulo 3. Otherwise $3\mid g$, so $3\nmid B$ and the forbidden labels $p\equiv0\pmod3$ are exactly $R\equiv0\pmod3$. Thus a positive affine filter and at most one exclusion suffice. [Theorems `reduced_trace`, `digit_class`, `veto_three` and `join_affine`](../PrimeFactors/OffsetUnitTrace.lean)

For each feasible fixed trace there are exactly $8/\varphi(f)$ signed residues modulo $48k^2$. Their smallest positive circular separation is $2k^2L$, counting one full period for a singleton. The residues are uniformly spaced when $3\mid f$. Otherwise one of each three consecutive lattice points is absent. Lean checks the count and smallest separation for all eight possible $f$, all unit labels and every admissible multiplier $B$ modulo 24. [Theorem `fibre_count_and_spacing`](../PrimeFactors/OffsetUnitTrace.lean)

For $N=2501=41\cdot61$, $(s,v)=(5,4)$ gives $S=2001$, $z=49$, and $g=3$. The normalized digit $R$ is either 14 or 22 modulo 24. This trace shares a factor with 24, and both allowable residues must be retained. For $527=17\cdot31$ at $(1,1)$ the trace is 48 and $H=528$. All eight unit labels are possible at this trace, while the entire progression $S\not\equiv0\pmod{24}$ has none. These are exact local statements for the toy inputs. [Kernel-checked examples](../PrimeFactors/OffsetUnitTrace.lean)
