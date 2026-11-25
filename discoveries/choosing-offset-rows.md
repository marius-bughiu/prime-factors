# Choosing the coordinate frame from the product

Changing the coordinate frame reduced the count of surviving offsets by **22,503,769,796** on the fresh 2048-bit input and **10,977,960,641** on the crossed input. Each search covered the same first $2^{40}$ offsets as its baseline. Counting took longer in both chosen frames because their coordinates spread the points over more rows. The timing comparison counted survivors. Separate benchmark runs tested 64 survivors in each frame and found no factor. The two frames may keep different offsets. [Timing samples, scores and exact counts](../research/grouped-offset-frames.json) · [Original row counter](grouped-offset-rows.md) · [Selection and replay](../experiments/grouped_offset_frame.py)

## A score that can be computed before the search

From $N$ compute $T=\lfloor\sqrt N\rfloor$ and $h=N-T^2$. Each offset $1\le j\le J$ supplies $k=\lfloor(Tj-1)/h\rfloor$. Test positive $k$ with $\gcd(j,k)=1$. A successful offset requires the discriminant $F(j,k)=j^2+4k(Tj-hk)$ to be a square. With columns $V=(B,A)$, $W=(C,D)$ and $BD-AC=1$, write $(j,k)=rV+tW$. The inverse change has integer entries, so $\gcd(r,t)=1$. If $p^w\mid t$, the discriminant reduces to $r^2F(V)$ modulo $p^w$ and $r$ is a unit. Thus an obstruction to $F(V)$ being a square modulo $p^w$ excludes that point. The same argument uses $F(W)$ when $p^w\mid r$. [Modular tests](../experiments/grouped_offset_rows.py)

For each prime $p\le251$, take the least obstructing power on each axis, when one exists. In a complete period modulo $p^m$, with $m\ge w$, there are $p^{2m}-p^{2m-2}$ residue pairs primitive at $p$. Of them, $p^{m-w}(p^m-p^{m-1})$ have $p^w\mid t$. Their fraction is $1/((p+1)p^{w-1})$. The forbidden sets on the two axes are disjoint because a primitive pair cannot have both coordinates divisible by $p$. Subtract the two fractions from one, then multiply the resulting survival fractions across primes by the Chinese remainder theorem. This gives the exact score for a complete modular period conditioned on primitivity at those primes. The actual offsets follow a narrow strip, and the final count includes obstructions at larger primes. The score can rank two frames in the opposite order from their actual finite counts. [Score and complete small-period check](../experiments/grouped_offset_frame.py)

Starting with the continued-fraction frame, enumerate every change $V'=iV+k'W$, $W'=j'V+lW$ with entries in $[-4,4]$ and $il-j'k'=1$. Require $B'>0$ and require the row counter's bounds for both absolute coordinates to be at most $8\lceil\sqrt J\rceil$. Minimize the exact rational score. Ties prefer the smaller row span, then the shorter coordinate prefix, then lexicographic change entries. The choice uses only the product and $J$. If no change qualifies, the experiment uses the original frame and reports the abstention.

## Two 2048-bit products

| Product | Eligible frames | Original → chosen score | Original → chosen full survivors | Original → chosen nonempty rows | Seconds, original → chosen |
|---|---:|---:|---:|---:|---:|
| Fresh | 37 | 0.24404 → 0.13950 | 41,878,707,496 → 19,374,937,700 | 420,117 → 4,314,359 | 2.28 → 17.55 |
| Crossed | 73 | 0.22834 → 0.15869 | 35,042,535,262 → 24,064,574,621 | 750,667 → 2,230,897 | 3.64 → 9.05 |

The chosen changes $(i,j',k',l)$ were $(2,-3,-1,2)$ and $(1,-3,-1,4)$ respectively. The primitive counts agreed exactly within each comparison: 668,422,917,531 for fresh and 668,422,918,155 for crossed. Runtimes are local medians over three paired rounds with alternating scan order. Each chosen run includes a new selection, whose median took 2.2 ms and 3.6 ms respectively. The full tests reduced the survivor counts by 53.74% and 31.33%. [2048-bit inputs](../benchmarks/grouped-norm.json)

A second, predeclared comparison also required the row span to fit the original and the prefix length to stay within twice the original. On fresh, the score decreased from 0.24404 to 0.24046 but full survivors **increased** to 42,693,153,755. Counting took 2.51 seconds, versus 2.33 seconds in that comparison's baseline. On crossed, the rule selected the original frame. Its two runs took 3.65 and 3.60 seconds including selection where applicable.

## Independent small-input checks

On all eight frozen 16-bit-prime-pair products, we checked every offset through $J=4096$ individually and compared exact counts for both frames. The main selector reduced total survivors from 5,662 to 1,962 and retained the panel's one exact square hit. Seven products had an eligible frame, and one kept the original after the coordinate cap excluded all candidates. Summing the per-product medians gave 24.4 ms including selection versus 2.4 ms for the original. The cost-constrained selector left 3,823 survivors and retained the same hit. [Frozen inputs](../research/quartic-lane-holdout.json)

Run `python3 -m experiments.grouped_offset_frame` for the two full-size inputs. Use `--holdout` for the small inputs and finite-period check, or `--cost-constrained` to apply the secondary rule. Each run reports exact scores, row counts, survival counts and all timing samples.
