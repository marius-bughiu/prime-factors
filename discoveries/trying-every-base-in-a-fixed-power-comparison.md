# Would another starting number have found a factor?

We tried an idea that gave us a factor on a small example. Pick a starting number, raise it to several powers, and compare the remainders. We wanted to know whether our two 2,048-bit tests had failed simply because we picked the wrong starting number. For one specific part of the search, we can now answer that question for **every** starting number coprime to each product.

We used the published factors to evaluate the search. The search itself prepares its guesses from the product alone. We capped the multiplier at 64 and tried at most two positions in each row. Changing these limits changes the question.

| 2,048-bit product | Distinct comparisons | Starting numbers that give a factor in any comparison after setup | Starting numbers that give a factor by comparing different gaps after setup |
| --- | ---: | ---: | ---: |
| Independently generated | 8 | 48 | 0 |
| Crossed construction | 36 | 0 | 0 |

Each input has more than $2^{2047}$ eligible starting numbers. All 48 successes on the first input occur in the original, same-gap comparison. Choosing a starting number uniformly gives that stage a chance below $2^{-2041}$. The preliminary checks have their own successes. They split the product for fewer than one in $2^{1021}$ eligible starting numbers on the first input and fewer than one in $2^{717}$ on the second. Some of those bases would also work later if the search continued. The last column counts only cases where the later comparison adds a way to split the number. [Exact integer counts](../research/trace-base-population.json) · [How the comparison works](comparing-weighted-powers-at-both-primes.md)

## How to count without trying every base

Let $N=pq$ with distinct odd primes. For a starting number $u$ coprime to $N$, let $r$ and $t$ be the smallest positive exponents for which its power returns to 1 modulo $p$ and $q$, respectively. These orders divide $p-1$ and $q-1$. Write $h=(N-1)/2$. A search position specifies the weight sum $c$, a guessed weighted factor sum $s$, and the comparison gap $d$. It compares $X=u^{s-(h+1)c}$ with $Y=u^{hd}$ using the key $X+X^{-1}$.

Over a prime field, two keys match exactly when $X=Y$ or $XY=1$. Define $A=|s-(h+1)c-hd|$ and $B=|s-(h+1)c+hd|$. A local scalar match means the local order divides $A$. A local inverse match means it divides $B$. The full key matches and $\gcd(X-Y,N)=p$ exactly when $r\mid A$, $t\mid B$ and $t\nmid A$. Interchanging the primes gives the other branch. A preliminary check at gap $d'$ splits the number exactly when just one of $r,t$ divides $(N-1)d'$.

These rules let us eliminate many orders with a few integer gcds. In the first branch the orders divide $\gcd(p-1,A)$ and $\gcd(q-1,B)$. If all remaining orders on one side divide a preliminary exponent, every order on the other side that survives setup must divide that exponent too. Taking the gcd tightens its bound. Lean checks this implication at every step. On the first input the only winning order pairs left after setup are $(7,8)$ and $(14,8)$, with $p<q$. A cyclic group has $\varphi(r)$ elements of order $r$, and the Chinese remainder theorem combines the two independent choices uniquely. This gives $6\cdot4+6\cdot4=48$. On the second input every candidate branch is impossible. [Lean theorems](../PrimeFactors/TraceOrderPopulation.lean) · [Full-size certificate generator](../experiments/trace_population_receipt.py)

The calculation behind the full table also counts bases for which just one local equality holds. It partitions the cyclic unit group at each prime into classes on which every tested divisibility has the same answer. Intersections are gcds of subgroup sizes. Subtracting smaller classes gives their exact populations. The code multiplies the two local class sizes and adds the disjoint results. The group-size calculation needs the prime factors, so these counts diagnose the search after the fact. They give no direct way to select one of the successful starting numbers from $N$ alone. [Counting code](../experiments/trace_base_population.py) · [Direct enumeration on small products](../tests/test_trace_base_population.py)

Run `python3 -m experiments.trace_base_population --check` to regenerate the numerical table. Run `python3 -m experiments.trace_population_receipt` after `lake build` to check both prime factorizations and the two rightmost columns in Lean. The certificate checks the explicit finite lists of guesses produced by the public scheduling code. The exact setup and local-only counts in the JSON use the independent Python calculation.
