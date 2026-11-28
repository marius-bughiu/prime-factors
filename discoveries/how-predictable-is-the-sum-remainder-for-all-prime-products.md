# Predicting the sum remainder across all full-width prime products

Pick two distinct 1,024-bit primes whose product has 2,048 bits. Give each such product equal weight. How many guesses would it take to name the remainder of the two primes’ sum modulo **7,239,457,225**? The order of the guesses may depend on the visible product remainder. Each guess names one attainable sum remainder, and the count includes the correct guess.

The best such rule averages **about 25,976,435 guesses**. Choosing a uniformly random order for the same candidate list averages **about 36,990,753**. That is a reduction of **more than 29.7758%**, with all eligible products counted. Lean proves the full-size comparison from published Dirichlet-GRH prime-count inequalities. A remainder guess still needs a way to recognize success, and many integer sums can share that remainder. [Population comparison and numerical bounds](../PrimeFactors/FiveSquarePooledRanks.lean)

## How the product changes the list

The modulus is the product of five prime squares. For each prime, the product remainder tells us whether it is a square modulo that prime. This gives five yes-or-no answers and therefore 32 patterns. For a square product at a given prime, two sum remainders are more frequent than the others modulo its square. For a nonsquare product at that prime, every attainable sum remainder has the same frequency.

| Product pattern | Best mean guesses in the modular model | Random-order mean | Reduction |
| --- | ---: | ---: | ---: |
| Square at all five primes | 9,806,148.896 | 20,883,632.5 | 53.0439% |
| Nonsquare at all five primes | 61,261,200.5 | 61,261,200.5 | 0% |
| All patterns pooled | 25,976,434.966 | 36,990,753.391 | 29.7759% |

The first row includes many product remainders in addition to one. In the second row every order ties. Lean checks the full table of 32 patterns and shows that the first and second rows have the highest and lowest relative savings. The pooled percentage divides the total saved guesses by the total random-order guesses. [All 32 exact results](../PrimeFactors/FiveSquareSignRanks.lean)

## From modular pairs to prime products

First sample two unit remainders independently and uniformly. Each possible product remainder has exactly 3,920,716,800 ordered pairs that produce it. Each of the 32 patterns occurs for exactly **122,522,400** product remainders. Choosing a different best list for each known product remainder gives the pooled optimum $159599216429/6144$. The random-order mean is $2367408217/64$. Both modular results are unconditional. [Counting product patterns](../PrimeFactors/FiveSquareSignPopulation.lean) · [Guess orders chosen from the product](../PrimeFactors/FiveSquarePolicy.lean)

For actual 1,024-bit primes the finite modular model alone cannot set the frequencies. The explicit estimate of Ernvall-Hytönen and Palojärvi bounds how many primes occur in each required residue class and interval. The comparison includes the condition that the product has 2,048 bits and counts each distinct pair once. For **any** ordering chosen from the product remainder, the actual mean differs from its modular mean by less than 0.001. Thus the actual optimum also lies within 0.001 of the modular optimum. The actual random-order baseline differs from its modular value by less than 0.0005. The repository takes the paper’s endpoint inequalities as hypotheses. [All-products transfer](../PrimeFactors/FiveSquareAllPrimeRanks.lean) · [Corollary 2 and its Dirichlet-GRH assumption](https://arxiv.org/pdf/2003.01925#page=2) · [Independent checks of the upstream Dirichlet-GRH statement](https://math.mit.edu/~drew/shortgrh/)

## Complete small prime populations

We enumerated all distinct, equal-width prime pairs whose product has twice the factor width. For tied weights we averaged over the positions in that group, so the result does not depend on an arbitrary tie-breaking rule. These are remainder-guess counts.

| Prime width | Eligible products | Patterns present | Reduction in mean guesses |
| --- | ---: | ---: | ---: |
| 8 bits | 148 | 31 | 28.178902% |
| 10 bits | 1,718 | 32 | 29.686167% |
| 12 bits | 19,546 | 32 | 29.317191% |
| 14 bits | 228,713 | 32 | 29.720999% |

The small samples give independent checks on the direction and size of the effect. The full-size result follows from the counting proof above. [Reproduce the complete censuses](../experiments/five_square_all_prime_census.py)

Among the 1,718 full-width products at ten bits per prime, 50 have the all-nonsquare pattern. For a checked example we selected one of the pairs requiring the fewest Fermat midpoints, $550{,}483=733\times751$. Each attainable remainder has exactly 32 ordered modular pairs and the mean is the same for every list. The separate factorization certificate takes one midpoint because the two primes are close. [Benchmark fixture](../benchmarks/cases.json)
