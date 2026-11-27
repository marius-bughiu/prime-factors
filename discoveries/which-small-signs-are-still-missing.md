# Which clues are still missing about each prime?

On 246,180,296,426,219 we recovered three small square classes from the product. Knowing them narrows the possible divisors from 1,920 to 240 positions in a repeating list. Two further questions would narrow it to 60. Do 3 and 5 each have a square root modulo the input? Answering yes requires just one root that we can check. Getting a correct no from an unsuccessful search is harder. [How the first three roots were obtained](combining-remainders-to-skip-divisors.md)

## Reading the two primes' signs

Take an odd product $N=pq$ of distinct primes and a list of $s$ signed integers coprime to $N$. A prime's sign for a generator is positive if that generator has a square root at the prime and negative otherwise. Encode positive by 0 and negative by 1. Each prime has a row of $s$ bits, say $x$ and $y$. The product gives us $n=x+y$ from its Jacobi symbols, with addition modulo two.

A mask $h$ selects generators to multiply. Its product has a square root modulo $N$ exactly when both $x(h)=0$ and $y(h)=0$. Suppose $n$ has a nonzero entry. Choose a mask $a$ with $n(a)=1$, and call the row with $x(a)=0$ the first one. This labels the factors by a test they disagree on. For any desired mask $v$, put $h=v+n(v)a$. Then $n(h)=0$, so the factors agree on $h$. The product selected by $h$ has a square root modulo $N$ exactly when $x(v)=0$. The public row then supplies $y(v)$ as well.

If the initial root witnesses cover $r$ independent masks, exactly $2^{s-r-1}$ unordered pairs of abstract rows fit that information. A basis for the remaining directions gives **$s-r-1$ yes-or-no questions**, one per direction. They distinguish every pair. Fewer binary answers cannot separate all $2^{s-r-1}$ possibilities. This counts queries when each answer is available. Deciding whether a number of positive Jacobi sign has a square root modulo a composite is the classical quadratic residuosity problem. Neither the proof nor the query count supplies a fast algorithm for it. [Lean proofs and exact count](../PrimeFactors/RootableSignSpan.lean) · [Goldwasser and Micali, section 4](https://people.csail.mit.edu/silvio/Selected%20Scientific%20Papers/Encryption/Probabilistic_Encryption.pdf)

## Four genuinely possible answers

On the 48-bit example we use the six generators $-1,2,3,5,7,11$. The three known independent masks have products $-11,14,22$. The public Jacobi signs of 3 and 5 are both positive. Four possible pairs of hidden sign rows remain. They correspond exactly to the four ways the primes can agree on the signs of 3 and 5. The table gives four other products with the same public residue **5,699 modulo 9,240**, the same bit width as one another and square roots of all three specified classes.

| Product | Checked primes | Sign of 3 at both | Sign of 5 at both |
|---:|---:|:---:|:---:|
| 138,051,299 | 9,241 × 14,939 | + | + |
| 135,205,379 | 8,779 × 15,401 | − | + |
| 146,626,019 | 11,027 × 13,297 | + | − |
| 145,951,499 | 9,067 × 16,097 | − | − |

Each product has its own numerical root witnesses. The ambiguity concerns the product residue and the *existence* of the specified roots. An algorithm reading the entire product can use other information. [Four Lean certificates](../PrimeFactors/SignAmbiguityExamples.lean)

At 2,048 bits this ambiguity occurs on many actual products. Fix any unit residue $C$ modulo 9,240 and any collection of small masks whose roots are required to exist. For **each** compatible pair of six-bit sign rows, more than $2^{2000}$ distinct products of two 1,024-bit primes have that pair of rows, are 2,048 bits long, have residue $C$, and admit every required root. To see why, choose a residue $a$ realizing the first row and set $b=C/a$ modulo 9,240. Every possible sign row occurs on the wheel. The second residue gives the other row by multiplicativity. With $U=2^{1024}$, select the first prime from $(3U/4,7U/8]$ and the second from $(7U/8,U]$. Each chosen residue has over $2^{1000}$ primes in its respective interval. Unique factorization makes every product distinct. Lean proves the deduction using the published unconditional estimate for primes in arithmetic progressions as an explicit premise. [Residue and sign proof](../PrimeFactors/PrimeResidueSignWheel.lean) · [Prime counts](../PrimeFactors/PrimeResidueRealization.lean) · [Bennett, Martin, O’Bryant and Rechnitzer, Theorem 1.2](https://personal.math.ubc.ca/~bennett/BeMaObRe-IJM-2018.pdf#page=5)

For our original 48-bit product the answers are **yes for 3 and no for 5**. A public search for the first answer found two different square roots of 3 whose difference already gave a prime factor. Knowing both answers in advance would reduce direct division from 14,474 tests to 3,621. That last figure prices a search with supplied answers. The new method of obtaining the first answer has its own measured cost. [Finding the roots from the original product](skipping-impossible-square-root-searches.md)

## When can the product supply a negative answer?

For the deliberately chosen product 24,881 the factors' bit widths put their sum between 316 and 322. A public pair of numbers, 15,252 and 8,047, satisfies the equations for a point of order five on the circle modulo the product. If −1 had a square root there, this point would force the sum to be 7 modulo 25. No integer in the interval qualifies. This certifies that −1 is a nonsquare at both primes.

We chose the example using the primes 139 and 179. Starting over with the product, the first positive integer satisfying $5t^4-10t^2+1=0$ modulo 24,881 is 577. Evaluating $(t^2-1)/(t^2+1)$ and $2t/(t^2+1)$ modulo the input then reproduces the witness. Ordinary Fermat search recovers the primes in two square tests. More generally, when the possible sum interval misses an entire residue class modulo $m^2$, it contains at most one representative of each of the two proposed sum classes. That makes this a certificate of additional information on some inputs, with a competing direct route to the factors. [Order, sum and interval proofs](../PrimeFactors/SameSignSumWindow.lean)
