# One empty divisor interval excludes many weight assignments

On two public 2,048-bit products, one certified divisor-free interval per input ruled out more than 180 trillion assignments of weights in the rectangular search. The calculation uses the product and integer arithmetic. Both inputs remain unresolved. [Lean proof](../PrimeFactors/WeightDivisorSector.lean) · [Checked controls](../research/divisor-weight-sectors.json)

Suppose a pair of positive weights assigns $A$ to a divisor $p$ and $B$ to its partner $q=N/p$. In a rectangular search point, $y+x$ and $y-x$ are $tAp$ and $tBq$ in some order, with $t\ge 1$ and $x\le H$. Thus $|Ap-Bq|\le 2H$. If two integer endpoints satisfy

$$ (AL+2H)L\le BN,\qquad BN+2HU\le AU^2, $$

then $L\le p\le U$. An empty interval $[L,U]$ rules out this assignment. These same inequalities hold for every pair $(A+sV,B+sW)$ with $s\ge 0$ when $VL^2\le WN\le VU^2$. Choosing $VB-WA=1$ makes all these pairs coprime. An even step preserves the odd weights. One upper bound at the last index and two ratio comparisons certify that every product in the family passes the public multiplier scanner. The products strictly increase. [Formal statements](../PrimeFactors/WeightDivisorSector.lean)

| Public control | Distinct products with one excluded assignment | LLL calls | LLL swaps | Continued-fraction steps |
|---|---:|---:|---:|---:|
| Fresh 440 | 247,113,136,056,682 | 1 | 1,478 | 164 |
| Crossed three-quarters | 189,273,664,074,281 | 1 | 1,463 | 164 |

For both controls the center comes from the product. With $w=1024$, set $l=\max(2^{w-1},\lceil N/(2^w-1)\rceil)$ and $u=\lfloor\sqrt N\rfloor$. Set the low bit of $\lfloor(3l+u)/4\rfloor$ to one to obtain the odd center $c$. The endpoints are $c-2R$ and $c+2R$. The two radii come from earlier public experiments. The fresh input used $R=2^{440}$. On the crossed input, earlier searches missed the certificate height bound at $2^{440}$ and $2^{441}$ before the follow-up succeeded at $3\cdot2^{438}$. The table gives the cost of rerunning the successful settings. Construction factors and stored expected outcomes play no role in either rerun. [Prior experiments, including failed settings](sifting-a-divisor-window.md)

The lattice calculation proves that every integer in the selected interval fails to divide the public product. The continued fraction supplies a direction inside the inequalities. The family certificate checks its endpoints and scanner bounds without enumerating its members. Run `python3 -m experiments.divisor_weight_sectors --check` to regenerate both Lean certificates and compare their checked source hashes and work counts with the published figures. The experiment reuses the repository's MIT-licensed divisor-window and rectangle implementations. [Reproducer](../experiments/divisor_weight_sectors.py) · [Divisor interval certificates](../PrimeFactors/SiftedDivisorWindow.lean) · [License](../LICENSE)

A numerical multiplier can have other coprime weight factorizations. For $N=34{,}361{,}588{,}549$, the assignment $(65,33)$ at $k=2{,}145$ requires a divisor between 131,976 and 132,183, inclusive. There is none. The same multiplier also equals $55\cdot39$. Those weights give $(x,y)=(302,8{,}585{,}197)$ and $\gcd(y-x,N)=156{,}089$, whose prime partner is 220,141. Skipping an entire multiplier requires covering every eligible assignment that could yield a point. The two large counts measure exclusions for the specified weight pairs. End-to-end search savings remain unmeasured. [Checked example](../PrimeFactors/WeightDivisorSector.lean)
