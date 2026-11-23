# Finite checks

From the repository root, run

```sh
python experiments/check.py
```

The script uses the Python standard library (Python 3.8 or later). Each comparison uses integer or rational arithmetic. The program exits with an error if a comparison fails. The reference output is in [expected.txt](expected.txt).

## Ordered Goldbach counts

For $N=50050$, the script counts all ordered prime pairs summing to $N-4ki$ for $24\le k\le48$ and $1\le i\le10$. One calculation sieves the primes and checks the complement of each prime. The other generates primes by trial division, encodes their indicator as the digits of a single integer and squares it. With base $256^b>N$, every coefficient fits in one digit, so the digit at the target index gives the ordered count. The output prints two progressions, one with composite $k=35$ and the other with prime $k=37$.

## Local moments

For $P=3\cdot5\cdot7\cdot11$, the program averages the product of $u_p$ over the primes $p\mid P$ dividing $N-4ik$. The Chinese remainder theorem gives the factor $1+(u_p-1)\Pr(p\mid N-4ik)$ at each prime. The program checks both choices of sampling space.

| Condition | All residues $k\bmod P$ | Unit residues $k\bmod P$ |
| --- | --- | --- |
| $p\mid i$ and $p\mid N$ | 1 | 1 |
| $p\mid i$ and $p\nmid N$ | 0 | 0 |
| $p\nmid i$ and $p\mid N$ | $1/p$ | 0 |
| $p\nmid i$ and $p\nmid N$ | $1/p$ | $1/(p-1)$ |

The entries are local probabilities. For each of three choices of $N\bmod P$ and 24 indices $i$, the script checks the singular-series weights $u_p=(p-1)/(p-2)$ and the exponential weights $u_p=2^{P/p}$. The latter give the paper's moment with $\tau=P\log 2$ over this finite set of primes. The unit experiment enumerates every reduced residue class. The paper treats the distribution of actual prime multipliers in a long interval analytically.

## Simultaneous divisibility and sieving

The block of primes $5<p\le17$ has product $17017$. The script solves $ih\equiv N\pmod{17017}$ for three anchors and three steps $h=60k$, then enumerates all qualifying positive indices through $34051$. A multiplier sharing an incompatible factor with the modulus gives an empty class.

For $N=7\cdot2^{26}$ it also excludes $k$ whenever one of these four primes divides $N-60k$ or $N-120k$. Exactly 8910 multipliers survive in one full period. On the shorter interval $101\le k\le2193$, the order-three and order-four Bonferroni sums give 1096 and 1097, respectively. Direct counting gives 1097. These examples check the arithmetic used in the proof. The limiting distribution is derived in the paper.
