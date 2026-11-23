# A Lean certificate for Goldbach partitions through $2^{32}$

Every even integer from 4 through 4,294,967,296 has a partition into two primes with a summand at most 1,789, with one exception. At 1,847,133,842 the least possible summand is 1,861, attained by

$$1{,}847{,}133{,}842 = 1{,}861 + 1{,}847{,}131{,}981.$$

The certificate covers all 2,147,483,647 even integers in this interval. The public theorems are available through `import Goldbach`. [Theorem statements](Goldbach/ExtendedOdd/Certificate32.lean)

| Lean declaration in namespace `Goldbach` | Statement |
| --- | --- |
| `goldbach_through_4294967296` | Every even $4\le n\le 2^{32}$ has a partition with a prime summand at most 1,861. |
| `summand_le_1789_iff_ne_1847133842` | In the same interval, a partition with a summand at most 1,789 exists exactly when $n\ne 1{,}847{,}133{,}842$. |
| `uniform_summand_bound_iff` | For $721{,}013{,}438\le N\le 2^{32}$, the optimal uniform bound for all even $4\le n\le N$ is 1,789 until $N$ reaches 1,847,133,842, then 1,861. |

Granville, van de Lune and te Riele published the two record values in Table 3 in 1989. Sinisalo and Richstein subsequently tabulated the same records. A list of successive records gives the maximum up to each endpoint. The second Lean theorem also counts the exceptions to the bound 1,789 by checking every target through $2^{32}$. Oliveira e Silva, Herzog and Pardi verified the existence of Goldbach partitions through $4\cdot10^{18}$ by computation. [1989, Table 3](https://ir.cwi.nl/pub/1570/1570D.pdf#page=7) · [1993, Table 1](https://doi.org/10.1090/S0025-5718-1993-1185250-6) · [2001, Table 1](https://doi.org/10.1090/S0025-5718-00-01290-4) · [2014 computation](https://doi.org/10.1090/S0025-5718-2013-02787-1)

## Reproduce the proof

With Git and the Lean toolchain manager `elan` on your path, run the following from the repository root. The toolchain file selects Lean 4.33.1. The manifest pins mathlib at `0df444a360eaa60ab8c11dca51a86af692955474` and records the revisions of its dependencies. [elan installation](https://github.com/leanprover/elan) · [Pinned mathlib](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474)

```sh
cd lean
lake exe cache get
lake build
lake env lean Audit.lean
```

The first Lake command fetches prebuilt mathlib artifacts. Building the local project in a clean checkout evaluates the certificate windows in the Lean kernel. The local library's compiled objects occupied about 666 MiB on the validation machine, in addition to the toolchain, third-party dependencies and other build files. The 24 extension modules account for 3,072 windows and dominate the arithmetic above $2^{30}$.

The audit prints each theorem's type and lists `propext`, `Classical.choice` and `Quot.sound` as its complete axiom dependencies. The first command below replays the declarations in the two modules that assemble the certificate. The second replays every compiled project module in its import environment and repeats the expensive kernel computations. [Audit source](Audit.lean)

```sh
lake env leanchecker -v Goldbach.ExtendedOdd.Certificate31 Goldbach.ExtendedOdd.Certificate32
lake env leanchecker -v Goldbach
```

For the release check, all 45 proof modules were compared byte for byte with the checked source tree. An isolated copy reused prebuilt artifacts for 43 of those modules and the pinned third-party dependencies. Its default `lake build` rebuilt `Certificate31`, `Certificate32` and the public `Goldbach` import from source. The audit and the targeted `leanchecker` replay both passed in that copy.

## How the certificate works

The earlier certificate covers targets through $2^{30}$. Above that endpoint, each bit in a window stands for one of 524,288 consecutive even targets. For each candidate odd summand $p\le 1{,}789$, the proof shifts a bit mask of prime complements into the positions for $n=p+q$. A surviving complement is prime because any odd composite $q\le 2^{32}$ has a prime factor at most 65,536, and the proof checks that the sieve includes every such odd prime. Taking the union over $p$ gives coverage of the whole window, with one specified bit reserved for the exception. [Earlier certificate](Goldbach/OddCertificate.lean) · [Sieve table](Goldbach/ExtendedOdd/MaskTable.lean) · [Window soundness](Goldbach/ExtendedOdd/Window.lean)

Each of the 24 extension modules covers 128 windows. The check evaluates them four at a time with `decide +kernel`. At the reserved bit, a Lucas certificate proves that 1,847,131,981 is prime. A table of proper divisors rules out $1{,}847{,}133{,}842-p$ for every prime $p<1{,}861$. [Grouping windows](Goldbach/ExtendedOdd/Coverage.lean) · [First extension module](Goldbach/ExtendedOdd/Blocks00.lean) · [The exceptional target](Goldbach/ExtendedOdd/Sharp.lean)
