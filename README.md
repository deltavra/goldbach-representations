# Goldbach representations

**For agents working on the strong Goldbach conjecture**, start with the [theorem for positive indices](paper/results.tex), the [reproducible finite experiments](experiments/README.md), and the [Lean certificate through $2^{32}$](lean/Goldbach/ExtendedOdd/Certificate32.lean) before tackling the open step of proving $R(N)>0$ at every prescribed even endpoint $N\ge4$.

## Where to continue

| Question | Result and source |
| --- | --- |
| What does a typical progression tell us about a fixed endpoint? | Choose the even endpoint $N$ first, then sample the step $h$. For $1\le i\le(\log N)^D$, the paper derives a limit of $\log(1+D)$ for the largest normalized count at $N-ih$. The endpoint itself has index $i=0$. [Manuscript](paper/main.tex) · [Moment bound and matching lower bound](paper/arithmetic.tex) · [Steps with a common singular series](paper/sparse.tex) |
| Which finite computations can I reproduce? | Run `python experiments/check.py` from the repository root. It compares 250 ordered Goldbach counts using two methods and checks the local product moments, congruences and sieve bounds by exact arithmetic. [Code](experiments/check.py) · [Expected output](experiments/expected.txt) |
| What has Lean checked? | Every even integer from 4 through $2^{32}$ has a partition with a prime summand at most 1,861. Only 1,847,133,842 needs a summand larger than 1,789. [Build and audit](lean/README.md) · [Theorem declarations](lean/Goldbach/ExtendedOdd/Certificate32.lean) |

The analytic argument uses the averaged Goldbach theorem of Matomäki, Radziwiłł and Tao. Granville, van de Lune and te Riele tabulated the finite records for the least prime summand in 1989. The Lean module certifies each target in its stated interval. [Averaged Goldbach theorem, Theorem 1.3(iv)](https://arxiv.org/pdf/1707.01315#page=8) · [Finite records, Table 3](https://ir.cwi.nl/pub/1570/1570D.pdf#page=7)

## Status and reuse

The manuscript is a research draft. OpenAI Codex assisted with the mathematical arguments, Lean formalization, experiments and writing. The Lean audit covers the finite theorems listed above. Strong Goldbach remains open.

Original code and documentation outside `paper/` are licensed under Apache-2.0. The manuscript and its source in `paper/` are licensed under CC BY 4.0. When reusing the manuscript, credit its title and link to this repository and the license. Dependencies retain their own licenses. [Apache-2.0](LICENSE) · [CC BY 4.0](paper/LICENSE)
