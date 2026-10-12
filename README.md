# Ordowski's conjecture on squares modulo n (OEIS A000224): prime powers and semiprimes in Lean 4

Let `a(n)` be the number of squares modulo `n` ([A000224](https://oeis.org/A000224)).
**Conjecture (T. Ordowski).** For `n > 1`, `n` is an odd prime ⟺ `n² ≡ 1 (mod a(n)(a(n)-1))`.
The conjecture is listed as open in
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/OEIS/224.lean`).

## What is proved, unconditionally and machine-checked

`OeisA224.conjecture_main` (in `OrdowskiA224/Main.lean`): the conjecture holds for every
`n > 1` that is **even**, a **prime power** `p^k` (k ≥ 1), or **a product of two distinct odd
primes**. It is stated with the exact definition of `a` and the exact form of
`OeisA224.conjecture` from formal-conjectures.

- No `sorry`, no `native_decide`, and no extra hypotheses. The finite check uses `decide +kernel`.
- `#print axioms` gives only `propext, Classical.choice, Quot.sound` (see `axioms.txt`).
- The supporting lemmas are fully proved:
  - `a_eq_aZ`: reduction to `ZMod n`
  - `aZ_mul`: CRT multiplicativity
  - `aZ_prime`: `a p = (p+1)/2`
  - `stangl`: Stangl's closed form for `a (p^k)`
  - `prime_power_case`, `semiprime_case` and `even_case`

## Still open

Squarefree `n` with three or more prime factors, and general odd composites (for example
`p^2 q`). The paper explains why the semiprime method does not directly extend.

## Build

```
lake exe cache get
lake build
lake env lean Axioms.lean
```
Toolchain: `leanprover/lean4:v4.35.0-rc4`, Mathlib `v4.35.0-rc4`. `FiniteCheck.lean` takes
about 2 minutes and a few GB of RAM.

## Layout
- `OrdowskiA224/`: Lean sources (Defs, Count, Basic, PrimePowerCore, PrimePower, FiniteCheck, Semiprime, Main)
- `Axioms.lean`: axiom report
- `paper/`: LaTeX paper (`paper.tex`, `paper.pdf`)
- `scripts/`: independent Python/C cross-checks (brute force up to 10^8)
