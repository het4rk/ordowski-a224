# Ordowski's conjecture on squares modulo n (OEIS A000224): even numbers, prime powers and semiprimes

[![Lean build](https://github.com/het4rk/ordowski-a224/actions/workflows/lean.yml/badge.svg)](https://github.com/het4rk/ordowski-a224/actions/workflows/lean.yml)

**Author:** Hetark Shah, AI-assisted by Grok  
**Date:** October 12, 2026

## Result

Let `a(n)` be the number of squares modulo `n` ([A000224](https://oeis.org/A000224)). T. Ordowski (2025) conjectured that for `n > 1`, `n` is an odd prime ⟺ `n² ≡ 1 (mod a(n)(a(n)−1))`. The conjecture is listed as `research open` in [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (`FormalConjectures/OEIS/224.lean`). We prove it for all even `n`, all prime powers and all products of two distinct odd primes, stated against the exact upstream definition of `a`.

## Status

**Partial result. The full conjecture remains open.** Proved: every `n > 1` that is even, a prime power `p^k` (k ≥ 1), or a product of two distinct odd primes. Open: squarefree `n` with ≥ 3 prime factors, and odd composites such as `p²q`.

## Theorems and Lean names

| Lean name | Statement |
|---|---|
| `conjecture_main` | the conjecture for `n` even, `p^k`, or `pq` (exact upstream conclusion) |
| `even_case` | even `n` never satisfy the congruence |
| `prime_direction` | odd prime ⇒ congruence |
| `a_eq_aZ`, `aZ_mul`, `aZ_prime` | reduction to `ZMod n`, CRT multiplicativity, `a p = (p+1)/2` |
| `stangl` | Stangl's closed form for `a (p^k)` |
| `prime_power_case` | odd prime powers `p^k`, `k ≥ 2` |
| `semiprime_case` | `n = pq`, distinct odd primes (finite check by `decide +kernel`) |

No `sorry`, no `native_decide`, no extra hypotheses.

## Build

Toolchain `leanprover/lean4:v4.35.0-rc4`; Mathlib `v4.35.0-rc4` (commit `1f414401f69059aa7eead47b53ee40bd38455eeb`, pinned in `lake-manifest.json`).

```bash
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Axioms output

```
'OeisA224.conjecture_main' depends on axioms: [propext, Classical.choice, Quot.sound]
'OeisA224.stangl' depends on axioms: [propext, Classical.choice, Quot.sound]
'OeisA224.prime_power_case' depends on axioms: [propext, Classical.choice, Quot.sound]
'OeisA224.conjecture_of_even_or_prime_or_semiprime' depends on axioms: [propext, Classical.choice, Quot.sound]
'OeisA224.semiprime_case' depends on axioms: [propext, Classical.choice, Quot.sound]
'OeisA224.even_case' depends on axioms: [propext, Classical.choice, Quot.sound]
'OeisA224.prime_direction' depends on axioms: [propext, Classical.choice, Quot.sound]
'OeisA224.a_eq_aZ' depends on axioms: [propext, Classical.choice, Quot.sound]
'OeisA224.aZ_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'OeisA224.aZ_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'OeisA224.pp_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'OeisA224.pp_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Machine-check attestation

- [`verification/`](verification/) holds `build-log.txt` (fresh-clone build), `axioms.txt`, and [`VERIFICATION.md`](verification/VERIFICATION.md) with the commit SHA, toolchain, Mathlib commit, reproduce commands, the no-sorry grep result and SHA-256 hashes of the Lean sources.
- [CI](https://github.com/het4rk/ordowski-a224/actions/workflows/lean.yml) does a clean build on every push, fails on any `sorry`, and checks an axiom whitelist (`scripts/check_axioms.sh`). It uploads the build log and axiom report as the `lean-attestation` artifact and shows them in the job summary.

## Paper

[`paper/paper.tex`](paper/paper.tex) and [`paper/paper.pdf`](paper/paper.pdf).

## Exact match with upstream definitions

Upstream: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at commit `34ee0e3c5fd52d202d62a71094a37970cb5fb870` (main, Oct 12 2026), `FormalConjectures/OEIS/224.lean`:
```lean
def a (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    Finset.card ((Finset.range n).image (fun k : ℕ => k ^ 2 % n))

theorem conjecture (n : ℕ) (hn : 1 < n) :
    (n.Prime ∧ n ≠ 2) ↔ n ^ 2 ≡ 1 [MOD a n * (a n - 1)] := by
  sorry
```
`OeisA224.a` in `OrdowskiA224/Defs.lean` has exactly this body, and `OeisA224.conjecture_main` concludes exactly `(n.Prime ∧ n ≠ 2) ↔ n ^ 2 ≡ 1 [MOD a n * (a n - 1)]` under its case hypothesis.

## Citation

See [`CITATION.cff`](CITATION.cff):

> Hetark Shah (AI-assisted by Grok), *Ordowski's conjecture on squares modulo n (OEIS A000224): even numbers, prime powers and semiprimes*, 2026. https://github.com/het4rk/ordowski-a224

## License

Apache-2.0 (the same as Mathlib). See [`LICENSE`](LICENSE).
