# Verification record

| Item | Value |
|---|---|
| Date | 2026-10-12 |
| Verified commit | `13cfedcbb36f4b5472bf1f8b5d12e5c1fd6797d4` |
| Lean toolchain | `leanprover/lean4:v4.35.0-rc4` |
| Mathlib | `v4.35.0-rc4`, commit `1f414401f69059aa7eead47b53ee40bd38455eeb` |
| Main theorem | `OeisA224.conjecture_main_three` (even, `p^k`, `pq`, `pqr`) |
| Build result | `Build completed successfully` (see [`build-log.txt`](build-log.txt)) |
| Axioms | 15 declarations, all within `[propext, Classical.choice, Quot.sound]` (`finCheck3_true` uses only `propext`) (see [`axioms.txt`](axioms.txt)) |
| CI | [![Lean build](https://github.com/het4rk/ordowski-a224/actions/workflows/lean.yml/badge.svg)](https://github.com/het4rk/ordowski-a224/actions/workflows/lean.yml) |

## Reproduce

```bash
git clone https://github.com/het4rk/ordowski-a224
cd ordowski-a224
git checkout 13cfedcbb36f4b5472bf1f8b5d12e5c1fd6797d4
lake exe cache get
lake build
lake env lean Axioms.lean
grep -rnw sorry OrdowskiA224 --include=*.lean   # expect no output
```

## No-sorry check

`grep -rnw sorry OrdowskiA224 --include=*.lean` gave no matches (exit code 1), and the build log has no `declaration uses 'sorry'` warnings.

## SHA-256 of the Lean sources (at the verified commit)

```
c42b3c49bc48897d71bca8380f296ff9ffd2f7cb172ab7600431f5820efd78d9  ./Axioms.lean
2765a2d37dac5478a4f7ec072c24b6a2e629d67edef0bf8297a3a985498ddb64  ./OrdowskiA224.lean
b896ee0c0d76f69c1d984e1a3068a0a4c237a2995232be931339213f0e298d13  ./OrdowskiA224/Basic.lean
819e96c15760c5e4a49538ca7893dd0354fc6c2468ff0a614d50357ac3640d23  ./OrdowskiA224/Count.lean
035e37920759796196de50a2ab90ea9c8248ecf7b1cbf7e0921df9e4ca35d0ab  ./OrdowskiA224/Defs.lean
03caf46b6529d9d30f11a39e3adb8c866d364b964d032fb391b834d0adfca69d  ./OrdowskiA224/FiniteCheck.lean
d1d04b1da4ddb46573d43ea60c8903c2153de1e555a63161910ed8c2eec0d60b  ./OrdowskiA224/FiniteCheck3.lean
1bc668faf48226488949da7965359a7ec477a087f78bebeb3e1eebbec1565492  ./OrdowskiA224/Main.lean
90a2d21f2b464889c4a636931be6dcc6a56282aa5f59a4bd7ec9ee96ded2f635  ./OrdowskiA224/MainThree.lean
efcde0268c1e2e7dd14b899b788073b68e30acb8ae6078745e55f7c99de355fe  ./OrdowskiA224/PrimePower.lean
0608f646b36d8dc2b4db8d452b46703eb9b9483378c567c9f283dc67b48fafba  ./OrdowskiA224/PrimePowerCore.lean
ff324b200031c14d5ba70e6cb9aabd5fe595f321c24d837e79e86e1e6bc83fa3  ./OrdowskiA224/Semiprime.lean
a1c841c3bb3599d73318bf1a5471fc101cf5a4a74d56e925e61b97f887139cc2  ./OrdowskiA224/ThreePrimes.lean
```

Commits after the verified one change only `verification/` (and the paper PDF). The Lean sources are unchanged, as the hashes above confirm.
