# Verification record

| Item | Value |
|---|---|
| Date | 2026-10-12 |
| Verified commit | `3d40f5fe1f94b1370d3244c711d3a4df73699b2e` |
| Lean toolchain | `leanprover/lean4:v4.35.0-rc4` |
| Mathlib | `v4.35.0-rc4`, commit `1f414401f69059aa7eead47b53ee40bd38455eeb` |
| Build result | `Build completed successfully` (see [`build-log.txt`](build-log.txt)) |
| Axioms | 12 declarations, all `[propext, Classical.choice, Quot.sound]` (see [`axioms.txt`](axioms.txt)) |
| CI | [![Lean build](https://github.com/het4rk/ordowski-a224/actions/workflows/lean.yml/badge.svg)](https://github.com/het4rk/ordowski-a224/actions/workflows/lean.yml) |

## Reproduce

```bash
git clone https://github.com/het4rk/ordowski-a224
cd ordowski-a224
git checkout 3d40f5fe1f94b1370d3244c711d3a4df73699b2e
lake exe cache get
lake build
lake env lean Axioms.lean
grep -rnw sorry OrdowskiA224 --include=*.lean   # expect no output
```

## No-sorry check

`grep -rnw sorry OrdowskiA224 --include=*.lean` gave no matches (exit code 1), and the build log has no `declaration uses 'sorry'` warnings.

## SHA-256 of the Lean sources (at the verified commit)

```
0d5c0233051ae5ddaf396d626b851abe9d54b926f27ee88cbb42b30fdd17663c  ./Axioms.lean
2d8336a18813fb432c8a9402522ef336f38c1e568f4d50d4261ba6b768b70b55  ./OrdowskiA224.lean
b896ee0c0d76f69c1d984e1a3068a0a4c237a2995232be931339213f0e298d13  ./OrdowskiA224/Basic.lean
819e96c15760c5e4a49538ca7893dd0354fc6c2468ff0a614d50357ac3640d23  ./OrdowskiA224/Count.lean
035e37920759796196de50a2ab90ea9c8248ecf7b1cbf7e0921df9e4ca35d0ab  ./OrdowskiA224/Defs.lean
03caf46b6529d9d30f11a39e3adb8c866d364b964d032fb391b834d0adfca69d  ./OrdowskiA224/FiniteCheck.lean
1bc668faf48226488949da7965359a7ec477a087f78bebeb3e1eebbec1565492  ./OrdowskiA224/Main.lean
efcde0268c1e2e7dd14b899b788073b68e30acb8ae6078745e55f7c99de355fe  ./OrdowskiA224/PrimePower.lean
0608f646b36d8dc2b4db8d452b46703eb9b9483378c567c9f283dc67b48fafba  ./OrdowskiA224/PrimePowerCore.lean
ff324b200031c14d5ba70e6cb9aabd5fe595f321c24d837e79e86e1e6bc83fa3  ./OrdowskiA224/Semiprime.lean
```

Commits after the verified one change only `verification/` (and the paper PDF). The Lean sources are unchanged, as the hashes above confirm.
