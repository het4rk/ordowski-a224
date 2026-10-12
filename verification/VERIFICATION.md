# Verification record

| Item | Value |
|---|---|
| Date | 2026-10-12 |
| Verified commit | `abb86ea60694ae6a24cb618382cc69480af54470` |
| Lean toolchain | `leanprover/lean4:v4.35.0-rc4` |
| Mathlib | `v4.35.0-rc4`, commit `1f414401f69059aa7eead47b53ee40bd38455eeb` |
| Main theorem | `OeisA224.conjecture_main_ppq` (even, `p^k`, `p^a q^b`, `pqr`) |
| Build result | `Build completed successfully` (see [`build-log.txt`](build-log.txt)) |
| Axioms | 18 declarations, all within `[propext, Classical.choice, Quot.sound]` (`finCheck3_true` uses only `propext`) (see [`axioms.txt`](axioms.txt)) |
| CI | run [38281817447](https://github.com/het4rk/ordowski-a224/actions/runs/38281817447) on `abb86ea` passed; [![Lean build](https://github.com/het4rk/ordowski-a224/actions/workflows/lean.yml/badge.svg)](https://github.com/het4rk/ordowski-a224/actions/workflows/lean.yml) |

## Reproduce

```bash
git clone https://github.com/het4rk/ordowski-a224
cd ordowski-a224
git checkout abb86ea60694ae6a24cb618382cc69480af54470
lake exe cache get
lake build        # on machines with < 16 GB RAM, build the finite checks one module at a time, in CI order
lake env lean Axioms.lean
grep -rnw sorry OrdowskiA224 --include=*.lean   # expect no output
```

## How the local build was run

Fresh clone of `main`, `LEAN_NUM_THREADS=2`, each heavy module built with its own `lake build <module>` call in the order used by CI, then a final `lake build`. The machine was shared with another Lean job, so a module that was killed for lack of memory (exit code 137; it happened twice, on `FiniteCheck` and `FCPQ.P11`) was retried. Each retry then built cleanly. These retries show up in `build-log.txt`. The final `lake build` and `lake env lean Axioms.lean` completed successfully.

## No-sorry check

`grep -rnw sorry OrdowskiA224 --include=*.lean` gave no matches, the build log has no `declaration uses 'sorry'` warnings, and no source uses `native_decide` (the finite checks use `decide +kernel`).

## SHA-256 of the Lean sources (at the verified commit)

```
8454b372d2285d62d7b9f467f2b8a84bfb1c2626f8869faef07f00746e85b30e  ./Axioms.lean
8d4be2d2efd7d0c6f08d1e6ac21cd0618c9a673fb2bd9f54aefc95a3cfabe4a3  ./OrdowskiA224.lean
b896ee0c0d76f69c1d984e1a3068a0a4c237a2995232be931339213f0e298d13  ./OrdowskiA224/Basic.lean
819e96c15760c5e4a49538ca7893dd0354fc6c2468ff0a614d50357ac3640d23  ./OrdowskiA224/Count.lean
035e37920759796196de50a2ab90ea9c8248ecf7b1cbf7e0921df9e4ca35d0ab  ./OrdowskiA224/Defs.lean
2907ab49c1b3e95c05433be6a5710c705b16e09d4d29f430e7553c1c21315433  ./OrdowskiA224/FCPQ/P11.lean
9dbc0dea0a6ec0d5d94385ace0221b31a5df267f519185750450ab10d7afd8e9  ./OrdowskiA224/FCPQ/P13.lean
1a64f6f125f9f343f640d9038f262a999cf07c43fed41284e528e9634a47e016  ./OrdowskiA224/FCPQ/P17.lean
93a00d7dc377398b05d090c97f0af7fbca8420a0640711300bd0b9fb64b0710f  ./OrdowskiA224/FCPQ/P19.lean
40cb9c0d95e8f47bd79197e4d234000cab16e4cccfd2d09e50e8aac109270d53  ./OrdowskiA224/FCPQ/P23.lean
e391a43b4d8572c94b8ef9ab90c7f0c565d1e96afa77f457dcb24a1782d1c10f  ./OrdowskiA224/FCPQ/P29.lean
839d629368a87cf9680105985a665c6e56069db2c8a0f54d3cde37e2e541356b  ./OrdowskiA224/FCPQ/P3.lean
184e43d40243c3c9c0403a6e8b73b5cf5cdf833cb873cacbb77ffd0a9f086ff9  ./OrdowskiA224/FCPQ/P31.lean
c2c63c8725a67e2625b3cf765615d72aeba6b78d901bf706143cb7c3c9a24cd9  ./OrdowskiA224/FCPQ/P37.lean
8ee34a402af9ad874083439050f42bc196943368b1a053e763e9592c22e0c5f2  ./OrdowskiA224/FCPQ/P41.lean
bf1df13130f956ffabfcfcc1e9f36febb1d0de9c15248c5f3d4f2cea5edc88be  ./OrdowskiA224/FCPQ/P43.lean
29e911ff2fcecbed4b20b03df48205e4432fdfbada1ebdb64e2d997e8ba2c58a  ./OrdowskiA224/FCPQ/P47.lean
88de962a4c5e9e1825a4e6f56eed49c84df89f6999aff3baf6160a65253ee50a  ./OrdowskiA224/FCPQ/P5.lean
41c0076d5dcd618ddd2084a4481953b4ae50595561e152f84c19dffe2ecb4672  ./OrdowskiA224/FCPQ/P53.lean
00d1d3912c3c3d5fb29f773780122c6d7d25719ffbaebfbcfb9055582e7c7652  ./OrdowskiA224/FCPQ/P59.lean
581bd2e104babba308f75f66fe813ca6062dd5552e7e122c73190053c1a7ddbf  ./OrdowskiA224/FCPQ/P5Q23_b0.lean
a6f69397d389fbee4359fc350cf3de436ccf0fce9552e1029230563594911923  ./OrdowskiA224/FCPQ/P5Q23_b1.lean
e9fa7d5b39703d7c423c665089dfccf66431388b79c077e4b77478aa291e29b2  ./OrdowskiA224/FCPQ/P5Q23_b2.lean
6a42a97002a4c4e4c51d96a40ad6a250a8f2477f585edb641fb1d025d49f225f  ./OrdowskiA224/FCPQ/P5Q23_b3.lean
c259b23e8c2ff286cfaa8b183aab3099b0327ca843b70ceea845c06e5598a7df  ./OrdowskiA224/FCPQ/P5Q23_b4.lean
ff93484a2f09d0144f1f88b3eda6647e1655d2c464d0143d7c2ead7336e0be34  ./OrdowskiA224/FCPQ/P5Q23_b5.lean
fde83e99556a8f4f56ec6feece8d01d5968d0630104fb5d1b5c53eec31aff604  ./OrdowskiA224/FCPQ/P5Q23_b6.lean
191c4c196c8c95e4308616d2bda77d7d35bc7bde2b24d84e7744171428f532a6  ./OrdowskiA224/FCPQ/P5Q23_b7.lean
380531535b08bd996e98ab99d62084cc1c3d949eff02d6b27c5525d850a88900  ./OrdowskiA224/FCPQ/P5Q23_s1.lean
1c01476bc26452fa2caea7300254a640867dacad8eb78db23b50ed137d8a4ad1  ./OrdowskiA224/FCPQ/P5Q23_s2.lean
f79052dcecf38e1391a4b0f32c60d4ba6a6b39a40150694b5158b73904f8dfbb  ./OrdowskiA224/FCPQ/P5Q23_s3.lean
8c9f1af3ea7ca17ff78793543e2a83c95bd2bb1c7e0a0e43581eed5491c2553a  ./OrdowskiA224/FCPQ/P5Q23_s4.lean
2ea21aedb20460c9deae3d6550961b2426448ddb27e682d753222f38c604e31b  ./OrdowskiA224/FCPQ/P5Q23_s5.lean
e40a6fbe876535a1acb635af65115b525e88830457b31b53418c1c39f99a8535  ./OrdowskiA224/FCPQ/P5_0.lean
370635cf1690b1f06b0743b6ca51c73b7aabe13ff4a3e8f224cdbf649b9ddc50  ./OrdowskiA224/FCPQ/P5_1.lean
3577db28101c692c9565ab8db0e1367a15222e04a46738cde193484ec1439f4d  ./OrdowskiA224/FCPQ/P5_2.lean
46a1963f25292e3c11348166f9da2c30a2ca9e9e95f2beaea2ed0297793090e0  ./OrdowskiA224/FCPQ/P5_3.lean
a2ecca75bc7aec8b4ad43f36b16d03c7852711612e8f13ccddcbe065f76808ef  ./OrdowskiA224/FCPQ/P5_Q21.lean
925a583b87718acccb761bd08a71c3c79e860b1b2a3963067cfa62091c57dd31  ./OrdowskiA224/FCPQ/P5_Q22.lean
0ae8239c175f45f03f5e5e60a68dd0537b115c9874e542801105bce9fb45045c  ./OrdowskiA224/FCPQ/P5_Q23.lean
afbc3ea668e5bbb4b1e962e699bbb892ed2bb9beb06881db10021747654cf367  ./OrdowskiA224/FCPQ/P5_Q24.lean
81a09802e7b2bf54e07336edc5ab5a8c6dfedf83cc97f1ec6bbf309e84e357db  ./OrdowskiA224/FCPQ/P5_Q25.lean
a42ccb7647bad7bee914e529d3a51abcc57738afd18074a29809a6cc7254dca5  ./OrdowskiA224/FCPQ/P5_Q26.lean
94439babd834adb10371ea00dd6953154acc43c4b29a28eecb50473308a96fb1  ./OrdowskiA224/FCPQ/P5_Q27.lean
0839ed82ffe033fade63e72a945b6bcb8ff71902da362e2da96bb0199ec4128c  ./OrdowskiA224/FCPQ/P5_Q28.lean
d8114a693dc68a6369994174b40a77928edd8ee8f63d5ec1832f1584f3f1e5d4  ./OrdowskiA224/FCPQ/P5_Q29.lean
26f710512dd2493d10a1cc4ea3810bd66182286dac38159a5bda8c204320d847  ./OrdowskiA224/FCPQ/P5_Q30.lean
f72a2f005bec01dabadf7c5c1e760d34176e404c4053148ef58315d3122bc44b  ./OrdowskiA224/FCPQ/P61.lean
613d578c3f1ca19fc36daf5785f7855592805b056e7f5fe3ce0cbf22900af530  ./OrdowskiA224/FCPQ/P67.lean
bb1619e5637955a710f744128c402baec92de3f3bf1a300b26a099a9101fc014  ./OrdowskiA224/FCPQ/P7.lean
03caf46b6529d9d30f11a39e3adb8c866d364b964d032fb391b834d0adfca69d  ./OrdowskiA224/FiniteCheck.lean
d1d04b1da4ddb46573d43ea60c8903c2153de1e555a63161910ed8c2eec0d60b  ./OrdowskiA224/FiniteCheck3.lean
bccc9cf95234bbbe485252d57ac03842fc13737b9ecfa357bcc8060528e3efae  ./OrdowskiA224/FiniteCheckPQ.lean
907dfe6b037479823a89ba8751db9cfd48076a9d7ef076195f094205b2c62293  ./OrdowskiA224/FiniteCheckPQ2.lean
58136fdb4fd893acbe4e415b2ce6bc54e000da566681817b2777d3ce9e680e8c  ./OrdowskiA224/FiniteCheckPQAll.lean
1bc668faf48226488949da7965359a7ec477a087f78bebeb3e1eebbec1565492  ./OrdowskiA224/Main.lean
90a2d21f2b464889c4a636931be6dcc6a56282aa5f59a4bd7ec9ee96ded2f635  ./OrdowskiA224/MainThree.lean
efcde0268c1e2e7dd14b899b788073b68e30acb8ae6078745e55f7c99de355fe  ./OrdowskiA224/PrimePower.lean
0608f646b36d8dc2b4db8d452b46703eb9b9483378c567c9f283dc67b48fafba  ./OrdowskiA224/PrimePowerCore.lean
ff324b200031c14d5ba70e6cb9aabd5fe595f321c24d837e79e86e1e6bc83fa3  ./OrdowskiA224/Semiprime.lean
a1c841c3bb3599d73318bf1a5471fc101cf5a4a74d56e925e61b97f887139cc2  ./OrdowskiA224/ThreePrimes.lean
de07c49422d5dba6d166bc722437c066cf69968e39ec94b508a51146b7d95951  ./OrdowskiA224/TwoPrimePowers.lean
018c26cf96c5d2d5e361d9698af951c336266cc0c46a6312b97e3417ab74140b  ./OrdowskiA224/TwoPrimePowersGlue.lean
7056adc308888c7ddb5865a6ce2847487836d9da20989f26c75fcd8135e11831  ./OrdowskiA224/TwoPrimePowersMain.lean
```

Commits after the verified one change only documentation, `verification/` and the paper. The Lean sources are unchanged, as the hashes above confirm.
