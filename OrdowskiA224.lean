import OrdowskiA224.Defs
import OrdowskiA224.Count
import OrdowskiA224.Basic
import OrdowskiA224.PrimePowerCore
import OrdowskiA224.FiniteCheck
import OrdowskiA224.Semiprime
import OrdowskiA224.PrimePower
import OrdowskiA224.Main
import OrdowskiA224.FiniteCheck3
import OrdowskiA224.ThreePrimes
import OrdowskiA224.MainThree
import OrdowskiA224.TwoPrimePowers
import OrdowskiA224.FiniteCheckPQ
import OrdowskiA224.FiniteCheckPQ2
import OrdowskiA224.FiniteCheckPQAll
import OrdowskiA224.TwoPrimePowersGlue
import OrdowskiA224.TwoPrimePowersMain

/-!
# Partial results on Ordowski's conjecture (OEIS A000224)

Root module. The full conjecture remains open; `OeisA224.conjecture_main` proves it for
even `n`, prime powers, and products of two distinct odd primes; `OeisA224.conjecture_main_three` adds products of three
distinct odd primes; `OeisA224.conjecture_main_ppq` adds every `n = p^a q^b` (two distinct odd
primes, any exponents).
Author: Hetark Shah, AI-assisted by Grok.
-/
