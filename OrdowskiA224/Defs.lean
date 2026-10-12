import Mathlib

/-!
# The sequence A000224

`OeisA224.a n` is the number of squares modulo `n`. This is *verbatim* the definition used in
`google-deepmind/formal-conjectures`, file `FormalConjectures/OEIS/224.lean`.
-/

namespace OeisA224

/-- The number of squares modulo $n$ (verbatim from formal-conjectures). -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    Finset.card ((Finset.range n).image (fun k : ℕ => k ^ 2 % n))

end OeisA224
