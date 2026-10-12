import Mathlib

/-!
# Finite verification for the case `n = p q r` (kernel-checked, `decide +kernel`)

For each odd prime `p ≤ 400`, each `1 ≤ Q ≤ 63` with `d := 64 p² - Q (p+1)² > 0`, and each
odd `q` with `p < q ≤ 6 Q (p+1)² / d + 8`, we check that the quadratic
`c₂ r² = c₁ r + c₀` (see `ThreePrimes.lean`) has no natural root `r > q`.  A candidate integer
square root of the discriminant is produced by Newton's method, and the check itself verifies
`c² ≤ D < (c+1)²`, so the correctness of Newton's method is never needed.
-/

namespace OeisA224

def ps3_0 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]
def ps3_1 : List ℕ := [43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89]
def ps3_2 : List ℕ := [97, 101, 103, 107, 109, 113, 127]
def ps3_3 : List ℕ := [131]
def ps3_4 : List ℕ := [137]
def ps3_5 : List ℕ := [139]
def ps3_6 : List ℕ := [149, 151, 157, 163, 167, 173]
def ps3_7 : List ℕ := [179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233]
def ps3_8 : List ℕ := [239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313]
def ps3_9 : List ℕ := [317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397]
def primesTo400 : List ℕ := ps3_0 ++ ps3_1 ++ ps3_2 ++ ps3_3 ++ ps3_4 ++ ps3_5 ++ ps3_6 ++ ps3_7 ++ ps3_8 ++ ps3_9

/-- Newton iteration for the integer square root, with fuel. Only used to propose a candidate. -/
def nsqrt : ℕ → ℕ → ℕ → ℕ
  | 0, _, x => x
  | f+1, D, x => let y := (x + D / x) / 2; if y < x then nsqrt f D y else x

/-- coefficients of the quadratic in `r`. -/
def c2 (p Q q : ℕ) : ℕ := 64*(p*q)^2 - Q*((p+1)*(q+1))^2
def c1 (p Q q : ℕ) : ℕ := 2*Q*((p+1)*(q+1))^2 - 8*Q*((p+1)*(q+1))
def c0 (p Q q : ℕ) : ℕ := Q*((p+1)*(q+1))^2 - 8*Q*((p+1)*(q+1)) + 64

/-- `true` means: the equation `a r² = b r + e` has no natural solution `r > q`
(when `a > 0`, `e > 0`); see `rootFree_spec`. -/
def rootFree (q a b e : ℕ) : Bool :=
  let D := b*b + 4*a*e
  let c := nsqrt 200 D (b + 2*a*e/(b+1) + 1)
  a == 0 || (c*c ≤ D && D < (c+1)*(c+1) && (c*c != D || (b + c) % (2*a) != 0 || (b+c)/(2*a) ≤ q))

def okTriple (p Q q : ℕ) : Bool :=
  q ≤ p || rootFree q (c2 p Q q) (c1 p Q q) (c0 p Q q)

def qmax (p Q : ℕ) : ℕ := 6*Q*(p+1)^2 / (64*p^2 - Q*(p+1)^2) + 8

def okPQ (p Q : ℕ) : Bool :=
  Q*(p+1)^2 ≥ 64*p^2 || (List.range (qmax p Q + 1)).all fun q => okTriple p Q q

def finCheck3 (ps : List ℕ) : Bool := ps.all fun p => (List.range 64).all fun Q => okPQ p Q

theorem finCheck3_0 : finCheck3 ps3_0 = true := by decide +kernel
theorem finCheck3_1 : finCheck3 ps3_1 = true := by decide +kernel
theorem finCheck3_2 : finCheck3 ps3_2 = true := by decide +kernel
theorem finCheck3_3 : finCheck3 ps3_3 = true := by decide +kernel
theorem finCheck3_4 : finCheck3 ps3_4 = true := by decide +kernel
theorem finCheck3_5 : finCheck3 ps3_5 = true := by decide +kernel
theorem finCheck3_6 : finCheck3 ps3_6 = true := by decide +kernel
theorem finCheck3_7 : finCheck3 ps3_7 = true := by decide +kernel
theorem finCheck3_8 : finCheck3 ps3_8 = true := by decide +kernel
theorem finCheck3_9 : finCheck3 ps3_9 = true := by decide +kernel

theorem finCheck3_true : finCheck3 primesTo400 = true := by
  simp only [primesTo400, finCheck3, List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨finCheck3_0, finCheck3_1⟩, finCheck3_2⟩, finCheck3_3⟩, finCheck3_4⟩, finCheck3_5⟩, finCheck3_6⟩, finCheck3_7⟩, finCheck3_8⟩, finCheck3_9⟩

end OeisA224
