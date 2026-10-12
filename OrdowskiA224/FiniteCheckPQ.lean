import OrdowskiA224.FiniteCheck3

/-!
# Finite verification for `n = p^a q^b` (kernel-checked, `decide +kernel`)

See `TwoPrimePowers.lean` for the reduction. All loops are bounded; root tests reuse the
Newton-candidate-plus-bracket technique of `FiniteCheck3.lean`.
-/

namespace OeisA224

/-- `true` means: `a r² = b r + e` has no natural solution `r` with `r ≥ lo` and `d ∣ r`
(when `a, e > 0`); see `rootFreeDiv_spec`. -/
def rootFreeDiv (lo d a b e : ℕ) : Bool :=
  let D := b*b + 4*a*e
  let c := nsqrt 200 D (b + 2*a*e/(b+1) + 1)
  a == 0 || (c*c ≤ D && D < (c+1)*(c+1) &&
    (c*c != D || (b + c) % (2*a) != 0 || (b+c)/(2*a) < lo || (b+c)/(2*a) % d != 0))

/-- Iterate `f a X` over `X = X₀, X₀ p, X₀ p², …` while `X ≤ B` (with fuel). -/
def allPow (p B : ℕ) (f : ℕ → ℕ → Bool) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | n+1, a, X => if B < X then true else f a X && allPow p B f n (a+1) (X*p)

def cpar (p a : ℕ) : ℕ := if a % 2 = 0 then p + 2 else 2*p + 1

/-- no `Y ≥ q`, `q ∣ Y` solves the quadratic in `Y` (for either value of `e`). -/
def solveY (p X c q Q : ℕ) : Bool :=
  let U := p*X + c
  let M := 4*(p+1)*(q+1)
  let DX := M*M*(X*X) - Q*(q*q)*(U*U)
  M*M*(X*X) ≤ Q*(q*q)*(U*U) ||
  (rootFreeDiv q q DX (Q*q*U*(2*(q+2)*U - M)) (Q*(q+2)*U*((q+2)*U - M) + M*M) &&
   rootFreeDiv q q DX (Q*q*U*(2*(2*q+1)*U - M)) (Q*(2*q+1)*U*((2*q+1)*U - M) + M*M))

/-- no `X ≥ p`, `p ∣ X` solves the quadratic in `X` (for either value of `c`). -/
def solveX (p q Y e Q : ℕ) : Bool :=
  let V := q*Y + e
  let M := 4*(p+1)*(q+1)
  let DY := M*M*(Y*Y) - Q*(p*p)*(V*V)
  M*M*(Y*Y) ≤ Q*(p*p)*(V*V) ||
  (rootFreeDiv p p DY (Q*p*V*(2*(p+2)*V - M)) (Q*(p+2)*V*((p+2)*V - M) + M*M) &&
   rootFreeDiv p p DY (Q*p*V*(2*(2*p+1)*V - M)) (Q*(2*p+1)*V*((2*p+1)*V - M) + M*M))

def smallCheck (p Q a : ℕ) : Bool :=
  let X := p^a
  let c := cpar p a
  let U := p*X + c
  let A := 16*(p+1)^2*(X*X)
  let B := Q*(U*U)
  A != B &&
  (let qB := if A < B then 48*(p+1)^2*(X*X) / (B - A) else 13*Q*(U*U) / (A - B)
   (List.range (qB+1)).all fun q => q ≤ p || q % 2 == 0 || solveY p X c q Q)

def bigX (p Q X : ℕ) : Bool :=
  Q*(p*p) < 16*(p+1)^2 &&
  2*Q*(2*p+1)*(2*p*X + 2*p + 1) ≤ (16*(p+1)^2 - Q*(p*p))*(X*X)

def triple (p Q q : ℕ) : Bool :=
  let M := 4*(p+1)*(q+1)
  M*M ≤ Q*(p*p)*(q*q) ||
  (let B := (45*Q*(p*p)*(q*q) + M*M) / (M*M - Q*(p*p)*(q*q))
   allPow p B (fun a X => solveY p X (cpar p a) q Q) 200 1 p &&
   allPow q B (fun b Y => solveX p q Y (cpar q b) Q) 200 1 q)

def bigBranch (p Q qU : ℕ) : Bool :=
  (List.range (qU+1)).all fun q => q ≤ p || q % 2 == 0 || triple p Q q

def qUpos (p Q : ℕ) : ℕ := 26*Q*(p+1)^4 / ((p*p)*(16*(p+1)^2 - Q*(p*p)))
def qUneg (p Q : ℕ) : ℕ := 48*(p+1)^2 / (Q*(p*p) - 16*(p+1)^2)

def okPQ2 (p Q : ℕ) : Bool :=
  Q % p == 0 || (Q*(p*p) != 16*(p+1)^2 &&
  (if Q*(p*p) < 16*(p+1)^2 then
     allPow p 2000000 (fun a X => bigX p Q X || smallCheck p Q a) 200 1 p &&
     bigBranch p Q (qUpos p Q)
   else bigBranch p Q (qUneg p Q)))

def okP2 (p : ℕ) : Bool := (List.range 41).all fun Q => Q == 0 || okPQ2 p Q

def primesTo67 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67]

end OeisA224
