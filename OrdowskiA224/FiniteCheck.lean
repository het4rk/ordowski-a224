import Mathlib

/-!
# The finite verification, checked by the Lean kernel (`decide +kernel`, no `native_decide`)
-/

def primesTo61 : List ℕ := [3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61]
def okPair (p d : ℕ) : Bool :=
  let q := d - 1
  let s := (p+1)*(q+1)/4
  !(16*(p^2-1) % d == 0 && p < q && q % 2 == 1) || ((p*q)^2 - 1) % (s*(s-1)) != 0
def finCheck : Bool := primesTo61.all fun p => (List.range (16*(p^2-1)+1)).all fun d => okPair p d
theorem finCheck_true : finCheck = true := by decide +kernel




theorem mem_primesTo61 (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ p) (h61 : p ≤ 61) : p ∈ primesTo61 := by
  interval_cases p <;> first | (simp [primesTo61]; done) | (norm_num at hp)

theorem okPair_spec (p d : ℕ) (h : okPair p d = true) (h1 : 16*(p^2-1) % d = 0) (h2 : p < d - 1)
    (h3 : (d-1) % 2 = 1) : ((p*(d-1))^2 - 1) % (((p+1)*(d-1+1)/4)*((p+1)*(d-1+1)/4-1)) ≠ 0 := by
  unfold okPair at h
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne,
    bne_iff_ne, ne_eq] at h
  rcases h with ((h | h) | h) | h
  all_goals first | exact absurd h1 (by simpa using h) | (simp at h; omega) | exact h

theorem finCheck_spec (p : ℕ) (hp : p ∈ primesTo61) (d : ℕ) (hd : d < 16*(p^2-1)+1) :
    okPair p d = true := by
  have hc := finCheck_true
  unfold finCheck at hc
  rw [List.all_eq_true] at hc
  have := hc p hp
  rw [List.all_eq_true] at this
  exact this d (List.mem_range.mpr hd)

attribute [irreducible] finCheck okPair primesTo61

