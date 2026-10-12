import OrdowskiA224.FiniteCheckPQ

namespace OeisA224

/-- `bigBranch` restricted to `q ∈ [lo, lo + n)`. -/
def bbR (p Q lo n : ℕ) : Bool :=
  (List.range' lo n).all fun q => q ≤ p || q % 2 == 0 || triple p Q q

end OeisA224

namespace OeisA224

theorem bbR_append (p Q lo m n : ℕ) :
    (bbR p Q lo m && bbR p Q (lo+m) n) = bbR p Q lo (m+n) := by
  simp only [bbR, ← List.range'_append, List.all_append, Nat.one_mul]

theorem bigBranch_eq (p Q qU : ℕ) : bigBranch p Q qU = bbR p Q 0 (qU+1) := by
  simp only [bigBranch, bbR, List.range_eq_range']

theorem allPow_of (p B : ℕ) (f : ℕ → ℕ → Bool) :
    ∀ n a X, B < X*p^n → (∀ k ≤ n, X*p^k ≤ B → f (a+k) (X*p^k) = true) →
      allPow p B f (n+1) a X = true := by
  intro n
  induction n with
  | zero => intro a X h _; simp at h; simp [allPow, h]
  | succ n ih =>
    intro a X hB hf
    simp only [allPow]
    split
    · rfl
    · rename_i hX
      have h0 := hf 0 (by omega) (by simpa using hX)
      simp only [Nat.add_zero, pow_zero, mul_one] at h0
      rw [h0, Bool.true_and]
      have := ih (a+1) (X*p) (by rw [mul_assoc, ← pow_succ']; exact hB) (by
        intro k hk hk'
        have := hf (k+1) (by omega) (by rw [pow_succ', ← mul_assoc]; exact hk')
        rw [pow_succ', ← mul_assoc, show a + (k+1) = a + 1 + k by omega] at this
        exact this)
      simpa [allPow] using this

end OeisA224
