import OrdowskiA224.ThreePrimes
import OrdowskiA224.FiniteCheckPQ

/-!
# The case `n = p^a q^b` (two distinct odd primes, any exponents `a, b ≥ 1`)

Write `X = p^a`, `Y = q^b`, `U = 2(p+1) a(X) = pX + c`, `V = 2(q+1) a(Y) = qY + e` (Stangl),
`M = 4(p+1)(q+1)`, so `M s = U V` for `s = a(n)`. If `Q s(s-1) = n² - 1` then
`Q U V (U V - M) = M² (X²Y² - 1)`, which is a quadratic in `X` and in `Y`. See the paper for the
argument; every step below is an exact inequality.
-/

namespace OeisA224

/-! ### Root test specification -/

theorem rootFreeDiv_spec (lo d a b e r : ℕ) (h : rootFreeDiv lo d a b e = true) (ha : 0 < a)
    (he : 0 < e) (hr : a * r ^ 2 = b * r + e) : r < lo ∨ r % d ≠ 0 := by
  unfold rootFreeDiv at h
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne,
    ne_eq] at h
  generalize nsqrt 200 (b*b + 4*a*e) (b + 2*a*e/(b+1) + 1) = c at h
  rcases h with h0 | ⟨⟨h1, h2⟩, h3⟩
  · omega
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h; simp at hr; omega
    · exact h
  have hbr : b < 2 * a * r := by
    have : b * r < a * r * r := by nlinarith
    have : b < a * r := Nat.lt_of_mul_lt_mul_right (a := r) (by linarith)
    nlinarith
  have ht : (2*a*r - b) * (2*a*r - b) = b*b + 4*a*e := by
    zify [hbr.le]
    have hrz : (a:ℤ) * r^2 = b * r + e := by exact_mod_cast hr
    linear_combination 4 * (a:ℤ) * hrz
  have hct : c = 2*a*r - b := by
    rw [← ht] at h1 h2
    have := Nat.mul_self_le_mul_self_iff.mp h1
    have := Nat.mul_self_lt_mul_self_iff.mp h2
    omega
  have hbc : b + c = 2 * a * r := by omega
  rw [hbc, ← ht, hct, Nat.mul_mod_right, Nat.mul_div_cancel_left _ (by omega)] at h3
  simp only [not_true_eq_false, false_or] at h3
  omega

theorem allPow_spec (p B : ℕ) (f : ℕ → ℕ → Bool) (hp : 2 ≤ p) :
    ∀ n a X, allPow p B f n a X = true → ∀ k, X * p ^ k ≤ B → f (a + k) (X * p ^ k) = true := by
  intro n
  induction n with
  | zero => intro a X h; simp [allPow] at h
  | succ n ih =>
    intro a X h k hk
    unfold allPow at h
    by_cases hB : B < X
    · have : X ≤ X * p ^ k := Nat.le_mul_of_pos_right _ (by positivity)
      omega
    · rw [if_neg hB, Bool.and_eq_true] at h
      rcases k with _ | k
      · simpa using h.1
      · have := ih (a+1) (X*p) h.2 k (by rw [pow_succ] at hk; linarith [show X*p*p^k = X*(p^k*p) by ring])
        rw [show a + (k+1) = a + 1 + k by ring, show X * p ^ (k+1) = X * p * p ^ k by ring]
        exact this

theorem allPow_spec' (p B : ℕ) (f : ℕ → ℕ → Bool) (hp : 2 ≤ p)
    (h : allPow p B f 200 1 p = true) (a : ℕ) (ha : 1 ≤ a) (hB : p ^ a ≤ B) : f a (p ^ a) = true := by
  have := allPow_spec p B f hp 200 1 p h (a - 1) (by
    rw [show p * p ^ (a-1) = p ^ a by rw [← pow_succ']; congr 1; omega]; exact hB)
  rwa [show 1 + (a-1) = a by omega, show p * p ^ (a-1) = p ^ a by
    rw [← pow_succ']; congr 1; omega] at this

/-! ### The algebra over `ℤ` -/

section core
variable (p q X Y c e Q U V M : ℤ)

theorem core_quadX (hU : U = p*X + c)
    (key : Q * (U*V) * (U*V - M) = M^2 * (X^2*Y^2 - 1)) :
    (M^2*Y^2 - Q*p^2*V^2) * X^2 = Q*p*V*(2*c*V - M) * X + (Q*c*V*(c*V - M) + M^2) := by
  subst hU; linear_combination (-1) * key

theorem core_quadY (hV : V = q*Y + e)
    (key : Q * (U*V) * (U*V - M) = M^2 * (X^2*Y^2 - 1)) :
    (M^2*X^2 - Q*q^2*U^2) * Y^2 = Q*q*U*(2*e*U - M) * Y + (Q*e*U*(e*U - M) + M^2) := by
  subst hV; linear_combination (-1) * key

theorem core_cV (hp : 3 ≤ p) (hpq : p < q) (hc : p + 2 ≤ c) (hV : (q+1)^2 ≤ V)
    (hM : M = 4*(p+1)*(q+1)) : M < c * V := by
  subst hM
  have h1 : (p+2)*(q+1)^2 ≤ c * V := mul_le_mul hc hV (by positivity) (by linarith)
  nlinarith [mul_pos (by linarith : (0:ℤ) < q+1) (by nlinarith : (0:ℤ) < p*q + 2*q - 3*p - 2)]

theorem core_eU (hp : 3 ≤ p) (hpq : p < q) (he : q + 2 ≤ e) (hU : (p+1)^2 ≤ U)
    (hM : M = 4*(p+1)*(q+1)) : M < e * U := by
  subst hM
  have h1 : (q+2)*(p+1)^2 ≤ e * U := mul_le_mul he hU (by positivity) (by linarith)
  nlinarith [mul_pos (by linarith : (0:ℤ) < p+1) (by nlinarith : (0:ℤ) < p*q + 2*p - 3*q - 2)]

/-- positivity of the leading coefficient of a quadratic `a x² = b x + e` with `b,e > 0`. -/
theorem lead_pos (a b e x : ℤ) (hx : 0 < x) (hb : 0 < b) (he : 0 < e)
    (h : a * x^2 = b * x + e) : 0 < a := by
  by_contra h'; push Not at h'
  have : a * x^2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h' (by positivity)
  nlinarith [mul_pos hb hx]

/-- bound on `q` once `p, Q, X` are fixed (`G = 16(p+1)²X² - Q U²`). -/
theorem core_qbound (hp : 3 ≤ p) (hpq : p < q) (hY : q ≤ Y) (he1 : q + 2 ≤ e) (he2 : e ≤ 2*q+1)
    (hX : 1 ≤ X) (hQ : 1 ≤ Q) (hU : (p+1)^2 ≤ U) (hM : M = 4*(p+1)*(q+1))
    (hquad : (M^2*X^2 - Q*q^2*U^2) * Y^2 = Q*q*U*(2*e*U - M) * Y + (Q*e*U*(e*U - M) + M^2)) :
    (16*(p+1)^2*X^2 - Q*U^2 < 0 → q * (Q*U^2 - 16*(p+1)^2*X^2) < 48*(p+1)^2*X^2) ∧
    (0 < 16*(p+1)^2*X^2 - Q*U^2 → q * (16*(p+1)^2*X^2 - Q*U^2) ≤ 13*Q*U^2) := by
  have heU := core_eU p q e U M hp hpq he1 hU hM
  have hq0 : 0 < q := by linarith
  have hY0 : 0 < Y := by linarith
  have hU0 : 0 < U := by nlinarith
  have hM0 : 0 < M := by rw [hM]; nlinarith
  obtain ⟨c1, hc1d⟩ : ∃ t, t = Q*q*U*(2*e*U - M) := ⟨_, rfl⟩
  obtain ⟨c0, hc0d⟩ : ∃ t, t = Q*e*U*(e*U - M) + M^2 := ⟨_, rfl⟩
  obtain ⟨D, hDd⟩ : ∃ t, t = M^2*X^2 - Q*q^2*U^2 := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ t, t = 16*(p+1)^2*X^2 - Q*U^2 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ t, t = 16*(p+1)^2*X^2 := ⟨_, rfl⟩
  rw [← hc1d, ← hc0d, ← hDd] at hquad
  have heU0 : 0 < e*U := mul_pos (by linarith) hU0
  have hQqU : 0 < Q*q*U := mul_pos (mul_pos (by linarith) hq0) hU0
  have hQeU : 0 < Q*e*U := mul_pos (mul_pos (by linarith) (by linarith)) hU0
  have hc1 : 0 < c1 := by rw [hc1d]; exact mul_pos hQqU (by linarith)
  have hc0 : 0 < c0 := by rw [hc0d]; nlinarith [mul_pos hQeU (by linarith : (0:ℤ) < e*U - M)]
  have hD := lead_pos _ _ _ Y hY0 hc1 hc0 hquad
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hDf : D = q^2 * G + A*(2*q+1) := by rw [hDd, hG, hA, hM]; ring
  have e48 : 48*(p+1)^2*X^2 = 3*A := by rw [hA]; ring
  have eG' : Q*U^2 - 16*(p+1)^2*X^2 = -G := by rw [hG]; ring
  rw [← hG, e48, eG']
  constructor
  · intro hGn
    have h1 : A*(2*q+1) ≤ 3*A*q := by nlinarith only [hA0, hq0]
    have h2 : q * (q * (-G)) < q * (3*A) := by
      have : q*(q*(-G)) = -(q^2*G) := by ring
      rw [this]; nlinarith only [hD, hDf, h1]
    exact lt_of_mul_lt_mul_left h2 hq0.le
  · intro hGp
    have hDY : D * Y ≤ c1 + c0 := by
      have e1 : D * Y * Y - (c1 + c0) * Y = c0 - c0 * Y := by linear_combination hquad
      have e2 : c0 ≤ c0 * Y := le_mul_of_one_le_right hc0.le (by linarith)
      have h1 : D * Y * Y ≤ (c1 + c0) * Y := by linarith
      exact le_of_mul_le_mul_right h1 hY0
    have hQUM : 0 ≤ Q*U*M*(q+e) := by
      have : 0 < Q*U*M := mul_pos (mul_pos (by linarith) hU0) hM0
      exact mul_nonneg this.le (by linarith)
    have hsum : c1 + c0 = Q*U^2*(e*(2*q+e)) + M^2 - Q*U*M*(q+e) := by
      rw [hc1d, hc0d]; ring
    have he2q : e*(2*q+e) ≤ 11*q^2 := by nlinarith only [he1, he2, hq0, hp, hpq]
    have hM2 : M^2 ≤ 2*q^2*U^2 := by
      have h1 : (p+1)^2*(p+1)^2 ≤ U*U := mul_le_mul hU hU (by positivity) hU0.le
      have h16 : (16:ℤ) ≤ (p+1)^2 := by nlinarith
      have h2a : 16*q^2 ≤ q^2*(p+1)^2 := by nlinarith only [mul_le_mul_of_nonneg_left h16 (sq_nonneg q)]
      have h2 : 8*(q+1)^2 ≤ q^2*(p+1)^2 := by nlinarith only [h2a, hp, hpq]
      have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℤ) ≤ 2*(p+1)^2)
      have h4 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℤ) ≤ 2*q^2)
      have e1 : M^2 = 2*(p+1)^2*(8*(q+1)^2) := by rw [hM]; ring
      have e2 : 2*(p+1)^2*(q^2*(p+1)^2) = 2*q^2*((p+1)^2*(p+1)^2) := by ring
      have e3 : 2*q^2*(U*U) = 2*q^2*U^2 := by ring
      linarith
    have hQU : 0 ≤ Q*U^2 := by positivity
    have h3 : Q*U^2*(e*(2*q+e)) ≤ Q*U^2*(11*q^2) := mul_le_mul_of_nonneg_left he2q hQU
    have h4 : 2*q^2*U^2 ≤ 2*Q*q^2*U^2 := by
      have := mul_le_mul_of_nonneg_left hQ (by positivity : (0:ℤ) ≤ 2*q^2*U^2); linarith
    have hlow : q^2 * G * q ≤ D * Y := by
      rw [hDf]
      have h5 : q^2*G*q ≤ q^2*G*Y := mul_le_mul_of_nonneg_left hY (by positivity)
      have h6 : 0 ≤ A*(2*q+1)*Y := by positivity
      have : (q^2*G + A*(2*q+1))*Y = q^2*G*Y + A*(2*q+1)*Y := by ring
      linarith
    have h6 : q^2 * (q * G) ≤ q^2 * (13*Q*U^2) := by
      have e1 : q^2*(q*G) = q^2*G*q := by ring
      have e2 : q^2*(13*Q*U^2) = Q*U^2*(11*q^2) + 2*Q*q^2*U^2 := by ring
      linarith
    exact le_of_mul_le_mul_left h6 (by positivity)

theorem min_aux (Δ K M X Y : ℤ) (hX : 3 ≤ X) (hY : 3 ≤ Y) (hK : 0 ≤ K)
    (h : Δ*X^2*Y^2 < 9*K*X^2*Y + 9*K*X*Y^2 + 81*K*X*Y + M^2) :
    X * Δ < 45*K + M^2 ∨ Y * Δ < 45*K + M^2 := by
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  rcases le_total X Y with hxy | hxy
  · left
    by_contra hc; push Not at hc
    have b1 := mul_le_mul_of_nonneg_right hc (by positivity : (0:ℤ) ≤ X*Y^2)
    have b2 := mul_le_mul_of_nonneg_left hxy (by positivity : (0:ℤ) ≤ 9*K*X*Y)
    have b3 := mul_le_mul_of_nonneg_left hY (by positivity : (0:ℤ) ≤ 27*K*X*Y)
    have b4 : M^2 ≤ M^2*(X*Y^2) := le_mul_of_one_le_right (sq_nonneg M) (by nlinarith)
    have e1 : X*Δ*(X*Y^2) = Δ*X^2*Y^2 := by ring
    have e2 : 9*K*X*Y*X = 9*K*X^2*Y := by ring
    have e3 : 9*K*X*Y*Y = 9*K*X*Y^2 := by ring
    have e4 : 27*K*X*Y*3 = 81*K*X*Y := by ring
    have e5 : 27*K*X*Y*Y = 27*K*X*Y^2 := by ring
    have e6 : (45*K + M^2)*(X*Y^2) = 45*(K*X*Y^2) + M^2*(X*Y^2) := by ring
    have e7 : 9*K*X*Y^2 = 9*(K*X*Y^2) := by ring
    have e8 : 27*K*X*Y^2 = 27*(K*X*Y^2) := by ring
    linarith
  · right
    by_contra hc; push Not at hc
    have b1 := mul_le_mul_of_nonneg_right hc (by positivity : (0:ℤ) ≤ Y*X^2)
    have b2 := mul_le_mul_of_nonneg_left hxy (by positivity : (0:ℤ) ≤ 9*K*X*Y)
    have b3 := mul_le_mul_of_nonneg_left hX (by positivity : (0:ℤ) ≤ 27*K*X*Y)
    have b4 : M^2 ≤ M^2*(Y*X^2) := le_mul_of_one_le_right (sq_nonneg M) (by nlinarith)
    have e1 : Y*Δ*(Y*X^2) = Δ*X^2*Y^2 := by ring
    have e2 : 9*K*X*Y*Y = 9*K*X*Y^2 := by ring
    have e3 : 9*K*X*Y*X = 9*K*X^2*Y := by ring
    have e4 : 27*K*X*Y*3 = 81*K*X*Y := by ring
    have e5 : 27*K*X*Y*X = 27*K*X^2*Y := by ring
    have e6 : (45*K + M^2)*(Y*X^2) = 45*(K*X^2*Y) + M^2*(Y*X^2) := by ring
    have e7 : 9*K*X^2*Y = 9*(K*X^2*Y) := by ring
    have e8 : 27*K*X^2*Y = 27*(K*X^2*Y) := by ring
    linarith

/-- `min(X, Y) · Δ < 45 Q p² q² + M²`, where `Δ = M² - Q p² q² > 0`. -/
theorem core_min (hp : 3 ≤ p) (hpq : p < q) (hX : p ≤ X) (hY : q ≤ Y)
    (hc1 : p+2 ≤ c) (hc2 : c ≤ 2*p+1) (he1 : q+2 ≤ e) (he2 : e ≤ 2*q+1) (hQ : 1 ≤ Q)
    (hUd : U = p*X + c) (hVd : V = q*Y + e) (hM : M = 4*(p+1)*(q+1))
    (hDY : 0 < M^2*Y^2 - Q*p^2*V^2)
    (key : Q * (U*V) * (U*V - M) = M^2 * (X^2*Y^2 - 1)) :
    0 < M^2 - Q*p^2*q^2 ∧
      (X * (M^2 - Q*p^2*q^2) < 45*(Q*p^2*q^2) + M^2 ∨
        Y * (M^2 - Q*p^2*q^2) < 45*(Q*p^2*q^2) + M^2) := by
  have hM0 : 0 < M := by rw [hM]; nlinarith
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hU0 : 0 < U := by rw [hUd]; nlinarith
  have hV0 : 0 < V := by rw [hVd]; nlinarith
  obtain ⟨PX, hPX⟩ : ∃ t, t = U^2 - p^2*X^2 := ⟨_, rfl⟩
  obtain ⟨PY, hPY⟩ : ∃ t, t = V^2 - q^2*Y^2 := ⟨_, rfl⟩
  have hPXe : PX = c*(2*p*X + c) := by rw [hPX, hUd]; ring
  have hPYe : PY = e*(2*q*Y + e) := by rw [hPY, hVd]; ring
  have hPX0 : 0 < PX := by rw [hPXe]; exact mul_pos (by linarith) (by nlinarith)
  have hPY0 : 0 < PY := by rw [hPYe]; exact mul_pos (by linarith) (by nlinarith)
  have hPX9 : PX ≤ 9*p^2*X := by
    rw [hPXe]
    have := mul_le_mul (by linarith : c ≤ 3*p) (by nlinarith : 2*p*X + c ≤ 3*p*X)
      (by nlinarith) (by linarith)
    linarith [show (3*p)*(3*p*X) = 9*p^2*X by ring]
  have hPY9 : PY ≤ 9*q^2*Y := by
    rw [hPYe]
    have := mul_le_mul (by linarith : e ≤ 3*q) (by nlinarith : 2*q*Y + e ≤ 3*q*Y)
      (by nlinarith) (by linarith)
    linarith [show (3*q)*(3*q*Y) = 9*q^2*Y by ring]
  obtain ⟨K, hK⟩ : ∃ t, t = Q*p^2*q^2 := ⟨_, rfl⟩
  obtain ⟨Δ, hΔ⟩ : ∃ t, t = M^2 - K := ⟨_, rfl⟩
  have eΔ : M^2 - Q*p^2*q^2 = Δ := by rw [hΔ, hK]
  rw [eΔ, ← hK]
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hΔ0 : 0 < Δ := by
    have e1 : M^2*Y^2 - Q*p^2*V^2 = Δ*Y^2 - Q*p^2*PY := by rw [hΔ, hK, hPY]; ring
    rw [e1] at hDY
    have : 0 < Q*p^2*PY := mul_pos (mul_pos (by linarith) (by positivity)) hPY0
    by_contra h; push Not at h
    have := mul_nonpos_of_nonpos_of_nonneg h (sq_nonneg Y)
    linarith
  refine ⟨hΔ0, min_aux Δ K M X Y (by linarith) (by linarith) hK0 ?_⟩
  have hlt : M^2 * (X^2*Y^2 - 1) < Q * U^2 * V^2 := by
    have : 0 < Q*(U*V)*M := mul_pos (mul_pos (by linarith) (mul_pos hU0 hV0)) hM0
    have e1 : Q * (U*V) * (U*V - M) = Q*U^2*V^2 - Q*(U*V)*M := by ring
    linarith
  have hexp : Q*U^2*V^2 = K*X^2*Y^2 + Q*(p^2*X^2*PY + q^2*Y^2*PX + PX*PY) := by
    have hU2 : U^2 = p^2*X^2 + PX := by rw [hPX]; ring
    have hV2 : V^2 = q^2*Y^2 + PY := by rw [hPY]; ring
    rw [hU2, hV2, hK]; ring
  have hQ0 : (0:ℤ) ≤ Q := by linarith
  have a1 : Q*(p^2*X^2*PY) ≤ 9*K*X^2*Y := by
    have := mul_le_mul_of_nonneg_left hPY9 (by positivity : (0:ℤ) ≤ Q*p^2*X^2)
    rw [hK]; linarith [show Q*p^2*X^2*(9*q^2*Y) = 9*(Q*p^2*q^2)*X^2*Y by ring,
      show Q*(p^2*X^2*PY) = Q*p^2*X^2*PY by ring]
  have a2 : Q*(q^2*Y^2*PX) ≤ 9*K*X*Y^2 := by
    have := mul_le_mul_of_nonneg_left hPX9 (by positivity : (0:ℤ) ≤ Q*q^2*Y^2)
    rw [hK]; linarith [show Q*q^2*Y^2*(9*p^2*X) = 9*(Q*p^2*q^2)*X*Y^2 by ring,
      show Q*(q^2*Y^2*PX) = Q*q^2*Y^2*PX by ring]
  have a3 : Q*(PX*PY) ≤ 81*K*X*Y := by
    have h1 := mul_le_mul hPX9 hPY9 hPY0.le (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1 hQ0
    rw [hK]; linarith [show Q*(9*p^2*X*(9*q^2*Y)) = 81*(Q*p^2*q^2)*X*Y by ring]
  have e2 : Δ*X^2*Y^2 = M^2*(X^2*Y^2-1) - K*X^2*Y^2 + M^2 := by rw [hΔ]; ring
  have e3 : Q*(p^2*X^2*PY + q^2*Y^2*PX + PX*PY) =
      Q*(p^2*X^2*PY) + Q*(q^2*Y^2*PX) + Q*(PX*PY) := by ring
  linarith

end core

theorem large_ratio (p q w u : ℤ) (hp : 71 ≤ p) (hpq : p < q) (hw : w = (p+1)*(q+1))
    (hu : u = p*q) : 5112^2 * w^2 ≤ 5256^2 * u^2 := by
  have hwu : 5112 * w ≤ 5256 * u := by
    rw [hw, hu]
    have a1 : 71*(p+1) ≤ 72*p := by linarith
    have a2 : 72*(q+1) ≤ 73*q := by linarith
    have := mul_le_mul a1 a2 (by linarith) (by linarith)
    linarith [show 71*(p+1)*(72*(q+1)) = 5112*((p+1)*(q+1)) by ring,
      show 72*p*(73*q) = 5256*(p*q) by ring]
  have hw0 : 0 ≤ w := by rw [hw]; nlinarith
  have := mul_le_mul hwu hwu (by linarith) (by linarith)
  linarith [show 5112*w*(5112*w) = 5112^2*w^2 by ring, show 5256*u*(5256*u) = 5256^2*u^2 by ring]

theorem large_le15 (Q s n w u Z : ℤ) (hQ : Q ≤ 15) (hs1 : 1 ≤ s) (hn : 5112 ≤ n)
    (hu0 : 0 < u) (hw0 : 0 < w) (hQs : Q * (s * (s-1)) = n^2 - 1) (hMs : 4*w*s = Z)
    (hZhi : u * Z ≤ w^2 * n) (h6 : 5112^2 * w^2 ≤ 5256^2 * u^2) : False := by
  have hss : 0 ≤ s*(s-1) := by nlinarith
  have h1 : n^2 - 1 ≤ 15 * (s*(s-1)) := by rw [← hQs]; exact mul_le_mul_of_nonneg_right hQ hss
  have hZ2 : Z^2 = 16*w^2*s^2 := by rw [← hMs]; ring
  have h2 : 16*w^2*(n^2-1) < 15*Z^2 := by
    have a1 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℤ) ≤ 16*w^2)
    have a2 : 0 < 16*w^2*s := by positivity
    rw [hZ2]; linarith [show 16*w^2*(15*(s*(s-1))) = 15*(16*w^2*s^2) - 15*(16*w^2*s) by ring]
  have hZ0 : 0 ≤ Z := by rw [← hMs]; positivity
  have h3 : u^2*Z^2 ≤ w^4*n^2 := by
    have := mul_le_mul hZhi hZhi (by positivity) (by positivity)
    linarith [show u*Z*(u*Z) = u^2*Z^2 by ring, show w^2*n*(w^2*n) = w^4*n^2 by ring]
  have h4 : w^2 * (16*(n^2-1)*u^2) < w^2 * (15*w^2*n^2) := by
    have a1 := mul_lt_mul_of_pos_left h2 (by positivity : (0:ℤ) < u^2)
    have a2 := mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℤ) ≤ 15)
    linarith [show u^2*(16*w^2*(n^2-1)) = w^2*(16*(n^2-1)*u^2) by ring,
      show u^2*(15*Z^2) = 15*(u^2*Z^2) by ring, show 15*(w^4*n^2) = w^2*(15*w^2*n^2) by ring]
  have h5 := lt_of_mul_lt_mul_left h4 (by positivity)
  have h7 := mul_le_mul_of_nonneg_left h6 (by positivity : (0:ℤ) ≤ 15*n^2)
  have h8 : 0 < u^2 * (418120704 - 3737664*n^2) := by
    have : 5112^2*(16*(n^2-1)*u^2) < 5112^2*(15*w^2*n^2) := by linarith
    nlinarith
  have h9 : 418120704 - 3737664*n^2 < 0 := by nlinarith
  nlinarith [mul_neg_of_pos_of_neg (by positivity : (0:ℤ) < u^2) h9]

theorem large_ge17 (Q s n w u Z : ℤ) (hQ : 17 ≤ Q) (hs1 : 1 ≤ s) (hn : 5112 ≤ n)
    (hu0 : 0 < u) (hw0 : 0 < w) (hQs : Q * (s * (s-1)) = n^2 - 1) (hMs : 4*w*s = Z)
    (hZlo : u * n ≤ Z) (h6 : 5112^2 * w^2 ≤ 5256^2 * u^2) : False := by
  have hss : 0 ≤ s*(s-1) := by nlinarith
  have h1 : 17 * (s*(s-1)) ≤ n^2 - 1 := by rw [← hQs]; exact mul_le_mul_of_nonneg_right hQ hss
  have hZZ : Z*(Z - 4*w) = 16*w^2*(s*(s-1)) := by rw [← hMs]; ring
  have h2 : 17 * (Z*(Z - 4*w)) < 16*w^2*n^2 := by
    rw [hZZ]
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℤ) ≤ 16*w^2)
    have : 0 < 16*w^2 := by positivity
    linarith [show 16*w^2*(n^2-1) = 16*w^2*n^2 - 16*w^2 by ring,
      show 17*(16*w^2*(s*(s-1))) = 16*w^2*(17*(s*(s-1))) by ring]
  have hw5 : 5112 * w ≤ 5256 * u := by nlinarith
  have hA : 4*w ≤ u*n := by nlinarith
  have h3 : u*n*(u*n - 4*w) ≤ Z*(Z - 4*w) := by
    have a : 0 ≤ Z - u*n := by linarith
    have : Z*(Z-4*w) - u*n*(u*n-4*w) = (Z - u*n)*(Z + u*n - 4*w) := by ring
    nlinarith [mul_nonneg a (by linarith : (0:ℤ) ≤ Z + u*n - 4*w)]
  have h7 : n * (17*u*(u*n - 4*w)) < n * (16*w^2*n) := by
    linarith [show n*(17*u*(u*n-4*w)) = 17*(u*n*(u*n-4*w)) by ring,
      show n*(16*w^2*n) = 16*w^2*n^2 by ring]
  have h8 := lt_of_mul_lt_mul_left h7 (by linarith)
  have h9 := mul_le_mul_of_nonneg_left h6 (by linarith : (0:ℤ) ≤ 16*n)
  have h10 : u * (2244672 * u * n - 1777012992 * w) < 0 := by
    nlinarith
  have h12 : 0 < 2244672 * u * n - 1777012992 * w := by nlinarith
  nlinarith [mul_pos hu0 h12]

theorem q16_no (s n : ℤ) (hn : 2 ≤ n) (h : 16 * (s * (s-1)) = n^2 - 1) : False := by
  have ht : (4*s-2)^2 = n^2 + 3 := by linear_combination h
  have h1 : n < |4*s-2| := by
    by_contra hc; push Not at hc
    have := pow_le_pow_left₀ (abs_nonneg _) hc 2
    rw [sq_abs] at this; linarith
  have h2 : n + 1 ≤ |4*s-2| := h1
  have := pow_le_pow_left₀ (by linarith) h2 2
  rw [sq_abs] at this; nlinarith

/-- No solutions with `p ≥ 71` (then `15 < Q < 17`, and `Q = 16` is impossible). -/
theorem core_large (p q X Y c e Q s : ℤ) (hp : 71 ≤ p) (hpq : p < q) (hX : p ≤ X) (hY : q ≤ Y)
    (hc1 : 0 ≤ c) (hc2 : c ≤ 2*p+1) (he1 : 0 ≤ e) (he2 : e ≤ 2*q+1)
    (hs : 4*(p+1)*(q+1) * s = (p*X + c) * (q*Y + e))
    (hQs : Q * (s * (s-1)) = (X*Y)^2 - 1) : False := by
  obtain ⟨n, hn⟩ : ∃ n, n = X*Y := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = (p+1)*(q+1) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = p*q := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = (p*X + c) * (q*Y + e) := ⟨_, rfl⟩
  rw [← hn] at hQs
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hn0 : 5112 ≤ n := by rw [hn]; nlinarith
  have h6 := large_ratio p q w u hp hpq hw hu
  have hu0 : 0 < u := by rw [hu]; nlinarith
  have hw0 : 0 < w := by rw [hw]; nlinarith
  have hpX : p*X ≤ p*X + c := by linarith
  have hqY : q*Y ≤ q*Y + e := by linarith
  have hZlo : u * n ≤ Z := by
    have := mul_le_mul hpX hqY (by nlinarith) (by nlinarith)
    rw [hZ, hu, hn]; linarith [show p*X*(q*Y) = p*q*(X*Y) by ring]
  have hZhi : u * Z ≤ w^2 * n := by
    have a1 : p*(p*X+c) ≤ (p+1)^2*X := by nlinarith
    have a2 : q*(q*Y+e) ≤ (q+1)^2*Y := by nlinarith
    have := mul_le_mul a1 a2 (by nlinarith) (by positivity)
    rw [hZ, hu, hw, hn]
    linarith [show p*(p*X+c)*(q*(q*Y+e)) = p*q*((p*X+c)*(q*Y+e)) by ring,
      show (p+1)^2*X*((q+1)^2*Y) = ((p+1)*(q+1))^2*(X*Y) by ring]
  have hMs : 4*w*s = Z := by rw [hw, hZ]; linear_combination hs
  have hZ0 : 0 < Z := by nlinarith
  have hs1 : 1 ≤ s := by nlinarith
  rcases lt_trichotomy Q 16 with hQ | hQ | hQ
  · exact large_le15 Q s n w u Z (by omega) hs1 hn0 hu0 hw0 hQs hMs hZhi h6
  · subst hQ
    exact q16_no s n (by linarith) hQs
  · exact large_ge17 Q s n w u Z (by omega) hs1 hn0 hu0 hw0 hQs hMs hZlo h6

end OeisA224
