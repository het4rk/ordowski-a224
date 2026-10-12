import OrdowskiA224.TwoPrimePowers
import OrdowskiA224.FiniteCheckPQAll

/-!
# Glue: the finite check `okP2` rules out every `n = p^a q^b` with `p ≤ 67`
-/

namespace OeisA224

/-- One root test for the quadratic in `Y`. -/
theorem noY_one (p X c q Q Y e : ℕ) (hp : 3 ≤ p) (hpq : p < q) (hX : p ≤ X) (hY : q ≤ Y)
    (hqY : q ∣ Y) (hc1 : p+2 ≤ c) (hU2N : (p+1)^2 ≤ p*X+c) (he1 : q+2 ≤ e) (he2 : e ≤ 2*q+1) (hQ : 1 ≤ Q)
    (key : (Q:ℤ) * (((p:ℤ)*X+c)*((q:ℤ)*Y+e)) * (((p:ℤ)*X+c)*((q:ℤ)*Y+e) - 4*((p:ℤ)+1)*((q:ℤ)+1))
      = (4*((p:ℤ)+1)*((q:ℤ)+1))^2 * ((X:ℤ)^2*(Y:ℤ)^2-1))
    (h : (4*(p+1)*(q+1))*(4*(p+1)*(q+1))*(X*X) ≤ Q*(q*q)*((p*X+c)*(p*X+c)) ∨
      rootFreeDiv q q ((4*(p+1)*(q+1))*(4*(p+1)*(q+1))*(X*X) - Q*(q*q)*((p*X+c)*(p*X+c)))
        (Q*q*(p*X+c)*(2*e*(p*X+c) - 4*(p+1)*(q+1)))
        (Q*e*(p*X+c)*(e*(p*X+c) - 4*(p+1)*(q+1)) + (4*(p+1)*(q+1))*(4*(p+1)*(q+1))) = true) :
    False := by
  obtain ⟨U, hU⟩ : ∃ U, U = p*X+c := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = 4*(p+1)*(q+1) := ⟨_, rfl⟩
  rw [← hU, ← hM] at h
  have hUz : (U:ℤ) = (p:ℤ)*X+c := by rw [hU]; push_cast; ring
  have hMz : (M:ℤ) = 4*((p:ℤ)+1)*((q:ℤ)+1) := by rw [hM]; push_cast; ring
  rw [← hUz, ← hMz] at key
  have hquad := core_quadY (q := q) (X := X) (Y := Y) (e := e) (Q := Q) (U := U) (V := (q:ℤ)*Y+e) (M := M) rfl key
  have hpZ : (3:ℤ) ≤ p := by exact_mod_cast hp
  have hpqZ : (p:ℤ) < q := by exact_mod_cast hpq
  have hU2 : ((p:ℤ)+1)^2 ≤ U := by rw [← hU] at hU2N; exact_mod_cast hU2N
  have heU := core_eU (p:ℤ) q e U M hpZ hpqZ (by exact_mod_cast he1) hU2 hMz
  have hY0 : (0:ℤ) < Y := by linarith [(by exact_mod_cast hY : (q:ℤ) ≤ Y)]
  have hU0 : (0:ℤ) < U := by nlinarith
  have hM0 : (0:ℤ) < M := by rw [hMz]; nlinarith
  have hb : (0:ℤ) < Q*q*U*(2*e*U - M) := by
    have : (0:ℤ) < Q := by exact_mod_cast hQ
    have : (0:ℤ) < q := by linarith
    have : (0:ℤ) < Q*q*U := by positivity
    exact mul_pos this (by linarith)
  have he0 : (0:ℤ) < Q*e*U*(e*U - M) + M^2 := by
    have : (0:ℤ) < Q := by exact_mod_cast hQ
    have : (0:ℤ) < e := by linarith [(by exact_mod_cast he1 : (q:ℤ)+2 ≤ e)]
    have : (0:ℤ) < Q*e*U := by positivity
    nlinarith [mul_pos this (by linarith : (0:ℤ) < e*U - M)]
  have hlead := lead_pos _ _ _ _ hY0 hb he0 hquad
  have hleadN : Q*(q*q)*(U*U) < M*M*(X*X) := by
    have : ((Q*(q*q)*(U*U) : ℕ) : ℤ) < ((M*M*(X*X) : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this
  have heUN : M < e*U := by exact_mod_cast heU
  rcases h with h | h
  · omega
  have hle1 : M ≤ 2*e*U := by nlinarith
  have hr := rootFreeDiv_spec q q _ _ _ Y h (by omega) (Nat.add_pos_right _ (Nat.mul_pos (by rw [hM]; positivity) (by rw [hM]; positivity))) (by
    zify [hleadN.le, hle1, heUN.le]
    linear_combination hquad)
  have := Nat.mod_eq_zero_of_dvd hqY
  omega

/-- One root test for the quadratic in `X`. -/
theorem noX_one (p q Y e Q X c : ℕ) (hp : 3 ≤ p) (hpq : p < q) (hX : p ≤ X) (hY : q ≤ Y)
    (hpX : p ∣ X) (hc1 : p+2 ≤ c) (he1 : q+2 ≤ e) (hV2N : (q+1)^2 ≤ q*Y+e) (hQ : 1 ≤ Q)
    (key : (Q:ℤ) * (((p:ℤ)*X+c)*((q:ℤ)*Y+e)) * (((p:ℤ)*X+c)*((q:ℤ)*Y+e) - 4*((p:ℤ)+1)*((q:ℤ)+1))
      = (4*((p:ℤ)+1)*((q:ℤ)+1))^2 * ((X:ℤ)^2*(Y:ℤ)^2-1))
    (h : (4*(p+1)*(q+1))*(4*(p+1)*(q+1))*(Y*Y) ≤ Q*(p*p)*((q*Y+e)*(q*Y+e)) ∨
      rootFreeDiv p p ((4*(p+1)*(q+1))*(4*(p+1)*(q+1))*(Y*Y) - Q*(p*p)*((q*Y+e)*(q*Y+e)))
        (Q*p*(q*Y+e)*(2*c*(q*Y+e) - 4*(p+1)*(q+1)))
        (Q*c*(q*Y+e)*(c*(q*Y+e) - 4*(p+1)*(q+1)) + (4*(p+1)*(q+1))*(4*(p+1)*(q+1))) = true) :
    False := by
  obtain ⟨V, hV⟩ : ∃ V, V = q*Y+e := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = 4*(p+1)*(q+1) := ⟨_, rfl⟩
  rw [← hV, ← hM] at h
  have hVz : (V:ℤ) = (q:ℤ)*Y+e := by rw [hV]; push_cast; ring
  have hMz : (M:ℤ) = 4*((p:ℤ)+1)*((q:ℤ)+1) := by rw [hM]; push_cast; ring
  rw [← hVz, ← hMz] at key
  have hquad := core_quadX (p := p) (X := X) (Y := Y) (c := c) (Q := Q) (U := (p:ℤ)*X+c) (V := V) (M := M) rfl key
  have hpZ : (3:ℤ) ≤ p := by exact_mod_cast hp
  have hpqZ : (p:ℤ) < q := by exact_mod_cast hpq
  have hV2 : ((q:ℤ)+1)^2 ≤ V := by rw [← hV] at hV2N; exact_mod_cast hV2N
  have hcV := core_cV (p:ℤ) q c V M hpZ hpqZ (by exact_mod_cast hc1) hV2 hMz
  have hX0 : (0:ℤ) < X := by linarith [(by exact_mod_cast hX : (p:ℤ) ≤ X)]
  have hV0 : (0:ℤ) < V := by nlinarith
  have hM0 : (0:ℤ) < M := by rw [hMz]; nlinarith
  have hb : (0:ℤ) < Q*p*V*(2*c*V - M) := by
    have : (0:ℤ) < Q := by exact_mod_cast hQ
    have : (0:ℤ) < p := by linarith
    have : (0:ℤ) < Q*p*V := by positivity
    exact mul_pos this (by linarith)
  have he0 : (0:ℤ) < Q*c*V*(c*V - M) + M^2 := by
    have : (0:ℤ) < Q := by exact_mod_cast hQ
    have : (0:ℤ) < c := by linarith [(by exact_mod_cast hc1 : (p:ℤ)+2 ≤ c)]
    have : (0:ℤ) < Q*c*V := by positivity
    nlinarith [mul_pos this (by linarith : (0:ℤ) < c*V - M)]
  have hlead := lead_pos _ _ _ _ hX0 hb he0 hquad
  have hleadN : Q*(p*p)*(V*V) < M*M*(Y*Y) := by
    have : ((Q*(p*p)*(V*V) : ℕ) : ℤ) < ((M*M*(Y*Y) : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this
  have hcVN : M < c*V := by exact_mod_cast hcV
  rcases h with h | h
  · omega
  have hle1 : M ≤ 2*c*V := by nlinarith
  have hr := rootFreeDiv_spec p p _ _ _ X h (by omega) (Nat.add_pos_right _ (Nat.mul_pos (by rw [hM]; positivity) (by rw [hM]; positivity))) (by
    zify [hleadN.le, hle1, hcVN.le]
    linear_combination hquad)
  have := Nat.mod_eq_zero_of_dvd hpX
  omega

end OeisA224
