import OrdowskiA224.TwoPrimePowersGlue
import OrdowskiA224.PrimePower
import OrdowskiA224.MainThree

/-!
# The case `n = p^a q^b`: assembling the reduction and the finite check
-/

namespace OeisA224

def KeyEq (p q X Y c e Q : ℕ) : Prop :=
  (Q:ℤ) * (((p:ℤ)*X+c)*((q:ℤ)*Y+e)) * (((p:ℤ)*X+c)*((q:ℤ)*Y+e) - 4*((p:ℤ)+1)*((q:ℤ)+1))
      = (4*((p:ℤ)+1)*((q:ℤ)+1))^2 * ((X:ℤ)^2*(Y:ℤ)^2-1)

theorem cpar_facts (p a : ℕ) (hp : 3 ≤ p) (ha : 1 ≤ a) :
    p + 2 ≤ cpar p a ∧ cpar p a ≤ 2*p+1 ∧ p ≤ p^a ∧ p ∣ p^a ∧ (p+1)^2 ≤ p*p^a + cpar p a := by
  have h1 : p ≤ p^a := by
    calc p = p^1 := (pow_one p).symm
      _ ≤ p^a := Nat.pow_le_pow_right (by omega) ha
  have h2 : p ∣ p^a := dvd_pow_self p (by omega)
  unfold cpar
  split_ifs with h
  · have ha2 : 2 ≤ a := by omega
    have : p^2 ≤ p^a := Nat.pow_le_pow_right (by omega) ha2
    refine ⟨le_refl _, by omega, h1, h2, ?_⟩
    nlinarith
  · refine ⟨by omega, le_refl _, h1, h2, ?_⟩
    nlinarith

theorem cpar_cases (p a : ℕ) : cpar p a = p + 2 ∨ cpar p a = 2*p+1 := by
  unfold cpar; split_ifs <;> simp

theorem solveY_spec (p X c q Q Y e : ℕ) (hp : 3 ≤ p) (hpq : p < q) (hX : p ≤ X) (hY : q ≤ Y)
    (hqY : q ∣ Y) (hc1 : p+2 ≤ c) (hU2N : (p+1)^2 ≤ p*X+c) (he : e = q+2 ∨ e = 2*q+1)
    (hQ : 1 ≤ Q) (key : KeyEq p q X Y c e Q) (h : solveY p X c q Q = true) : False := by
  unfold solveY at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases he with rfl | rfl
  · exact noY_one p X c q Q Y (q+2) hp hpq hX hY hqY hc1 hU2N (le_refl _) (by omega) hQ key
      (h.imp id (fun h' => h'.1))
  · exact noY_one p X c q Q Y (2*q+1) hp hpq hX hY hqY hc1 hU2N (by omega) (le_refl _) hQ key
      (h.imp id (fun h' => h'.2))

theorem solveX_spec (p q Y e Q X c : ℕ) (hp : 3 ≤ p) (hpq : p < q) (hX : p ≤ X) (hY : q ≤ Y)
    (hpX : p ∣ X) (he1 : q+2 ≤ e) (hV2N : (q+1)^2 ≤ q*Y+e) (hc : c = p+2 ∨ c = 2*p+1)
    (hQ : 1 ≤ Q) (key : KeyEq p q X Y c e Q) (h : solveX p q Y e Q = true) : False := by
  unfold solveX at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases hc with rfl | rfl
  · exact noX_one p q Y e Q X (p+2) hp hpq hX hY hpX (le_refl _) he1 hV2N hQ key
      (h.imp id (fun h' => h'.1))
  · exact noX_one p q Y e Q X (2*p+1) hp hpq hX hY hpX (by omega) he1 hV2N hQ key
      (h.imp id (fun h' => h'.2))

theorem KM_lt (p q X Y c e Q : ℤ) (hp : 3 ≤ p) (hpq : p < q) (hX : p ≤ X) (hY : q ≤ Y)
    (hc1 : p+2 ≤ c) (he1 : q+2 ≤ e) (hQ : 0 ≤ Q)
    (key : Q*((p*X+c)*(q*Y+e))*((p*X+c)*(q*Y+e) - 4*(p+1)*(q+1))
      = (4*(p+1)*(q+1))^2*(X^2*Y^2-1)) :
    Q*p^2*q^2 < (4*(p+1)*(q+1))^2 := by
  obtain ⟨W, hW⟩ : ∃ W, W = (p*X+c)*(q*Y+e) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = 4*(p+1)*(q+1) := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, n = X*Y := ⟨_, rfl⟩
  rw [← hW, ← hM] at key
  rw [← hM]
  have hpq0 : 0 < p*q := by nlinarith
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hn0 : 0 < n := by rw [hn]; exact mul_pos hX0 hY0
  have hM0 : 0 < M := by rw [hM]; nlinarith
  have hWM : p*q*n ≤ W - M := by
    have hqq : q*q ≤ q*Y := by nlinarith
    have hcY : q*q*(p+2) ≤ q*Y*c := mul_le_mul hqq hc1 (by linarith) (by nlinarith)
    have hMle : M ≤ q*q*(p+2) := by rw [hM]; nlinarith
    have hpX : 0 ≤ p*X := by nlinarith
    have : 0 ≤ p*X*e := mul_nonneg hpX (by linarith)
    have : 0 ≤ c*e := mul_nonneg (by linarith) (by linarith)
    have : W = p*q*n + p*X*e + q*Y*c + c*e := by rw [hW, hn]; ring
    linarith
  have hpqn : 0 < p*q*n := mul_pos hpq0 hn0
  have h1 : (p*q*n)*(p*q*n) ≤ W*(W-M) := mul_le_mul (by linarith) hWM hpqn.le (by linarith)
  have h2 : Q*((p*q*n)*(p*q*n)) ≤ Q*(W*(W-M)) := mul_le_mul_of_nonneg_left h1 hQ
  have h3 : Q*(W*(W-M)) = M^2*(n^2-1) := by rw [hn]; linear_combination key
  have hM2 : 0 < M^2 := pow_pos hM0 2
  have h4 : (Q*p^2*q^2) * n^2 < M^2 * n^2 := by nlinarith
  exact lt_of_mul_lt_mul_right h4 (by positivity)

theorem Q_le_40 (p q Q : ℤ) (hp : 3 ≤ p) (hpq : p < q) (hq5 : 5 ≤ q)
    (h : Q*p^2*q^2 < (4*(p+1)*(q+1))^2) : Q ≤ 40 := by
  by_contra hc; push Not at hc
  have h1 : 5*((p+1)*(q+1)) ≤ 8*(p*q) := by
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ p-3) (by linarith : (0:ℤ) ≤ q-5)]
  have h0 : 0 ≤ (p+1)*(q+1) := by nlinarith
  have h2 : 25*((p+1)*(q+1))^2 ≤ 64*(p*q)^2 := by
    nlinarith [mul_le_mul h1 h1 (by positivity) (by nlinarith)]
  have h3 : 41*(p*q)^2 ≤ Q*(p*q)^2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have hpq0 : 0 < (p*q)^2 := by have : 0 < p*q := by nlinarith
                                positivity
  nlinarith

theorem leadX_pos (p q X Y c e Q U V M : ℤ) (hp : 3 ≤ p) (hpq : p < q) (hX : p ≤ X)
    (hc1 : p+2 ≤ c) (hV2 : (q+1)^2 ≤ V) (hQ : 1 ≤ Q) (hM : M = 4*(p+1)*(q+1)) (hU : U = p*X+c)
    (key : Q*(U*V)*(U*V-M) = M^2*(X^2*Y^2-1)) : 0 < M^2*Y^2 - Q*p^2*V^2 := by
  have hquad := core_quadX (p := p) (X := X) (Y := Y) (c := c) (Q := Q) (U := U) (V := V)
    (M := M) hU key
  have hcV := core_cV p q c V M hp hpq hc1 hV2 hM
  have hX0 : 0 < X := by linarith
  have hV0 : 0 < V := by nlinarith
  have hM0 : 0 < M := by rw [hM]; nlinarith
  have hQ0 : 0 < Q := by linarith
  have hc0 : 0 < c := by linarith
  have hb : 0 < Q*p*V*(2*c*V - M) :=
    mul_pos (mul_pos (mul_pos hQ0 (by linarith)) hV0) (by linarith)
  have he0 : 0 < Q*c*V*(c*V - M) + M^2 := by
    have : 0 < Q*c*V := mul_pos (mul_pos hQ0 hc0) hV0
    nlinarith [mul_pos this (by linarith : (0:ℤ) < c*V - M)]
  exact lead_pos _ _ _ _ hX0 hb he0 hquad

theorem triple_eq (p Q q : ℕ) : triple p Q q =
    (decide (4*(p+1)*(q+1)*(4*(p+1)*(q+1)) ≤ Q*(p*p)*(q*q)) ||
      (allPow p ((45*Q*(p*p)*(q*q) + 4*(p+1)*(q+1)*(4*(p+1)*(q+1))) /
          (4*(p+1)*(q+1)*(4*(p+1)*(q+1)) - Q*(p*p)*(q*q)))
          (fun a X => solveY p X (cpar p a) q Q) 200 1 p &&
       allPow q ((45*Q*(p*p)*(q*q) + 4*(p+1)*(q+1)*(4*(p+1)*(q+1))) /
          (4*(p+1)*(q+1)*(4*(p+1)*(q+1)) - Q*(p*p)*(q*q)))
          (fun b Y => solveX p q Y (cpar q b) Q) 200 1 q)) := rfl

theorem triple_spec (p q aa bb Q : ℕ) (hp : 3 ≤ p) (hpq : p < q) (ha : 1 ≤ aa) (hb : 1 ≤ bb)
    (hQ : 1 ≤ Q) (key : KeyEq p q (p^aa) (q^bb) (cpar p aa) (cpar q bb) Q)
    (h : triple p Q q = true) : False := by
  obtain ⟨hc1, hc2, hX, hpX, hU2⟩ := cpar_facts p aa hp ha
  obtain ⟨he1, he2, hY, hqY, hV2⟩ := cpar_facts q bb (by omega) hb
  obtain ⟨X, hXd⟩ : ∃ X, X = p^aa := ⟨_, rfl⟩
  obtain ⟨Y, hYd⟩ : ∃ Y, Y = q^bb := ⟨_, rfl⟩
  rw [← hXd] at hX hpX hU2
  rw [← hYd] at hY hqY hV2
  rw [← hXd, ← hYd] at key
  have keyZ := key
  unfold KeyEq at keyZ
  have hpZ : (3:ℤ) ≤ p := by exact_mod_cast hp
  have hpqZ : (p:ℤ) < q := by exact_mod_cast hpq
  have hXZ : (p:ℤ) ≤ X := by exact_mod_cast hX
  have hYZ : (q:ℤ) ≤ Y := by exact_mod_cast hY
  have hc1Z : (p:ℤ)+2 ≤ cpar p aa := by exact_mod_cast hc1
  have hc2Z : (cpar p aa : ℤ) ≤ 2*p+1 := by exact_mod_cast hc2
  have he1Z : (q:ℤ)+2 ≤ cpar q bb := by exact_mod_cast he1
  have he2Z : (cpar q bb : ℤ) ≤ 2*q+1 := by exact_mod_cast he2
  have hQZ : (1:ℤ) ≤ Q := by exact_mod_cast hQ
  have hV2Z : ((q:ℤ)+1)^2 ≤ (q:ℤ)*Y + cpar q bb := by exact_mod_cast hV2
  have hKZ := KM_lt _ _ _ _ _ _ _ hpZ hpqZ hXZ hYZ hc1Z he1Z (by linarith) keyZ
  have hK : Q*(p*p)*(q*q) < (4*(p+1)*(q+1))*(4*(p+1)*(q+1)) := by
    have : ((Q*(p*p)*(q*q) : ℕ) : ℤ) < (((4*(p+1)*(q+1))*(4*(p+1)*(q+1)) : ℕ) : ℤ) := by
      push_cast
      linarith [hKZ, show (Q:ℤ)*(p*p)*(q*q) = Q*p^2*q^2 by ring,
        show (4*((p:ℤ)+1)*(q+1))*(4*(p+1)*(q+1)) = (4*(p+1)*(q+1))^2 by ring]
    exact_mod_cast this
  rw [triple_eq] at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨h1, h2⟩
  · omega
  have hDY := leadX_pos (p:ℤ) q X Y (cpar p aa) (cpar q bb) Q _ _ _ hpZ hpqZ hXZ hc1Z hV2Z hQZ
    rfl rfl keyZ
  obtain ⟨_, hmin⟩ := core_min (p:ℤ) q X Y (cpar p aa) (cpar q bb) Q _ _ _ hpZ hpqZ hXZ hYZ
    hc1Z hc2Z he1Z he2Z hQZ rfl rfl rfl hDY keyZ
  have hp2 : 2 ≤ p := by omega
  have hq2 : 2 ≤ q := by omega
  rcases hmin with hm | hm
  · have hXB : X ≤ (45*Q*(p*p)*(q*q) + 4*(p+1)*(q+1)*(4*(p+1)*(q+1))) /
        (4*(p+1)*(q+1)*(4*(p+1)*(q+1)) - Q*(p*p)*(q*q)) := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      zify [hK.le]
      linear_combination hm
    have := allPow_spec' p _ _ hp2 h1 aa ha (by rw [← hXd]; exact hXB)
    rw [← hXd] at this
    exact solveY_spec p X (cpar p aa) q Q Y (cpar q bb) hp hpq hX hY hqY hc1 hU2
      (cpar_cases q bb) hQ key this
  · have hYB : Y ≤ (45*Q*(p*p)*(q*q) + 4*(p+1)*(q+1)*(4*(p+1)*(q+1))) /
        (4*(p+1)*(q+1)*(4*(p+1)*(q+1)) - Q*(p*p)*(q*q)) := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      zify [hK.le]
      linear_combination hm
    have := allPow_spec' q _ _ hq2 h2 bb hb (by rw [← hYd]; exact hYB)
    rw [← hYd] at this
    exact solveX_spec p q Y (cpar q bb) Q X (cpar p aa) hp hpq hX hY hpX he1 hV2
      (cpar_cases p aa) hQ key this

theorem bigBranch_mem (p Q qU q : ℕ) (h : bigBranch p Q qU = true) (hpq : p < q)
    (hq : q % 2 = 1) (hqU : q ≤ qU) : triple p Q q = true := by
  unfold bigBranch at h
  rw [List.all_eq_true] at h
  have h' := h q (List.mem_range.mpr (by omega))
  have e1 : (q ≤ p : Bool) = false := by simp; omega
  have e2 : (q % 2 == 0) = false := by simp; omega
  rw [e1, e2] at h'
  simpa using h'


theorem qbound_nat (p q X Y c e Q : ℕ) (hp : 3 ≤ p) (hpq : p < q) (hX : p ≤ X) (hY : q ≤ Y)
    (hU2 : (p+1)^2 ≤ p*X+c) (he1 : q+2 ≤ e) (he2 : e ≤ 2*q+1) (hQ : 1 ≤ Q)
    (key : KeyEq p q X Y c e Q) :
    (16*(p+1)^2*(X*X) < Q*((p*X+c)*(p*X+c)) →
      q * (Q*((p*X+c)*(p*X+c)) - 16*(p+1)^2*(X*X)) < 48*(p+1)^2*(X*X)) ∧
    (Q*((p*X+c)*(p*X+c)) < 16*(p+1)^2*(X*X) →
      q * (16*(p+1)^2*(X*X) - Q*((p*X+c)*(p*X+c))) ≤ 13*Q*((p*X+c)*(p*X+c))) := by
  have keyZ := key
  unfold KeyEq at keyZ
  have hquad := core_quadY (q := q) (X := X) (Y := Y) (e := e) (Q := Q) (U := (p:ℤ)*X+c)
    (V := (q:ℤ)*Y+e) (M := 4*((p:ℤ)+1)*((q:ℤ)+1)) rfl keyZ
  have hU2Z : ((p:ℤ)+1)^2 ≤ (p:ℤ)*X+c := by exact_mod_cast hU2
  have cq := core_qbound (p:ℤ) q X Y e Q ((p:ℤ)*X+c) (4*((p:ℤ)+1)*((q:ℤ)+1))
    (by exact_mod_cast hp) (by exact_mod_cast hpq) (by exact_mod_cast hY) (by exact_mod_cast he1)
    (by exact_mod_cast he2) (by have : (3:ℤ) ≤ X := by exact_mod_cast (by omega : 3 ≤ X)
                                linarith)
    (by exact_mod_cast hQ) hU2Z rfl hquad
  constructor
  · intro h
    have hZ : ((16*(p+1)^2*(X*X) : ℕ) : ℤ) < ((Q*((p*X+c)*(p*X+c)) : ℕ) : ℤ) := by exact_mod_cast h
    push_cast at hZ
    have := cq.1 (by linarith [show ((Q:ℤ)*((p*X+c)*(p*X+c))) = Q*((p:ℤ)*X+c)^2 by ring,
      show (16*((p:ℤ)+1)^2*(X*X)) = 16*((p:ℤ)+1)^2*X^2 by ring])
    zify [h.le]
    linear_combination this
  · intro h
    have hZ : ((Q*((p*X+c)*(p*X+c)) : ℕ) : ℤ) < ((16*(p+1)^2*(X*X) : ℕ) : ℤ) := by exact_mod_cast h
    push_cast at hZ
    have := cq.2 (by linarith [show ((Q:ℤ)*((p*X+c)*(p*X+c))) = Q*((p:ℤ)*X+c)^2 by ring,
      show (16*((p:ℤ)+1)^2*(X*X)) = 16*((p:ℤ)+1)^2*X^2 by ring])
    zify [h.le]
    linear_combination this

theorem smallCheck_eq (p Q a : ℕ) : smallCheck p Q a =
    ((16*(p+1)^2*(p^a*p^a) != Q*((p*p^a+cpar p a)*(p*p^a+cpar p a))) &&
     (List.range ((if 16*(p+1)^2*(p^a*p^a) < Q*((p*p^a+cpar p a)*(p*p^a+cpar p a))
        then 48*(p+1)^2*(p^a*p^a) / (Q*((p*p^a+cpar p a)*(p*p^a+cpar p a)) - 16*(p+1)^2*(p^a*p^a))
        else 13*Q*((p*p^a+cpar p a)*(p*p^a+cpar p a)) /
          (16*(p+1)^2*(p^a*p^a) - Q*((p*p^a+cpar p a)*(p*p^a+cpar p a)))) + 1)).all
       fun q => q ≤ p || q % 2 == 0 || solveY p (p^a) (cpar p a) q Q) := rfl

theorem smallCheck_spec (p q aa bb Q : ℕ) (hp : 3 ≤ p) (hpq : p < q) (hqo : q % 2 = 1)
    (ha : 1 ≤ aa) (hb : 1 ≤ bb) (hQ : 1 ≤ Q)
    (key : KeyEq p q (p^aa) (q^bb) (cpar p aa) (cpar q bb) Q)
    (h : smallCheck p Q aa = true) : False := by
  obtain ⟨hc1, hc2, hX, hpX, hU2⟩ := cpar_facts p aa hp ha
  obtain ⟨he1, he2, hY, hqY, hV2⟩ := cpar_facts q bb (by omega) hb
  have qb := qbound_nat p q (p^aa) (q^bb) (cpar p aa) (cpar q bb) Q hp hpq hX hY hU2 he1 he2 hQ key
  rw [smallCheck_eq] at h
  obtain ⟨hne, hall⟩ := Bool.and_eq_true_iff.mp h
  rw [List.all_eq_true] at hall
  have hq : q ∈ List.range ((if 16*(p+1)^2*(p^aa*p^aa) < Q*((p*p^aa+cpar p aa)*(p*p^aa+cpar p aa))
        then 48*(p+1)^2*(p^aa*p^aa) / (Q*((p*p^aa+cpar p aa)*(p*p^aa+cpar p aa)) - 16*(p+1)^2*(p^aa*p^aa))
        else 13*Q*((p*p^aa+cpar p aa)*(p*p^aa+cpar p aa)) /
          (16*(p+1)^2*(p^aa*p^aa) - Q*((p*p^aa+cpar p aa)*(p*p^aa+cpar p aa)))) + 1) := by
    rw [List.mem_range, Nat.lt_succ_iff]
    split_ifs with hlt
    · rw [Nat.le_div_iff_mul_le (by omega)]
      exact (qb.1 hlt).le
    · have hne' := hne
      simp only [bne_iff_ne, ne_eq] at hne'
      have hlt' : Q*((p*p^aa+cpar p aa)*(p*p^aa+cpar p aa)) < 16*(p+1)^2*(p^aa*p^aa) := by omega
      rw [Nat.le_div_iff_mul_le (by omega)]
      have := qb.2 hlt'
      linarith [Nat.mul_comm q (16*(p+1)^2*(p^aa*p^aa) - Q*((p*p^aa+cpar p aa)*(p*p^aa+cpar p aa)))]
  have h' := hall q hq
  have e1 : (q ≤ p : Bool) = false := by simp; omega
  have e2 : (q % 2 == 0) = false := by simp; omega
  rw [e1, e2] at h'
  simp only [Bool.false_or] at h'
  exact solveY_spec p (p^aa) (cpar p aa) q Q (q^bb) (cpar q bb) hp hpq hX hY hqY hc1 hU2
    (cpar_cases q bb) hQ key h'


theorem q_le_qUneg (p q X Y c e Q : ℕ) (hp : 3 ≤ p) (hpq : p < q) (hX : p ≤ X) (hY : q ≤ Y)
    (hU2 : (p+1)^2 ≤ p*X+c) (he1 : q+2 ≤ e) (he2 : e ≤ 2*q+1) (hQ : 1 ≤ Q)
    (key : KeyEq p q X Y c e Q) (hlt : 16*(p+1)^2 < Q*(p*p)) : q ≤ qUneg p Q := by
  have qb := (qbound_nat p q X Y c e Q hp hpq hX hY hU2 he1 he2 hQ key).1
  have hX1 : 1 ≤ X*X := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hpXU : p*X ≤ p*X+c := Nat.le_add_right _ _
  have hUU : (p*X)*(p*X) ≤ (p*X+c)*(p*X+c) := Nat.mul_le_mul hpXU hpXU
  have h1 : 16*(p+1)^2*(X*X) < Q*((p*X+c)*(p*X+c)) := by
    have a1 : 16*(p+1)^2*(X*X) < Q*(p*p)*(X*X) := Nat.mul_lt_mul_of_pos_right hlt (by omega)
    have a2 : Q*(p*p)*(X*X) ≤ Q*((p*X+c)*(p*X+c)) := by
      rw [show Q*(p*p)*(X*X) = Q*((p*X)*(p*X)) by ring]; exact Nat.mul_le_mul_left _ hUU
    omega
  have h2 := qb h1
  have h3 : (Q*(p*p) - 16*(p+1)^2)*(X*X) ≤ Q*((p*X+c)*(p*X+c)) - 16*(p+1)^2*(X*X) := by
    rw [Nat.sub_mul]
    have : Q*(p*p)*(X*X) ≤ Q*((p*X+c)*(p*X+c)) := by
      rw [show Q*(p*p)*(X*X) = Q*((p*X)*(p*X)) by ring]; exact Nat.mul_le_mul_left _ hUU
    omega
  have h4 : q*(Q*(p*p) - 16*(p+1)^2)*(X*X) < 48*(p+1)^2*(X*X) := by
    calc q*(Q*(p*p) - 16*(p+1)^2)*(X*X) = q*((Q*(p*p) - 16*(p+1)^2)*(X*X)) := by ring
      _ ≤ q*(Q*((p*X+c)*(p*X+c)) - 16*(p+1)^2*(X*X)) := Nat.mul_le_mul_left _ h3
      _ < _ := h2
  have h5 := Nat.lt_of_mul_lt_mul_right h4
  unfold qUneg
  rw [Nat.le_div_iff_mul_le (by omega)]
  linarith [Nat.mul_comm q (Q*(p*p) - 16*(p+1)^2)]

theorem bigX_large (p Q X : ℕ) (hp : 3 ≤ p) (hp67 : p ≤ 67) (hQ : Q ≤ 40)
    (hlt : Q*(p*p) < 16*(p+1)^2) (hX : 2000000 < X) : bigX p Q X = true := by
  unfold bigX
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hlt, ?_⟩
  have hE : 1 ≤ 16*(p+1)^2 - Q*(p*p) := by omega
  have a1 : 2*Q*(2*p+1) ≤ 10800 := by
    have : 2*p+1 ≤ 135 := by omega
    calc 2*Q*(2*p+1) ≤ 2*40*135 := Nat.mul_le_mul (by omega) this
      _ = 10800 := by norm_num
  have a2 : 2*p*X+2*p+1 ≤ 135*X := by nlinarith
  calc 2*Q*(2*p+1)*(2*p*X+2*p+1) ≤ 10800*(135*X) := Nat.mul_le_mul a1 a2
    _ ≤ X*X := by nlinarith
    _ = 1*(X*X) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hE

theorem q_le_qUpos (p q X Y c e Q : ℕ) (hp : 3 ≤ p) (hpq : p < q) (hX : p ≤ X) (hY : q ≤ Y)
    (hU2 : (p+1)^2 ≤ p*X+c) (hc2 : c ≤ 2*p+1) (he1 : q+2 ≤ e) (he2 : e ≤ 2*q+1) (hQ : 1 ≤ Q)
    (key : KeyEq p q X Y c e Q) (hb : bigX p Q X = true) : q ≤ qUpos p Q := by
  unfold bigX at hb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨hlt, hbig⟩ := hb
  have qb := (qbound_nat p q X Y c e Q hp hpq hX hY hU2 he1 he2 hQ key).2
  -- integer reasoning
  have hbigZ : (2*(Q:ℤ)*(2*p+1)*(2*p*X+2*p+1)) ≤ (16*((p:ℤ)+1)^2 - Q*(p*p))*(X*X) := by
    have := (Nat.cast_le (α := ℤ)).mpr hbig
    push_cast [hlt.le] at this
    exact this
  have hpZ : (3:ℤ) ≤ p := by exact_mod_cast hp
  have hXZ : (p:ℤ) ≤ X := by exact_mod_cast hX
  have hc2Z : (c:ℤ) ≤ 2*p+1 := by exact_mod_cast hc2
  have hc0 : (0:ℤ) ≤ c := by positivity
  have hQ0 : (0:ℤ) ≤ Q := by positivity
  have hX0 : (0:ℤ) < X := by linarith
  -- Q U^2 ≤ Q p^2 X^2 + Q (2p+1)(2pX+2p+1)
  have hcc : (c:ℤ)*(2*p*X+c) ≤ (2*p+1)*(2*p*X+2*p+1) :=
    mul_le_mul hc2Z (by linarith) (by nlinarith) (by linarith)
  have hQU : (Q:ℤ)*((p*X+c)*(p*X+c)) ≤ Q*(p*p)*(X*X) + Q*((2*p+1)*(2*p*X+2*p+1)) := by
    have := mul_le_mul_of_nonneg_left hcc hQ0
    nlinarith
  -- G ≥ E X^2 / 2 > 0
  have hG : (16*((p:ℤ)+1)^2 - Q*(p*p))*(X*X) ≤ 2*(16*((p:ℤ)+1)^2*(X*X) - Q*((p*X+c)*(p*X+c))) := by
    nlinarith
  have hE : (0:ℤ) < 16*((p:ℤ)+1)^2 - Q*(p*p) := by
    have : ((Q*(p*p) : ℕ) : ℤ) < ((16*(p+1)^2 : ℕ) : ℤ) := by exact_mod_cast hlt
    push_cast at this; linarith
  have hGpos : Q*((p*X+c)*(p*X+c)) < 16*(p+1)^2*(X*X) := by
    have : (0:ℤ) < 16*((p:ℤ)+1)^2*(X*X) - Q*((p*X+c)*(p*X+c)) := by
      have : (0:ℤ) < (16*((p:ℤ)+1)^2 - Q*(p*p))*(X*X) := mul_pos hE (by positivity)
      linarith
    have : ((Q*((p*X+c)*(p*X+c)) : ℕ) : ℤ) < ((16*(p+1)^2*(X*X) : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this
  have h2 := qb hGpos
  have h2Z : (q:ℤ) * (16*((p:ℤ)+1)^2*(X*X) - Q*((p*X+c)*(p*X+c))) ≤ 13*Q*((p*X+c)*(p*X+c)) := by
    have := (Nat.cast_le (α := ℤ)).mpr h2
    push_cast [hGpos.le] at this
    exact this
  -- p U ≤ (p+1)^2 X
  have hpU : (p:ℤ)*(p*X+c) ≤ (p+1)^2*X := by nlinarith
  have hpU2 : ((p:ℤ)*(p*X+c))*((p:ℤ)*(p*X+c)) ≤ ((p+1)^2*X)*((p+1)^2*X) :=
    mul_le_mul hpU hpU (by positivity) (by positivity)
  have hq0 : (0:ℤ) ≤ q := by positivity
  have h3 : (p:ℤ)*p*q*(16*((p:ℤ)+1)^2 - Q*(p*p))*(X*X) ≤ 26*Q*(p+1)^4*(X*X) := by
    have a := mul_le_mul_of_nonneg_left hG (by positivity : (0:ℤ) ≤ p*p*q)
    have b := mul_le_mul_of_nonneg_left h2Z (by positivity : (0:ℤ) ≤ 2*(p*p))
    have c' := mul_le_mul_of_nonneg_left hpU2 (by positivity : (0:ℤ) ≤ 26*Q)
    linear_combination a + b + c'
  have h4 : (p:ℤ)*p*q*(16*((p:ℤ)+1)^2 - Q*(p*p)) ≤ 26*Q*(p+1)^4 :=
    le_of_mul_le_mul_right h3 (by positivity)
  unfold qUpos
  rw [Nat.le_div_iff_mul_le (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))]
  zify [hlt.le]
  linarith

theorem mem_primesTo67 (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ p) (h67 : p ≤ 67) :
    p ∈ primesTo67 := by
  interval_cases p <;> first | decide | (norm_num at hp)

/-- The finite check closes every case with `p ≤ 67`. -/
theorem ppq_finite (p q aa bb Q : ℕ) (hpp : p.Prime) (hp : 3 ≤ p) (hp67 : p ≤ 67) (hpq : p < q)
    (hqo : q % 2 = 1) (ha : 1 ≤ aa) (hb : 1 ≤ bb) (hQ : 1 ≤ Q) (hQ40 : Q ≤ 40)
    (hQp : Q % p ≠ 0) (key : KeyEq p q (p^aa) (q^bb) (cpar p aa) (cpar q bb) Q) : False := by
  obtain ⟨hc1, hc2, hX, hpX, hU2⟩ := cpar_facts p aa hp ha
  obtain ⟨he1, he2, hY, hqY, hV2⟩ := cpar_facts q bb (by omega) hb
  have hok := okP2_of_mem p (mem_primesTo67 p hpp hp hp67)
  unfold okP2 at hok
  rw [List.all_eq_true] at hok
  have hQ' := hok Q (List.mem_range.mpr (by omega))
  have e0 : (Q == 0) = false := by simp; omega
  rw [e0, Bool.false_or] at hQ'
  unfold okPQ2 at hQ'
  have e1 : (Q % p == 0) = false := by simp; omega
  rw [e1, Bool.false_or, Bool.and_eq_true] at hQ'
  obtain ⟨hne, hrest⟩ := hQ'
  simp only [bne_iff_ne, ne_eq] at hne
  split_ifs at hrest with hlt
  · rw [Bool.and_eq_true] at hrest
    obtain ⟨hall, hbb⟩ := hrest
    by_cases hbx : bigX p Q (p^aa) = true
    · have := q_le_qUpos p q (p^aa) (q^bb) (cpar p aa) (cpar q bb) Q hp hpq hX hY hU2 hc2 he1 he2
        hQ key hbx
      exact triple_spec p q aa bb Q hp hpq ha hb hQ key (bigBranch_mem p Q _ q hbb hpq hqo this)
    · have hXB : p^aa ≤ 2000000 := by
        by_contra hc
        exact hbx (bigX_large p Q (p^aa) hp hp67 hQ40 hlt (by omega))
      have := allPow_spec' p 2000000 _ (by omega) hall aa ha hXB
      simp only [Bool.or_eq_true, hbx, Bool.false_eq_true, false_or] at this
      exact smallCheck_spec p q aa bb Q hp hpq hqo ha hb hQ key this
  · have hlt' : 16*(p+1)^2 < Q*(p*p) := by omega
    have := q_le_qUneg p q (p^aa) (q^bb) (cpar p aa) (cpar q bb) Q hp hpq hX hY hU2 he1 he2 hQ key
      hlt'
    exact triple_spec p q aa bb Q hp hpq ha hb hQ key (bigBranch_mem p Q _ q hrest hpq hqo this)


/-- Unconditional: for distinct odd primes `p < q` and exponents `a, b ≥ 1`, `n = p^a q^b` fails
Ordowski's congruence. -/
theorem two_prime_powers_lt (p q aa bb : ℕ) (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2)
    (hpq : p < q) (ha : 1 ≤ aa) (hb : 1 ≤ bb) :
    ¬ (p^aa * q^bb) ^ 2 ≡ 1 [MOD a (p^aa * q^bb) * (a (p^aa * q^bb) - 1)] := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq2 : q ≠ 2 := by omega
  have hqo : q % 2 = 1 := by rcases hq.eq_two_or_odd with h | h; exact absurd h hq2; exact h
  haveI : NeZero (p^aa) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (q^bb) := ⟨pow_ne_zero _ hq.ne_zero⟩
  haveI : NeZero (p^aa * q^bb) := ⟨Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero)⟩
  have hcop : Nat.Coprime (p^aa) (q^bb) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).mpr (by omega))
  have hamul : a (p^aa * q^bb) = a (p^aa) * a (q^bb) := by
    rw [a_eq_aZ, aZ_mul hcop, ← a_eq_aZ, ← a_eq_aZ]
  have hU : 2*(p+1)*a (p^aa) = p*p^aa + cpar p aa := by
    rw [stangl p hp hp2 aa, pow_succ]; unfold cpar; ring
  have hV : 2*(q+1)*a (q^bb) = q*q^bb + cpar q bb := by
    rw [stangl q hq hq2 bb, pow_succ]; unfold cpar; ring
  obtain ⟨hc1, hc2, hX, hpX, hU2⟩ := cpar_facts p aa hp3 ha
  obtain ⟨he1, he2, hY, hqY, hV2⟩ := cpar_facts q bb (by omega) hb
  intro h
  rw [hamul] at h
  have hn1 : 1 ≤ (p^aa * q^bb)^2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne _))
  have hdv := (Nat.modEq_iff_dvd' hn1).mp h.symm
  obtain ⟨X, hXd⟩ : ∃ X, X = p^aa := ⟨_, rfl⟩
  obtain ⟨Y, hYd⟩ : ∃ Y, Y = q^bb := ⟨_, rfl⟩
  obtain ⟨A, hAd⟩ : ∃ A, A = a (p^aa) := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B, B = a (q^bb) := ⟨_, rfl⟩
  rw [← hAd, ← hBd, ← hXd, ← hYd] at hdv
  rw [← hAd, ← hXd] at hU
  rw [← hBd, ← hYd] at hV
  rw [← hXd] at hX hpX hU2
  rw [← hYd] at hY hqY hV2
  have hA1 : 1 ≤ A := by
    rcases Nat.eq_zero_or_pos A with h0 | h0
    · rw [h0] at hU; omega
    · exact h0
  have hB1 : 1 ≤ B := by
    rcases Nat.eq_zero_or_pos B with h0 | h0
    · rw [h0] at hV; omega
    · exact h0
  have hs1 : 1 ≤ A*B := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hn1' : 1 ≤ (X*Y)^2 := by rw [hXd, hYd]; exact hn1
  have hdZ : ((A*B:ℕ):ℤ) * (((A*B:ℕ):ℤ) - 1) ∣ ((X:ℤ)*Y)^2 - 1 := by
    have := Int.natCast_dvd_natCast.mpr hdv
    push_cast [Nat.cast_sub hs1, Nat.cast_sub hn1'] at this
    push_cast
    exact this
  obtain ⟨Q, hQ⟩ := hdZ
  have hUZ : (p:ℤ)*X + cpar p aa = 2*((p:ℤ)+1)*A := by exact_mod_cast hU.symm
  have hVZ : (q:ℤ)*Y + cpar q bb = 2*((q:ℤ)+1)*B := by exact_mod_cast hV.symm
  have hpZ : (3:ℤ) ≤ p := by exact_mod_cast hp3
  have hpqZ : (p:ℤ) < q := by exact_mod_cast hpq
  have hXZ : (p:ℤ) ≤ X := by exact_mod_cast hX
  have hYZ : (q:ℤ) ≤ Y := by exact_mod_cast hY
  have hX0 : (0:ℤ) < X := by linarith
  have hY0 : (0:ℤ) < Y := by linarith
  have hs1Z : (1:ℤ) ≤ (A:ℤ)*B := by exact_mod_cast hs1
  have hQpos : 1 ≤ Q := by
    by_contra hc; push Not at hc
    have h0 : 0 ≤ (A:ℤ)*B*((A:ℤ)*B - 1) := mul_nonneg (by linarith) (by linarith)
    have : (A:ℤ)*B*((A:ℤ)*B - 1)*Q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h0 (by omega)
    have hX3 : (3:ℤ) ≤ X := by linarith
    have hY3 : (3:ℤ) ≤ Y := by linarith
    have hXY : (3:ℤ)*3 ≤ X*Y := mul_le_mul hX3 hY3 (by norm_num) (by linarith)
    have h81 : (9:ℤ)*9 ≤ (X*Y)*(X*Y) := mul_le_mul hXY hXY (by norm_num) (by linarith)
    push_cast at hQ
    have : ((X:ℤ)*Y)^2 - 1 ≤ 0 := by rw [hQ]; exact this
    nlinarith only [this, h81]
  lift Q to ℕ using (by omega)
  have key : KeyEq p q X Y (cpar p aa) (cpar q bb) Q := by
    unfold KeyEq
    rw [hUZ, hVZ]
    push_cast at hQ
    linear_combination (-(4*((p:ℤ)+1)*((q:ℤ)+1))^2) * hQ
  have keyZ := key
  unfold KeyEq at keyZ
  have hc1Z : (p:ℤ)+2 ≤ cpar p aa := by exact_mod_cast hc1
  have he1Z : (q:ℤ)+2 ≤ cpar q bb := by exact_mod_cast he1
  have hKM := KM_lt _ _ _ _ _ _ _ hpZ hpqZ hXZ hYZ hc1Z he1Z (by positivity) keyZ
  have hq5 : (5:ℤ) ≤ q := by exact_mod_cast (show 5 ≤ q by omega)
  have hQ40 : (Q:ℤ) ≤ 40 := Q_le_40 _ _ _ hpZ hpqZ hq5 hKM
  have hQp : Q % p ≠ 0 := by
    intro hc
    have hpQ : (p:ℤ) ∣ (Q:ℤ) := Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero hc)
    have h1 : (p:ℤ) ∣ ((X:ℤ)*Y)^2 - 1 := by
      rw [hQ]; exact Dvd.dvd.mul_left hpQ _
    have h2 : (p:ℤ) ∣ ((X:ℤ)*Y)^2 := by
      have : (p:ℤ) ∣ (X:ℤ) := Int.natCast_dvd_natCast.mpr hpX
      exact Dvd.dvd.pow (Dvd.dvd.mul_right this _) (by norm_num)
    have h3 : (p:ℤ) ∣ 1 := by
      have := dvd_sub h2 h1
      simpa using this
    have : p ∣ 1 := by exact_mod_cast h3
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hp67 : p ≤ 67 := by
    by_contra hc; push Not at hc
    by_cases h71 : 71 ≤ p
    · apply core_large (p:ℤ) q X Y (cpar p aa) (cpar q bb) Q (A*B : ℕ) (by exact_mod_cast h71) hpqZ
        hXZ hYZ (by positivity) (by exact_mod_cast hc2) (by positivity) (by exact_mod_cast he2)
      · rw [hUZ, hVZ]; push_cast; ring
      · push_cast at hQ ⊢; linear_combination -hQ
    · interval_cases p <;> norm_num at hp
  subst hXd hYd
  exact ppq_finite p q aa bb Q hp hp3 hp67 hpq hqo ha hb (by exact_mod_cast hQpos)
    (by exact_mod_cast hQ40) hQp key

/-- `two_prime_powers_lt` without an ordering assumption. -/
theorem two_prime_powers_case (p q aa bb : ℕ) (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (hpq : p ≠ q) (ha : 1 ≤ aa) (hb : 1 ≤ bb) :
    ¬ (p^aa * q^bb) ^ 2 ≡ 1 [MOD a (p^aa * q^bb) * (a (p^aa * q^bb) - 1)] := by
  rcases Nat.lt_or_gt_of_ne hpq with h | h
  · exact two_prime_powers_lt p q aa bb hp hq hp2 h ha hb
  · rw [mul_comm (p^aa)]; exact two_prime_powers_lt q p bb aa hq hp hq2 h hb ha

/-- Main theorem (extended): Ordowski's conjecture holds for every `n > 1` that is even, an odd
prime power, a product of three distinct odd primes, or of the form `p^a q^b` with `p ≠ q` odd
primes and `a, b ≥ 1`. -/
theorem conjecture_main_ppq (n : ℕ) (hn : 1 < n)
    (hcase : Even n ∨ (∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ n = p ^ k) ∨
      (∃ p q a b : ℕ, p.Prime ∧ q.Prime ∧ p ≠ 2 ∧ q ≠ 2 ∧ p ≠ q ∧ 1 ≤ a ∧ 1 ≤ b ∧
        n = p ^ a * q ^ b) ∨
      ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p ≠ 2 ∧ q ≠ 2 ∧ r ≠ 2 ∧
        p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ n = p * q * r) :
    (n.Prime ∧ n ≠ 2) ↔ n ^ 2 ≡ 1 [MOD a n * (a n - 1)] := by
  rcases hcase with h | h | ⟨p, q, a', b', hp, hq, hp2, hq2, hpq, ha, hb, rfl⟩ | h
  · exact conjecture_main_three n hn (Or.inl h)
  · exact conjecture_main_three n hn (Or.inr (Or.inl h))
  · constructor
    · rintro ⟨hpr, -⟩
      exfalso
      have h1 : 1 < p^a' := Nat.one_lt_pow (by omega) hp.one_lt
      have h2 : 1 < q^b' := Nat.one_lt_pow (by omega) hq.one_lt
      exact Nat.not_prime_mul (by omega) (by omega) hpr
    · intro h; exact absurd h (two_prime_powers_case p q a' b' hp hq hp2 hq2 hpq ha hb)
  · exact conjecture_main_three n hn (Or.inr (Or.inr (Or.inr h)))

end OeisA224
