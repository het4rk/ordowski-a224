import OrdowskiA224.FiniteCheckPQ

/-! Kernel check for p = 43 (one theorem per Q). -/

namespace OeisA224

theorem okPQ2_43_1 : okPQ2 43 1 = true := by decide +kernel
theorem okPQ2_43_2 : okPQ2 43 2 = true := by decide +kernel
theorem okPQ2_43_3 : okPQ2 43 3 = true := by decide +kernel
theorem okPQ2_43_4 : okPQ2 43 4 = true := by decide +kernel
theorem okPQ2_43_5 : okPQ2 43 5 = true := by decide +kernel
theorem okPQ2_43_6 : okPQ2 43 6 = true := by decide +kernel
theorem okPQ2_43_7 : okPQ2 43 7 = true := by decide +kernel
theorem okPQ2_43_8 : okPQ2 43 8 = true := by decide +kernel
theorem okPQ2_43_9 : okPQ2 43 9 = true := by decide +kernel
theorem okPQ2_43_10 : okPQ2 43 10 = true := by decide +kernel
theorem okPQ2_43_11 : okPQ2 43 11 = true := by decide +kernel
theorem okPQ2_43_12 : okPQ2 43 12 = true := by decide +kernel
theorem okPQ2_43_13 : okPQ2 43 13 = true := by decide +kernel
theorem okPQ2_43_14 : okPQ2 43 14 = true := by decide +kernel
theorem okPQ2_43_15 : okPQ2 43 15 = true := by decide +kernel
theorem okPQ2_43_16 : okPQ2 43 16 = true := by decide +kernel
theorem okPQ2_43_17 : okPQ2 43 17 = true := by decide +kernel
theorem okPQ2_43_18 : okPQ2 43 18 = true := by decide +kernel
theorem okPQ2_43_19 : okPQ2 43 19 = true := by decide +kernel
theorem okPQ2_43_20 : okPQ2 43 20 = true := by decide +kernel
theorem okPQ2_43_21 : okPQ2 43 21 = true := by decide +kernel
theorem okPQ2_43_22 : okPQ2 43 22 = true := by decide +kernel
theorem okPQ2_43_23 : okPQ2 43 23 = true := by decide +kernel
theorem okPQ2_43_24 : okPQ2 43 24 = true := by decide +kernel
theorem okPQ2_43_25 : okPQ2 43 25 = true := by decide +kernel
theorem okPQ2_43_26 : okPQ2 43 26 = true := by decide +kernel
theorem okPQ2_43_27 : okPQ2 43 27 = true := by decide +kernel
theorem okPQ2_43_28 : okPQ2 43 28 = true := by decide +kernel
theorem okPQ2_43_29 : okPQ2 43 29 = true := by decide +kernel
theorem okPQ2_43_30 : okPQ2 43 30 = true := by decide +kernel
theorem okPQ2_43_31 : okPQ2 43 31 = true := by decide +kernel
theorem okPQ2_43_32 : okPQ2 43 32 = true := by decide +kernel
theorem okPQ2_43_33 : okPQ2 43 33 = true := by decide +kernel
theorem okPQ2_43_34 : okPQ2 43 34 = true := by decide +kernel
theorem okPQ2_43_35 : okPQ2 43 35 = true := by decide +kernel
theorem okPQ2_43_36 : okPQ2 43 36 = true := by decide +kernel
theorem okPQ2_43_37 : okPQ2 43 37 = true := by decide +kernel
theorem okPQ2_43_38 : okPQ2 43 38 = true := by decide +kernel
theorem okPQ2_43_39 : okPQ2 43 39 = true := by decide +kernel
theorem okPQ2_43_40 : okPQ2 43 40 = true := by decide +kernel

theorem okP2_43 : okP2 43 = true := by
  unfold okP2
  rw [List.all_eq_true]
  intro Q hQ
  rw [List.mem_range] at hQ
  simp only [Bool.or_eq_true, beq_iff_eq]
  interval_cases Q
  · left; rfl
  · right; exact okPQ2_43_1
  · right; exact okPQ2_43_2
  · right; exact okPQ2_43_3
  · right; exact okPQ2_43_4
  · right; exact okPQ2_43_5
  · right; exact okPQ2_43_6
  · right; exact okPQ2_43_7
  · right; exact okPQ2_43_8
  · right; exact okPQ2_43_9
  · right; exact okPQ2_43_10
  · right; exact okPQ2_43_11
  · right; exact okPQ2_43_12
  · right; exact okPQ2_43_13
  · right; exact okPQ2_43_14
  · right; exact okPQ2_43_15
  · right; exact okPQ2_43_16
  · right; exact okPQ2_43_17
  · right; exact okPQ2_43_18
  · right; exact okPQ2_43_19
  · right; exact okPQ2_43_20
  · right; exact okPQ2_43_21
  · right; exact okPQ2_43_22
  · right; exact okPQ2_43_23
  · right; exact okPQ2_43_24
  · right; exact okPQ2_43_25
  · right; exact okPQ2_43_26
  · right; exact okPQ2_43_27
  · right; exact okPQ2_43_28
  · right; exact okPQ2_43_29
  · right; exact okPQ2_43_30
  · right; exact okPQ2_43_31
  · right; exact okPQ2_43_32
  · right; exact okPQ2_43_33
  · right; exact okPQ2_43_34
  · right; exact okPQ2_43_35
  · right; exact okPQ2_43_36
  · right; exact okPQ2_43_37
  · right; exact okPQ2_43_38
  · right; exact okPQ2_43_39
  · right; exact okPQ2_43_40

end OeisA224
