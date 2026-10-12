import OrdowskiA224.FiniteCheckPQ

/-! Kernel check for p = 11 (one theorem per Q). -/

namespace OeisA224

theorem okPQ2_11_1 : okPQ2 11 1 = true := by decide +kernel
theorem okPQ2_11_2 : okPQ2 11 2 = true := by decide +kernel
theorem okPQ2_11_3 : okPQ2 11 3 = true := by decide +kernel
theorem okPQ2_11_4 : okPQ2 11 4 = true := by decide +kernel
theorem okPQ2_11_5 : okPQ2 11 5 = true := by decide +kernel
theorem okPQ2_11_6 : okPQ2 11 6 = true := by decide +kernel
theorem okPQ2_11_7 : okPQ2 11 7 = true := by decide +kernel
theorem okPQ2_11_8 : okPQ2 11 8 = true := by decide +kernel
theorem okPQ2_11_9 : okPQ2 11 9 = true := by decide +kernel
theorem okPQ2_11_10 : okPQ2 11 10 = true := by decide +kernel
theorem okPQ2_11_11 : okPQ2 11 11 = true := by decide +kernel
theorem okPQ2_11_12 : okPQ2 11 12 = true := by decide +kernel
theorem okPQ2_11_13 : okPQ2 11 13 = true := by decide +kernel
theorem okPQ2_11_14 : okPQ2 11 14 = true := by decide +kernel
theorem okPQ2_11_15 : okPQ2 11 15 = true := by decide +kernel
theorem okPQ2_11_16 : okPQ2 11 16 = true := by decide +kernel
theorem okPQ2_11_17 : okPQ2 11 17 = true := by decide +kernel
theorem okPQ2_11_18 : okPQ2 11 18 = true := by decide +kernel
theorem okPQ2_11_19 : okPQ2 11 19 = true := by decide +kernel
theorem okPQ2_11_20 : okPQ2 11 20 = true := by decide +kernel
theorem okPQ2_11_21 : okPQ2 11 21 = true := by decide +kernel
theorem okPQ2_11_22 : okPQ2 11 22 = true := by decide +kernel
theorem okPQ2_11_23 : okPQ2 11 23 = true := by decide +kernel
theorem okPQ2_11_24 : okPQ2 11 24 = true := by decide +kernel
theorem okPQ2_11_25 : okPQ2 11 25 = true := by decide +kernel
theorem okPQ2_11_26 : okPQ2 11 26 = true := by decide +kernel
theorem okPQ2_11_27 : okPQ2 11 27 = true := by decide +kernel
theorem okPQ2_11_28 : okPQ2 11 28 = true := by decide +kernel
theorem okPQ2_11_29 : okPQ2 11 29 = true := by decide +kernel
theorem okPQ2_11_30 : okPQ2 11 30 = true := by decide +kernel
theorem okPQ2_11_31 : okPQ2 11 31 = true := by decide +kernel
theorem okPQ2_11_32 : okPQ2 11 32 = true := by decide +kernel
theorem okPQ2_11_33 : okPQ2 11 33 = true := by decide +kernel
theorem okPQ2_11_34 : okPQ2 11 34 = true := by decide +kernel
theorem okPQ2_11_35 : okPQ2 11 35 = true := by decide +kernel
theorem okPQ2_11_36 : okPQ2 11 36 = true := by decide +kernel
theorem okPQ2_11_37 : okPQ2 11 37 = true := by decide +kernel
theorem okPQ2_11_38 : okPQ2 11 38 = true := by decide +kernel
theorem okPQ2_11_39 : okPQ2 11 39 = true := by decide +kernel
theorem okPQ2_11_40 : okPQ2 11 40 = true := by decide +kernel

theorem okP2_11 : okP2 11 = true := by
  unfold okP2
  rw [List.all_eq_true]
  intro Q hQ
  rw [List.mem_range] at hQ
  simp only [Bool.or_eq_true, beq_iff_eq]
  interval_cases Q
  · left; rfl
  · right; exact okPQ2_11_1
  · right; exact okPQ2_11_2
  · right; exact okPQ2_11_3
  · right; exact okPQ2_11_4
  · right; exact okPQ2_11_5
  · right; exact okPQ2_11_6
  · right; exact okPQ2_11_7
  · right; exact okPQ2_11_8
  · right; exact okPQ2_11_9
  · right; exact okPQ2_11_10
  · right; exact okPQ2_11_11
  · right; exact okPQ2_11_12
  · right; exact okPQ2_11_13
  · right; exact okPQ2_11_14
  · right; exact okPQ2_11_15
  · right; exact okPQ2_11_16
  · right; exact okPQ2_11_17
  · right; exact okPQ2_11_18
  · right; exact okPQ2_11_19
  · right; exact okPQ2_11_20
  · right; exact okPQ2_11_21
  · right; exact okPQ2_11_22
  · right; exact okPQ2_11_23
  · right; exact okPQ2_11_24
  · right; exact okPQ2_11_25
  · right; exact okPQ2_11_26
  · right; exact okPQ2_11_27
  · right; exact okPQ2_11_28
  · right; exact okPQ2_11_29
  · right; exact okPQ2_11_30
  · right; exact okPQ2_11_31
  · right; exact okPQ2_11_32
  · right; exact okPQ2_11_33
  · right; exact okPQ2_11_34
  · right; exact okPQ2_11_35
  · right; exact okPQ2_11_36
  · right; exact okPQ2_11_37
  · right; exact okPQ2_11_38
  · right; exact okPQ2_11_39
  · right; exact okPQ2_11_40

end OeisA224
