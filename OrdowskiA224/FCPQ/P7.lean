import OrdowskiA224.FiniteCheckPQ

/-! Kernel check for p = 7 (one theorem per Q). -/

namespace OeisA224

theorem okPQ2_7_1 : okPQ2 7 1 = true := by decide +kernel
theorem okPQ2_7_2 : okPQ2 7 2 = true := by decide +kernel
theorem okPQ2_7_3 : okPQ2 7 3 = true := by decide +kernel
theorem okPQ2_7_4 : okPQ2 7 4 = true := by decide +kernel
theorem okPQ2_7_5 : okPQ2 7 5 = true := by decide +kernel
theorem okPQ2_7_6 : okPQ2 7 6 = true := by decide +kernel
theorem okPQ2_7_7 : okPQ2 7 7 = true := by decide +kernel
theorem okPQ2_7_8 : okPQ2 7 8 = true := by decide +kernel
theorem okPQ2_7_9 : okPQ2 7 9 = true := by decide +kernel
theorem okPQ2_7_10 : okPQ2 7 10 = true := by decide +kernel
theorem okPQ2_7_11 : okPQ2 7 11 = true := by decide +kernel
theorem okPQ2_7_12 : okPQ2 7 12 = true := by decide +kernel
theorem okPQ2_7_13 : okPQ2 7 13 = true := by decide +kernel
theorem okPQ2_7_14 : okPQ2 7 14 = true := by decide +kernel
theorem okPQ2_7_15 : okPQ2 7 15 = true := by decide +kernel
theorem okPQ2_7_16 : okPQ2 7 16 = true := by decide +kernel
theorem okPQ2_7_17 : okPQ2 7 17 = true := by decide +kernel
theorem okPQ2_7_18 : okPQ2 7 18 = true := by decide +kernel
theorem okPQ2_7_19 : okPQ2 7 19 = true := by decide +kernel
theorem okPQ2_7_20 : okPQ2 7 20 = true := by decide +kernel
theorem okPQ2_7_21 : okPQ2 7 21 = true := by decide +kernel
theorem okPQ2_7_22 : okPQ2 7 22 = true := by decide +kernel
theorem okPQ2_7_23 : okPQ2 7 23 = true := by decide +kernel
theorem okPQ2_7_24 : okPQ2 7 24 = true := by decide +kernel
theorem okPQ2_7_25 : okPQ2 7 25 = true := by decide +kernel
theorem okPQ2_7_26 : okPQ2 7 26 = true := by decide +kernel
theorem okPQ2_7_27 : okPQ2 7 27 = true := by decide +kernel
theorem okPQ2_7_28 : okPQ2 7 28 = true := by decide +kernel
theorem okPQ2_7_29 : okPQ2 7 29 = true := by decide +kernel
theorem okPQ2_7_30 : okPQ2 7 30 = true := by decide +kernel
theorem okPQ2_7_31 : okPQ2 7 31 = true := by decide +kernel
theorem okPQ2_7_32 : okPQ2 7 32 = true := by decide +kernel
theorem okPQ2_7_33 : okPQ2 7 33 = true := by decide +kernel
theorem okPQ2_7_34 : okPQ2 7 34 = true := by decide +kernel
theorem okPQ2_7_35 : okPQ2 7 35 = true := by decide +kernel
theorem okPQ2_7_36 : okPQ2 7 36 = true := by decide +kernel
theorem okPQ2_7_37 : okPQ2 7 37 = true := by decide +kernel
theorem okPQ2_7_38 : okPQ2 7 38 = true := by decide +kernel
theorem okPQ2_7_39 : okPQ2 7 39 = true := by decide +kernel
theorem okPQ2_7_40 : okPQ2 7 40 = true := by decide +kernel

theorem okP2_7 : okP2 7 = true := by
  unfold okP2
  rw [List.all_eq_true]
  intro Q hQ
  rw [List.mem_range] at hQ
  simp only [Bool.or_eq_true, beq_iff_eq]
  interval_cases Q
  · left; rfl
  · right; exact okPQ2_7_1
  · right; exact okPQ2_7_2
  · right; exact okPQ2_7_3
  · right; exact okPQ2_7_4
  · right; exact okPQ2_7_5
  · right; exact okPQ2_7_6
  · right; exact okPQ2_7_7
  · right; exact okPQ2_7_8
  · right; exact okPQ2_7_9
  · right; exact okPQ2_7_10
  · right; exact okPQ2_7_11
  · right; exact okPQ2_7_12
  · right; exact okPQ2_7_13
  · right; exact okPQ2_7_14
  · right; exact okPQ2_7_15
  · right; exact okPQ2_7_16
  · right; exact okPQ2_7_17
  · right; exact okPQ2_7_18
  · right; exact okPQ2_7_19
  · right; exact okPQ2_7_20
  · right; exact okPQ2_7_21
  · right; exact okPQ2_7_22
  · right; exact okPQ2_7_23
  · right; exact okPQ2_7_24
  · right; exact okPQ2_7_25
  · right; exact okPQ2_7_26
  · right; exact okPQ2_7_27
  · right; exact okPQ2_7_28
  · right; exact okPQ2_7_29
  · right; exact okPQ2_7_30
  · right; exact okPQ2_7_31
  · right; exact okPQ2_7_32
  · right; exact okPQ2_7_33
  · right; exact okPQ2_7_34
  · right; exact okPQ2_7_35
  · right; exact okPQ2_7_36
  · right; exact okPQ2_7_37
  · right; exact okPQ2_7_38
  · right; exact okPQ2_7_39
  · right; exact okPQ2_7_40

end OeisA224
