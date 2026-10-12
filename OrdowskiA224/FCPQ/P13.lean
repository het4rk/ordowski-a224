import OrdowskiA224.FiniteCheckPQ

/-! Kernel check for p = 13 (one theorem per Q). -/

namespace OeisA224

theorem okPQ2_13_1 : okPQ2 13 1 = true := by decide +kernel
theorem okPQ2_13_2 : okPQ2 13 2 = true := by decide +kernel
theorem okPQ2_13_3 : okPQ2 13 3 = true := by decide +kernel
theorem okPQ2_13_4 : okPQ2 13 4 = true := by decide +kernel
theorem okPQ2_13_5 : okPQ2 13 5 = true := by decide +kernel
theorem okPQ2_13_6 : okPQ2 13 6 = true := by decide +kernel
theorem okPQ2_13_7 : okPQ2 13 7 = true := by decide +kernel
theorem okPQ2_13_8 : okPQ2 13 8 = true := by decide +kernel
theorem okPQ2_13_9 : okPQ2 13 9 = true := by decide +kernel
theorem okPQ2_13_10 : okPQ2 13 10 = true := by decide +kernel
theorem okPQ2_13_11 : okPQ2 13 11 = true := by decide +kernel
theorem okPQ2_13_12 : okPQ2 13 12 = true := by decide +kernel
theorem okPQ2_13_13 : okPQ2 13 13 = true := by decide +kernel
theorem okPQ2_13_14 : okPQ2 13 14 = true := by decide +kernel
theorem okPQ2_13_15 : okPQ2 13 15 = true := by decide +kernel
theorem okPQ2_13_16 : okPQ2 13 16 = true := by decide +kernel
theorem okPQ2_13_17 : okPQ2 13 17 = true := by decide +kernel
theorem okPQ2_13_18 : okPQ2 13 18 = true := by decide +kernel
theorem okPQ2_13_19 : okPQ2 13 19 = true := by decide +kernel
theorem okPQ2_13_20 : okPQ2 13 20 = true := by decide +kernel
theorem okPQ2_13_21 : okPQ2 13 21 = true := by decide +kernel
theorem okPQ2_13_22 : okPQ2 13 22 = true := by decide +kernel
theorem okPQ2_13_23 : okPQ2 13 23 = true := by decide +kernel
theorem okPQ2_13_24 : okPQ2 13 24 = true := by decide +kernel
theorem okPQ2_13_25 : okPQ2 13 25 = true := by decide +kernel
theorem okPQ2_13_26 : okPQ2 13 26 = true := by decide +kernel
theorem okPQ2_13_27 : okPQ2 13 27 = true := by decide +kernel
theorem okPQ2_13_28 : okPQ2 13 28 = true := by decide +kernel
theorem okPQ2_13_29 : okPQ2 13 29 = true := by decide +kernel
theorem okPQ2_13_30 : okPQ2 13 30 = true := by decide +kernel
theorem okPQ2_13_31 : okPQ2 13 31 = true := by decide +kernel
theorem okPQ2_13_32 : okPQ2 13 32 = true := by decide +kernel
theorem okPQ2_13_33 : okPQ2 13 33 = true := by decide +kernel
theorem okPQ2_13_34 : okPQ2 13 34 = true := by decide +kernel
theorem okPQ2_13_35 : okPQ2 13 35 = true := by decide +kernel
theorem okPQ2_13_36 : okPQ2 13 36 = true := by decide +kernel
theorem okPQ2_13_37 : okPQ2 13 37 = true := by decide +kernel
theorem okPQ2_13_38 : okPQ2 13 38 = true := by decide +kernel
theorem okPQ2_13_39 : okPQ2 13 39 = true := by decide +kernel
theorem okPQ2_13_40 : okPQ2 13 40 = true := by decide +kernel

theorem okP2_13 : okP2 13 = true := by
  unfold okP2
  rw [List.all_eq_true]
  intro Q hQ
  rw [List.mem_range] at hQ
  simp only [Bool.or_eq_true, beq_iff_eq]
  interval_cases Q
  · left; rfl
  · right; exact okPQ2_13_1
  · right; exact okPQ2_13_2
  · right; exact okPQ2_13_3
  · right; exact okPQ2_13_4
  · right; exact okPQ2_13_5
  · right; exact okPQ2_13_6
  · right; exact okPQ2_13_7
  · right; exact okPQ2_13_8
  · right; exact okPQ2_13_9
  · right; exact okPQ2_13_10
  · right; exact okPQ2_13_11
  · right; exact okPQ2_13_12
  · right; exact okPQ2_13_13
  · right; exact okPQ2_13_14
  · right; exact okPQ2_13_15
  · right; exact okPQ2_13_16
  · right; exact okPQ2_13_17
  · right; exact okPQ2_13_18
  · right; exact okPQ2_13_19
  · right; exact okPQ2_13_20
  · right; exact okPQ2_13_21
  · right; exact okPQ2_13_22
  · right; exact okPQ2_13_23
  · right; exact okPQ2_13_24
  · right; exact okPQ2_13_25
  · right; exact okPQ2_13_26
  · right; exact okPQ2_13_27
  · right; exact okPQ2_13_28
  · right; exact okPQ2_13_29
  · right; exact okPQ2_13_30
  · right; exact okPQ2_13_31
  · right; exact okPQ2_13_32
  · right; exact okPQ2_13_33
  · right; exact okPQ2_13_34
  · right; exact okPQ2_13_35
  · right; exact okPQ2_13_36
  · right; exact okPQ2_13_37
  · right; exact okPQ2_13_38
  · right; exact okPQ2_13_39
  · right; exact okPQ2_13_40

end OeisA224
