import OrdowskiA224.FiniteCheckPQ

/-! Kernel check for p = 3 (one theorem per Q). -/

namespace OeisA224

theorem okPQ2_3_1 : okPQ2 3 1 = true := by decide +kernel
theorem okPQ2_3_2 : okPQ2 3 2 = true := by decide +kernel
theorem okPQ2_3_3 : okPQ2 3 3 = true := by decide +kernel
theorem okPQ2_3_4 : okPQ2 3 4 = true := by decide +kernel
theorem okPQ2_3_5 : okPQ2 3 5 = true := by decide +kernel
theorem okPQ2_3_6 : okPQ2 3 6 = true := by decide +kernel
theorem okPQ2_3_7 : okPQ2 3 7 = true := by decide +kernel
theorem okPQ2_3_8 : okPQ2 3 8 = true := by decide +kernel
theorem okPQ2_3_9 : okPQ2 3 9 = true := by decide +kernel
theorem okPQ2_3_10 : okPQ2 3 10 = true := by decide +kernel
theorem okPQ2_3_11 : okPQ2 3 11 = true := by decide +kernel
theorem okPQ2_3_12 : okPQ2 3 12 = true := by decide +kernel
theorem okPQ2_3_13 : okPQ2 3 13 = true := by decide +kernel
theorem okPQ2_3_14 : okPQ2 3 14 = true := by decide +kernel
theorem okPQ2_3_15 : okPQ2 3 15 = true := by decide +kernel
theorem okPQ2_3_16 : okPQ2 3 16 = true := by decide +kernel
theorem okPQ2_3_17 : okPQ2 3 17 = true := by decide +kernel
theorem okPQ2_3_18 : okPQ2 3 18 = true := by decide +kernel
theorem okPQ2_3_19 : okPQ2 3 19 = true := by decide +kernel
theorem okPQ2_3_20 : okPQ2 3 20 = true := by decide +kernel
theorem okPQ2_3_21 : okPQ2 3 21 = true := by decide +kernel
theorem okPQ2_3_22 : okPQ2 3 22 = true := by decide +kernel
theorem okPQ2_3_23 : okPQ2 3 23 = true := by decide +kernel
theorem okPQ2_3_24 : okPQ2 3 24 = true := by decide +kernel
theorem okPQ2_3_25 : okPQ2 3 25 = true := by decide +kernel
theorem okPQ2_3_26 : okPQ2 3 26 = true := by decide +kernel
theorem okPQ2_3_27 : okPQ2 3 27 = true := by decide +kernel
theorem okPQ2_3_28 : okPQ2 3 28 = true := by decide +kernel
theorem okPQ2_3_29 : okPQ2 3 29 = true := by decide +kernel
theorem okPQ2_3_30 : okPQ2 3 30 = true := by decide +kernel
theorem okPQ2_3_31 : okPQ2 3 31 = true := by decide +kernel
theorem okPQ2_3_32 : okPQ2 3 32 = true := by decide +kernel
theorem okPQ2_3_33 : okPQ2 3 33 = true := by decide +kernel
theorem okPQ2_3_34 : okPQ2 3 34 = true := by decide +kernel
theorem okPQ2_3_35 : okPQ2 3 35 = true := by decide +kernel
theorem okPQ2_3_36 : okPQ2 3 36 = true := by decide +kernel
theorem okPQ2_3_37 : okPQ2 3 37 = true := by decide +kernel
theorem okPQ2_3_38 : okPQ2 3 38 = true := by decide +kernel
theorem okPQ2_3_39 : okPQ2 3 39 = true := by decide +kernel
theorem okPQ2_3_40 : okPQ2 3 40 = true := by decide +kernel

theorem okP2_3 : okP2 3 = true := by
  unfold okP2
  rw [List.all_eq_true]
  intro Q hQ
  rw [List.mem_range] at hQ
  simp only [Bool.or_eq_true, beq_iff_eq]
  interval_cases Q
  · left; rfl
  · right; exact okPQ2_3_1
  · right; exact okPQ2_3_2
  · right; exact okPQ2_3_3
  · right; exact okPQ2_3_4
  · right; exact okPQ2_3_5
  · right; exact okPQ2_3_6
  · right; exact okPQ2_3_7
  · right; exact okPQ2_3_8
  · right; exact okPQ2_3_9
  · right; exact okPQ2_3_10
  · right; exact okPQ2_3_11
  · right; exact okPQ2_3_12
  · right; exact okPQ2_3_13
  · right; exact okPQ2_3_14
  · right; exact okPQ2_3_15
  · right; exact okPQ2_3_16
  · right; exact okPQ2_3_17
  · right; exact okPQ2_3_18
  · right; exact okPQ2_3_19
  · right; exact okPQ2_3_20
  · right; exact okPQ2_3_21
  · right; exact okPQ2_3_22
  · right; exact okPQ2_3_23
  · right; exact okPQ2_3_24
  · right; exact okPQ2_3_25
  · right; exact okPQ2_3_26
  · right; exact okPQ2_3_27
  · right; exact okPQ2_3_28
  · right; exact okPQ2_3_29
  · right; exact okPQ2_3_30
  · right; exact okPQ2_3_31
  · right; exact okPQ2_3_32
  · right; exact okPQ2_3_33
  · right; exact okPQ2_3_34
  · right; exact okPQ2_3_35
  · right; exact okPQ2_3_36
  · right; exact okPQ2_3_37
  · right; exact okPQ2_3_38
  · right; exact okPQ2_3_39
  · right; exact okPQ2_3_40

end OeisA224
