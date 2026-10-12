import OrdowskiA224.FiniteCheckPQ

/-! Kernel check for p = 67 (one theorem per Q). -/

namespace OeisA224

theorem okPQ2_67_1 : okPQ2 67 1 = true := by decide +kernel
theorem okPQ2_67_2 : okPQ2 67 2 = true := by decide +kernel
theorem okPQ2_67_3 : okPQ2 67 3 = true := by decide +kernel
theorem okPQ2_67_4 : okPQ2 67 4 = true := by decide +kernel
theorem okPQ2_67_5 : okPQ2 67 5 = true := by decide +kernel
theorem okPQ2_67_6 : okPQ2 67 6 = true := by decide +kernel
theorem okPQ2_67_7 : okPQ2 67 7 = true := by decide +kernel
theorem okPQ2_67_8 : okPQ2 67 8 = true := by decide +kernel
theorem okPQ2_67_9 : okPQ2 67 9 = true := by decide +kernel
theorem okPQ2_67_10 : okPQ2 67 10 = true := by decide +kernel
theorem okPQ2_67_11 : okPQ2 67 11 = true := by decide +kernel
theorem okPQ2_67_12 : okPQ2 67 12 = true := by decide +kernel
theorem okPQ2_67_13 : okPQ2 67 13 = true := by decide +kernel
theorem okPQ2_67_14 : okPQ2 67 14 = true := by decide +kernel
theorem okPQ2_67_15 : okPQ2 67 15 = true := by decide +kernel
theorem okPQ2_67_16 : okPQ2 67 16 = true := by decide +kernel
theorem okPQ2_67_17 : okPQ2 67 17 = true := by decide +kernel
theorem okPQ2_67_18 : okPQ2 67 18 = true := by decide +kernel
theorem okPQ2_67_19 : okPQ2 67 19 = true := by decide +kernel
theorem okPQ2_67_20 : okPQ2 67 20 = true := by decide +kernel
theorem okPQ2_67_21 : okPQ2 67 21 = true := by decide +kernel
theorem okPQ2_67_22 : okPQ2 67 22 = true := by decide +kernel
theorem okPQ2_67_23 : okPQ2 67 23 = true := by decide +kernel
theorem okPQ2_67_24 : okPQ2 67 24 = true := by decide +kernel
theorem okPQ2_67_25 : okPQ2 67 25 = true := by decide +kernel
theorem okPQ2_67_26 : okPQ2 67 26 = true := by decide +kernel
theorem okPQ2_67_27 : okPQ2 67 27 = true := by decide +kernel
theorem okPQ2_67_28 : okPQ2 67 28 = true := by decide +kernel
theorem okPQ2_67_29 : okPQ2 67 29 = true := by decide +kernel
theorem okPQ2_67_30 : okPQ2 67 30 = true := by decide +kernel
theorem okPQ2_67_31 : okPQ2 67 31 = true := by decide +kernel
theorem okPQ2_67_32 : okPQ2 67 32 = true := by decide +kernel
theorem okPQ2_67_33 : okPQ2 67 33 = true := by decide +kernel
theorem okPQ2_67_34 : okPQ2 67 34 = true := by decide +kernel
theorem okPQ2_67_35 : okPQ2 67 35 = true := by decide +kernel
theorem okPQ2_67_36 : okPQ2 67 36 = true := by decide +kernel
theorem okPQ2_67_37 : okPQ2 67 37 = true := by decide +kernel
theorem okPQ2_67_38 : okPQ2 67 38 = true := by decide +kernel
theorem okPQ2_67_39 : okPQ2 67 39 = true := by decide +kernel
theorem okPQ2_67_40 : okPQ2 67 40 = true := by decide +kernel

theorem okP2_67 : okP2 67 = true := by
  unfold okP2
  rw [List.all_eq_true]
  intro Q hQ
  rw [List.mem_range] at hQ
  simp only [Bool.or_eq_true, beq_iff_eq]
  interval_cases Q
  · left; rfl
  · right; exact okPQ2_67_1
  · right; exact okPQ2_67_2
  · right; exact okPQ2_67_3
  · right; exact okPQ2_67_4
  · right; exact okPQ2_67_5
  · right; exact okPQ2_67_6
  · right; exact okPQ2_67_7
  · right; exact okPQ2_67_8
  · right; exact okPQ2_67_9
  · right; exact okPQ2_67_10
  · right; exact okPQ2_67_11
  · right; exact okPQ2_67_12
  · right; exact okPQ2_67_13
  · right; exact okPQ2_67_14
  · right; exact okPQ2_67_15
  · right; exact okPQ2_67_16
  · right; exact okPQ2_67_17
  · right; exact okPQ2_67_18
  · right; exact okPQ2_67_19
  · right; exact okPQ2_67_20
  · right; exact okPQ2_67_21
  · right; exact okPQ2_67_22
  · right; exact okPQ2_67_23
  · right; exact okPQ2_67_24
  · right; exact okPQ2_67_25
  · right; exact okPQ2_67_26
  · right; exact okPQ2_67_27
  · right; exact okPQ2_67_28
  · right; exact okPQ2_67_29
  · right; exact okPQ2_67_30
  · right; exact okPQ2_67_31
  · right; exact okPQ2_67_32
  · right; exact okPQ2_67_33
  · right; exact okPQ2_67_34
  · right; exact okPQ2_67_35
  · right; exact okPQ2_67_36
  · right; exact okPQ2_67_37
  · right; exact okPQ2_67_38
  · right; exact okPQ2_67_39
  · right; exact okPQ2_67_40

end OeisA224
