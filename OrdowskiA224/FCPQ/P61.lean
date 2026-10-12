import OrdowskiA224.FiniteCheckPQ

/-! Kernel check for p = 61 (one theorem per Q). -/

namespace OeisA224

theorem okPQ2_61_1 : okPQ2 61 1 = true := by decide +kernel
theorem okPQ2_61_2 : okPQ2 61 2 = true := by decide +kernel
theorem okPQ2_61_3 : okPQ2 61 3 = true := by decide +kernel
theorem okPQ2_61_4 : okPQ2 61 4 = true := by decide +kernel
theorem okPQ2_61_5 : okPQ2 61 5 = true := by decide +kernel
theorem okPQ2_61_6 : okPQ2 61 6 = true := by decide +kernel
theorem okPQ2_61_7 : okPQ2 61 7 = true := by decide +kernel
theorem okPQ2_61_8 : okPQ2 61 8 = true := by decide +kernel
theorem okPQ2_61_9 : okPQ2 61 9 = true := by decide +kernel
theorem okPQ2_61_10 : okPQ2 61 10 = true := by decide +kernel
theorem okPQ2_61_11 : okPQ2 61 11 = true := by decide +kernel
theorem okPQ2_61_12 : okPQ2 61 12 = true := by decide +kernel
theorem okPQ2_61_13 : okPQ2 61 13 = true := by decide +kernel
theorem okPQ2_61_14 : okPQ2 61 14 = true := by decide +kernel
theorem okPQ2_61_15 : okPQ2 61 15 = true := by decide +kernel
theorem okPQ2_61_16 : okPQ2 61 16 = true := by decide +kernel
theorem okPQ2_61_17 : okPQ2 61 17 = true := by decide +kernel
theorem okPQ2_61_18 : okPQ2 61 18 = true := by decide +kernel
theorem okPQ2_61_19 : okPQ2 61 19 = true := by decide +kernel
theorem okPQ2_61_20 : okPQ2 61 20 = true := by decide +kernel
theorem okPQ2_61_21 : okPQ2 61 21 = true := by decide +kernel
theorem okPQ2_61_22 : okPQ2 61 22 = true := by decide +kernel
theorem okPQ2_61_23 : okPQ2 61 23 = true := by decide +kernel
theorem okPQ2_61_24 : okPQ2 61 24 = true := by decide +kernel
theorem okPQ2_61_25 : okPQ2 61 25 = true := by decide +kernel
theorem okPQ2_61_26 : okPQ2 61 26 = true := by decide +kernel
theorem okPQ2_61_27 : okPQ2 61 27 = true := by decide +kernel
theorem okPQ2_61_28 : okPQ2 61 28 = true := by decide +kernel
theorem okPQ2_61_29 : okPQ2 61 29 = true := by decide +kernel
theorem okPQ2_61_30 : okPQ2 61 30 = true := by decide +kernel
theorem okPQ2_61_31 : okPQ2 61 31 = true := by decide +kernel
theorem okPQ2_61_32 : okPQ2 61 32 = true := by decide +kernel
theorem okPQ2_61_33 : okPQ2 61 33 = true := by decide +kernel
theorem okPQ2_61_34 : okPQ2 61 34 = true := by decide +kernel
theorem okPQ2_61_35 : okPQ2 61 35 = true := by decide +kernel
theorem okPQ2_61_36 : okPQ2 61 36 = true := by decide +kernel
theorem okPQ2_61_37 : okPQ2 61 37 = true := by decide +kernel
theorem okPQ2_61_38 : okPQ2 61 38 = true := by decide +kernel
theorem okPQ2_61_39 : okPQ2 61 39 = true := by decide +kernel
theorem okPQ2_61_40 : okPQ2 61 40 = true := by decide +kernel

theorem okP2_61 : okP2 61 = true := by
  unfold okP2
  rw [List.all_eq_true]
  intro Q hQ
  rw [List.mem_range] at hQ
  simp only [Bool.or_eq_true, beq_iff_eq]
  interval_cases Q
  · left; rfl
  · right; exact okPQ2_61_1
  · right; exact okPQ2_61_2
  · right; exact okPQ2_61_3
  · right; exact okPQ2_61_4
  · right; exact okPQ2_61_5
  · right; exact okPQ2_61_6
  · right; exact okPQ2_61_7
  · right; exact okPQ2_61_8
  · right; exact okPQ2_61_9
  · right; exact okPQ2_61_10
  · right; exact okPQ2_61_11
  · right; exact okPQ2_61_12
  · right; exact okPQ2_61_13
  · right; exact okPQ2_61_14
  · right; exact okPQ2_61_15
  · right; exact okPQ2_61_16
  · right; exact okPQ2_61_17
  · right; exact okPQ2_61_18
  · right; exact okPQ2_61_19
  · right; exact okPQ2_61_20
  · right; exact okPQ2_61_21
  · right; exact okPQ2_61_22
  · right; exact okPQ2_61_23
  · right; exact okPQ2_61_24
  · right; exact okPQ2_61_25
  · right; exact okPQ2_61_26
  · right; exact okPQ2_61_27
  · right; exact okPQ2_61_28
  · right; exact okPQ2_61_29
  · right; exact okPQ2_61_30
  · right; exact okPQ2_61_31
  · right; exact okPQ2_61_32
  · right; exact okPQ2_61_33
  · right; exact okPQ2_61_34
  · right; exact okPQ2_61_35
  · right; exact okPQ2_61_36
  · right; exact okPQ2_61_37
  · right; exact okPQ2_61_38
  · right; exact okPQ2_61_39
  · right; exact okPQ2_61_40

end OeisA224
