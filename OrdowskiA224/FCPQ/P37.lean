import OrdowskiA224.FiniteCheckPQ

/-! Kernel check for p = 37 (one theorem per Q). -/

namespace OeisA224

theorem okPQ2_37_1 : okPQ2 37 1 = true := by decide +kernel
theorem okPQ2_37_2 : okPQ2 37 2 = true := by decide +kernel
theorem okPQ2_37_3 : okPQ2 37 3 = true := by decide +kernel
theorem okPQ2_37_4 : okPQ2 37 4 = true := by decide +kernel
theorem okPQ2_37_5 : okPQ2 37 5 = true := by decide +kernel
theorem okPQ2_37_6 : okPQ2 37 6 = true := by decide +kernel
theorem okPQ2_37_7 : okPQ2 37 7 = true := by decide +kernel
theorem okPQ2_37_8 : okPQ2 37 8 = true := by decide +kernel
theorem okPQ2_37_9 : okPQ2 37 9 = true := by decide +kernel
theorem okPQ2_37_10 : okPQ2 37 10 = true := by decide +kernel
theorem okPQ2_37_11 : okPQ2 37 11 = true := by decide +kernel
theorem okPQ2_37_12 : okPQ2 37 12 = true := by decide +kernel
theorem okPQ2_37_13 : okPQ2 37 13 = true := by decide +kernel
theorem okPQ2_37_14 : okPQ2 37 14 = true := by decide +kernel
theorem okPQ2_37_15 : okPQ2 37 15 = true := by decide +kernel
theorem okPQ2_37_16 : okPQ2 37 16 = true := by decide +kernel
theorem okPQ2_37_17 : okPQ2 37 17 = true := by decide +kernel
theorem okPQ2_37_18 : okPQ2 37 18 = true := by decide +kernel
theorem okPQ2_37_19 : okPQ2 37 19 = true := by decide +kernel
theorem okPQ2_37_20 : okPQ2 37 20 = true := by decide +kernel
theorem okPQ2_37_21 : okPQ2 37 21 = true := by decide +kernel
theorem okPQ2_37_22 : okPQ2 37 22 = true := by decide +kernel
theorem okPQ2_37_23 : okPQ2 37 23 = true := by decide +kernel
theorem okPQ2_37_24 : okPQ2 37 24 = true := by decide +kernel
theorem okPQ2_37_25 : okPQ2 37 25 = true := by decide +kernel
theorem okPQ2_37_26 : okPQ2 37 26 = true := by decide +kernel
theorem okPQ2_37_27 : okPQ2 37 27 = true := by decide +kernel
theorem okPQ2_37_28 : okPQ2 37 28 = true := by decide +kernel
theorem okPQ2_37_29 : okPQ2 37 29 = true := by decide +kernel
theorem okPQ2_37_30 : okPQ2 37 30 = true := by decide +kernel
theorem okPQ2_37_31 : okPQ2 37 31 = true := by decide +kernel
theorem okPQ2_37_32 : okPQ2 37 32 = true := by decide +kernel
theorem okPQ2_37_33 : okPQ2 37 33 = true := by decide +kernel
theorem okPQ2_37_34 : okPQ2 37 34 = true := by decide +kernel
theorem okPQ2_37_35 : okPQ2 37 35 = true := by decide +kernel
theorem okPQ2_37_36 : okPQ2 37 36 = true := by decide +kernel
theorem okPQ2_37_37 : okPQ2 37 37 = true := by decide +kernel
theorem okPQ2_37_38 : okPQ2 37 38 = true := by decide +kernel
theorem okPQ2_37_39 : okPQ2 37 39 = true := by decide +kernel
theorem okPQ2_37_40 : okPQ2 37 40 = true := by decide +kernel

theorem okP2_37 : okP2 37 = true := by
  unfold okP2
  rw [List.all_eq_true]
  intro Q hQ
  rw [List.mem_range] at hQ
  simp only [Bool.or_eq_true, beq_iff_eq]
  interval_cases Q
  · left; rfl
  · right; exact okPQ2_37_1
  · right; exact okPQ2_37_2
  · right; exact okPQ2_37_3
  · right; exact okPQ2_37_4
  · right; exact okPQ2_37_5
  · right; exact okPQ2_37_6
  · right; exact okPQ2_37_7
  · right; exact okPQ2_37_8
  · right; exact okPQ2_37_9
  · right; exact okPQ2_37_10
  · right; exact okPQ2_37_11
  · right; exact okPQ2_37_12
  · right; exact okPQ2_37_13
  · right; exact okPQ2_37_14
  · right; exact okPQ2_37_15
  · right; exact okPQ2_37_16
  · right; exact okPQ2_37_17
  · right; exact okPQ2_37_18
  · right; exact okPQ2_37_19
  · right; exact okPQ2_37_20
  · right; exact okPQ2_37_21
  · right; exact okPQ2_37_22
  · right; exact okPQ2_37_23
  · right; exact okPQ2_37_24
  · right; exact okPQ2_37_25
  · right; exact okPQ2_37_26
  · right; exact okPQ2_37_27
  · right; exact okPQ2_37_28
  · right; exact okPQ2_37_29
  · right; exact okPQ2_37_30
  · right; exact okPQ2_37_31
  · right; exact okPQ2_37_32
  · right; exact okPQ2_37_33
  · right; exact okPQ2_37_34
  · right; exact okPQ2_37_35
  · right; exact okPQ2_37_36
  · right; exact okPQ2_37_37
  · right; exact okPQ2_37_38
  · right; exact okPQ2_37_39
  · right; exact okPQ2_37_40

end OeisA224
