import OrdowskiA224.FiniteCheckPQ

/-! Kernel check for p = 47 (one theorem per Q). -/

namespace OeisA224

theorem okPQ2_47_1 : okPQ2 47 1 = true := by decide +kernel
theorem okPQ2_47_2 : okPQ2 47 2 = true := by decide +kernel
theorem okPQ2_47_3 : okPQ2 47 3 = true := by decide +kernel
theorem okPQ2_47_4 : okPQ2 47 4 = true := by decide +kernel
theorem okPQ2_47_5 : okPQ2 47 5 = true := by decide +kernel
theorem okPQ2_47_6 : okPQ2 47 6 = true := by decide +kernel
theorem okPQ2_47_7 : okPQ2 47 7 = true := by decide +kernel
theorem okPQ2_47_8 : okPQ2 47 8 = true := by decide +kernel
theorem okPQ2_47_9 : okPQ2 47 9 = true := by decide +kernel
theorem okPQ2_47_10 : okPQ2 47 10 = true := by decide +kernel
theorem okPQ2_47_11 : okPQ2 47 11 = true := by decide +kernel
theorem okPQ2_47_12 : okPQ2 47 12 = true := by decide +kernel
theorem okPQ2_47_13 : okPQ2 47 13 = true := by decide +kernel
theorem okPQ2_47_14 : okPQ2 47 14 = true := by decide +kernel
theorem okPQ2_47_15 : okPQ2 47 15 = true := by decide +kernel
theorem okPQ2_47_16 : okPQ2 47 16 = true := by decide +kernel
theorem okPQ2_47_17 : okPQ2 47 17 = true := by decide +kernel
theorem okPQ2_47_18 : okPQ2 47 18 = true := by decide +kernel
theorem okPQ2_47_19 : okPQ2 47 19 = true := by decide +kernel
theorem okPQ2_47_20 : okPQ2 47 20 = true := by decide +kernel
theorem okPQ2_47_21 : okPQ2 47 21 = true := by decide +kernel
theorem okPQ2_47_22 : okPQ2 47 22 = true := by decide +kernel
theorem okPQ2_47_23 : okPQ2 47 23 = true := by decide +kernel
theorem okPQ2_47_24 : okPQ2 47 24 = true := by decide +kernel
theorem okPQ2_47_25 : okPQ2 47 25 = true := by decide +kernel
theorem okPQ2_47_26 : okPQ2 47 26 = true := by decide +kernel
theorem okPQ2_47_27 : okPQ2 47 27 = true := by decide +kernel
theorem okPQ2_47_28 : okPQ2 47 28 = true := by decide +kernel
theorem okPQ2_47_29 : okPQ2 47 29 = true := by decide +kernel
theorem okPQ2_47_30 : okPQ2 47 30 = true := by decide +kernel
theorem okPQ2_47_31 : okPQ2 47 31 = true := by decide +kernel
theorem okPQ2_47_32 : okPQ2 47 32 = true := by decide +kernel
theorem okPQ2_47_33 : okPQ2 47 33 = true := by decide +kernel
theorem okPQ2_47_34 : okPQ2 47 34 = true := by decide +kernel
theorem okPQ2_47_35 : okPQ2 47 35 = true := by decide +kernel
theorem okPQ2_47_36 : okPQ2 47 36 = true := by decide +kernel
theorem okPQ2_47_37 : okPQ2 47 37 = true := by decide +kernel
theorem okPQ2_47_38 : okPQ2 47 38 = true := by decide +kernel
theorem okPQ2_47_39 : okPQ2 47 39 = true := by decide +kernel
theorem okPQ2_47_40 : okPQ2 47 40 = true := by decide +kernel

theorem okP2_47 : okP2 47 = true := by
  unfold okP2
  rw [List.all_eq_true]
  intro Q hQ
  rw [List.mem_range] at hQ
  simp only [Bool.or_eq_true, beq_iff_eq]
  interval_cases Q
  · left; rfl
  · right; exact okPQ2_47_1
  · right; exact okPQ2_47_2
  · right; exact okPQ2_47_3
  · right; exact okPQ2_47_4
  · right; exact okPQ2_47_5
  · right; exact okPQ2_47_6
  · right; exact okPQ2_47_7
  · right; exact okPQ2_47_8
  · right; exact okPQ2_47_9
  · right; exact okPQ2_47_10
  · right; exact okPQ2_47_11
  · right; exact okPQ2_47_12
  · right; exact okPQ2_47_13
  · right; exact okPQ2_47_14
  · right; exact okPQ2_47_15
  · right; exact okPQ2_47_16
  · right; exact okPQ2_47_17
  · right; exact okPQ2_47_18
  · right; exact okPQ2_47_19
  · right; exact okPQ2_47_20
  · right; exact okPQ2_47_21
  · right; exact okPQ2_47_22
  · right; exact okPQ2_47_23
  · right; exact okPQ2_47_24
  · right; exact okPQ2_47_25
  · right; exact okPQ2_47_26
  · right; exact okPQ2_47_27
  · right; exact okPQ2_47_28
  · right; exact okPQ2_47_29
  · right; exact okPQ2_47_30
  · right; exact okPQ2_47_31
  · right; exact okPQ2_47_32
  · right; exact okPQ2_47_33
  · right; exact okPQ2_47_34
  · right; exact okPQ2_47_35
  · right; exact okPQ2_47_36
  · right; exact okPQ2_47_37
  · right; exact okPQ2_47_38
  · right; exact okPQ2_47_39
  · right; exact okPQ2_47_40

end OeisA224
