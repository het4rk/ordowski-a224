import OrdowskiA224.FCPQ.P5_0
import OrdowskiA224.FCPQ.P5_1
import OrdowskiA224.FCPQ.P5_2
import OrdowskiA224.FCPQ.P5_3

namespace OeisA224

theorem okP2_5 : okP2 5 = true := by
  unfold okP2
  rw [List.all_eq_true]
  intro Q hQ
  rw [List.mem_range] at hQ
  simp only [Bool.or_eq_true, beq_iff_eq]
  interval_cases Q
  · left; rfl
  · right; exact okPQ2_5_1
  · right; exact okPQ2_5_2
  · right; exact okPQ2_5_3
  · right; exact okPQ2_5_4
  · right; exact okPQ2_5_5
  · right; exact okPQ2_5_6
  · right; exact okPQ2_5_7
  · right; exact okPQ2_5_8
  · right; exact okPQ2_5_9
  · right; exact okPQ2_5_10
  · right; exact okPQ2_5_11
  · right; exact okPQ2_5_12
  · right; exact okPQ2_5_13
  · right; exact okPQ2_5_14
  · right; exact okPQ2_5_15
  · right; exact okPQ2_5_16
  · right; exact okPQ2_5_17
  · right; exact okPQ2_5_18
  · right; exact okPQ2_5_19
  · right; exact okPQ2_5_20
  · right; exact okPQ2_5_21
  · right; exact okPQ2_5_22
  · right; exact okPQ2_5_23
  · right; exact okPQ2_5_24
  · right; exact okPQ2_5_25
  · right; exact okPQ2_5_26
  · right; exact okPQ2_5_27
  · right; exact okPQ2_5_28
  · right; exact okPQ2_5_29
  · right; exact okPQ2_5_30
  · right; exact okPQ2_5_31
  · right; exact okPQ2_5_32
  · right; exact okPQ2_5_33
  · right; exact okPQ2_5_34
  · right; exact okPQ2_5_35
  · right; exact okPQ2_5_36
  · right; exact okPQ2_5_37
  · right; exact okPQ2_5_38
  · right; exact okPQ2_5_39
  · right; exact okPQ2_5_40

end OeisA224
