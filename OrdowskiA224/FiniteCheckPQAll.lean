import OrdowskiA224.FCPQ.P3
import OrdowskiA224.FCPQ.P5
import OrdowskiA224.FCPQ.P7
import OrdowskiA224.FCPQ.P11
import OrdowskiA224.FCPQ.P13
import OrdowskiA224.FCPQ.P17
import OrdowskiA224.FCPQ.P19
import OrdowskiA224.FCPQ.P23
import OrdowskiA224.FCPQ.P29
import OrdowskiA224.FCPQ.P31
import OrdowskiA224.FCPQ.P37
import OrdowskiA224.FCPQ.P41
import OrdowskiA224.FCPQ.P43
import OrdowskiA224.FCPQ.P47
import OrdowskiA224.FCPQ.P53
import OrdowskiA224.FCPQ.P59
import OrdowskiA224.FCPQ.P61
import OrdowskiA224.FCPQ.P67

namespace OeisA224

theorem okP2_of_mem (p : ℕ) (hp : p ∈ primesTo67) : okP2 p = true := by
  simp only [primesTo67, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact okP2_3
  · exact okP2_5
  · exact okP2_7
  · exact okP2_11
  · exact okP2_13
  · exact okP2_17
  · exact okP2_19
  · exact okP2_23
  · exact okP2_29
  · exact okP2_31
  · exact okP2_37
  · exact okP2_41
  · exact okP2_43
  · exact okP2_47
  · exact okP2_53
  · exact okP2_59
  · exact okP2_61
  · exact okP2_67

end OeisA224
