import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonoidAlgebraExistsRightInvOfMapField
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.groupAlgebra_exists_right_inv_of_map` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FMonoidAlgebraExistsRightInvOfMapField.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.monoidAlgebra_exists_right_inv_of_map_field : ∀ {E L G : Type} [Field E] [Field L] [Group G] [Fintype G] (j : E →+* L) (x : MonoidAlgebra E G), (∃ v : MonoidAlgebra L G, MonoidAlgebra.mapRingHom G j x * v = 1) → ∃ v : MonoidAlgebra E G, x * v = 1 := by
  first | exact @GlobalTheory.groupAlgebra_exists_right_inv_of_map | exact GlobalTheory.groupAlgebra_exists_right_inv_of_map | (intros; apply GlobalTheory.groupAlgebra_exists_right_inv_of_map <;> assumption)
