import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CenterMonoidAlgebraLeSpanCentralIntegral
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GroupAlg.center_mem_span_classSums` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCenterMonoidAlgebraLeSpanCentralIntegral.lean&line=70#L70)
-/
theorem _root_.GlobalTheory.T.center_monoidAlgebra_le_span_centralIntegral : ∀ (R G : Type) [CommRing R] [Group G] [Finite G] (z : MonoidAlgebra R G), z ∈ Subalgebra.center R (MonoidAlgebra R G) → z ∈ Submodule.span R ((MonoidAlgebra.mapRingHom G (Int.castRingHom R)) '' {c : MonoidAlgebra ℤ G | ∀ a, c * a = a * c}) := by
  first | exact @GlobalTheory.GroupAlg.center_mem_span_classSums | exact GlobalTheory.GroupAlg.center_mem_span_classSums | (intros; apply GlobalTheory.GroupAlg.center_mem_span_classSums <;> assumption)
