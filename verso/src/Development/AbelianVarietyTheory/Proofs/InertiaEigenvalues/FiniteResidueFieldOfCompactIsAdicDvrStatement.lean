import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteResidueFieldOfCompactIsAdicDvr
import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ShapeNeg.finite_residueField_of_compact_isAdic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFiniteResidueFieldOfCompactIsAdicDvr.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.finite_residueField_of_compact_isAdic_dvr : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O], IsAdic (IsLocalRing.maximalIdeal O) →
    Finite (IsLocalRing.ResidueField O) := by
  first | exact @GlobalTheory.ShapeNeg.finite_residueField_of_compact_isAdic | exact GlobalTheory.ShapeNeg.finite_residueField_of_compact_isAdic | (intros; apply GlobalTheory.ShapeNeg.finite_residueField_of_compact_isAdic <;> assumption)
