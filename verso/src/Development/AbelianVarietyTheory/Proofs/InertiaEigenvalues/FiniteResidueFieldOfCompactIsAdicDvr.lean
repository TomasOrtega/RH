import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem finite_residueField_of_compact_isAdic :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O], IsAdic (IsLocalRing.maximalIdeal O) →
    Finite (IsLocalRing.ResidueField O) := by
  intro O _ _ _ _ _ _ h
  have hopen : IsOpen ((IsLocalRing.maximalIdeal O : Ideal O) : Set O) := by
    have := (isAdic_iff.mp h).1 1
    simpa using this
  have hfin : Finite (O ⧸ (IsLocalRing.maximalIdeal O).toAddSubgroup) :=
    AddSubgroup.quotient_finite_of_isOpen _ hopen
  exact hfin

end GlobalTheory.ShapeNeg
