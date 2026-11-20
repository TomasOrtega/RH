import Mathlib
import Formalism.PeriodIntegrals.FoldDCUnfold
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FoldUnfold
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FoldingUnfolding.FoldDCUnfoldOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FoldingUnfolding.TranslationIndependent
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FoldingUnfolding.DoubleCosetTranslation

/- English proof (translation)
The claim follows from `PI.FoldDCUnfold.W.foldDCUnfold_of PI.FoldDCUnfold.W.translation_exists PI.FoldDCUnfold.W.translation_independent PI.FoldDCUnfold.W.translation_product PI.FoldDCUnfold.W.double_coset_translation lintegralTransversalSum`.
-/
theorem fold_dc_unfold : PI.FoldDCUnfold.FoldDCUnfold :=
  PI.FoldDCUnfold.W.foldDCUnfold_of PI.FoldDCUnfold.W.translation_exists
    PI.FoldDCUnfold.W.translation_independent PI.FoldDCUnfold.W.translation_product
    PI.FoldDCUnfold.W.double_coset_translation lintegralTransversalSum
