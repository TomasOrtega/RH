import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIntegersFiniteExtensionOpen
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerWindowSums
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isOpen_integers_finExt` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FPadicIntegersFiniteExtensionOpen.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.padic_integers_finite_extension_open : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), IsOpen ((OL LL : Subalgebra ℤ_[l] ↥LL.1) : Set ↥LL.1) := by
  first | exact @GlobalTheory.isOpen_integers_finExt | exact GlobalTheory.isOpen_integers_finExt | (intros; apply GlobalTheory.isOpen_integers_finExt <;> assumption)
