import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DcrisExactStrictElementwiseCrystalline
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FDcrisExactStrictElementwiseCrystalline.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.dcris_exact_strict_elementwise_crystalline : ∀ D : D7, Formalism.MainNotions.TruncatedSeriesCountingBounds.adm9 D := by
  first | exact @GlobalTheory.dcris_exact_strict_elementwise | exact GlobalTheory.dcris_exact_strict_elementwise | (intros; apply GlobalTheory.dcris_exact_strict_elementwise <;> assumption)
