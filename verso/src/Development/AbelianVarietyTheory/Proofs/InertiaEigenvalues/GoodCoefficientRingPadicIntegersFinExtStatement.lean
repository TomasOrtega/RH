import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientRingPadicIntegersFinExt
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LocalIntegers.goodO_integers` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FGoodCoefficientRingPadicIntegersFinExt.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.goodCoefficientRing_padicIntegers_finExt : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL) := by
  first | exact @GlobalTheory.LocalIntegers.goodO_integers | exact GlobalTheory.LocalIntegers.goodO_integers | (intros; apply GlobalTheory.LocalIntegers.goodO_integers <;> assumption)
