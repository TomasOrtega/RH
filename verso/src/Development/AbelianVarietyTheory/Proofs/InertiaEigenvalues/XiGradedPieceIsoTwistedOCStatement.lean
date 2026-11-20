import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiGradedPieceIsoTwistedOC
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Cyc.Graded.graded_iso` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FXiGradedPieceIsoTwistedOC.lean&line=279#L279)
-/
theorem _root_.GlobalTheory.T.xiGradedPiece_iso_twistedOC : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (i : ℤ), ∃ Φ : Qab (AinfSub l) (xiU AI) i (i + 1) →+ PadicComplex l, Function.Injective Φ ∧ Set.range Φ = {y | ‖y‖ ≤ 1} ∧ (∀ (z : ℤ_[l]) x, Φ (z • x) = zC z * Φ x) ∧ ∀ g : GQ l, g (P.ζQ 1) = P.ζQ 1 → ∀ x, Φ (actQab (xiOK AI) i (i + 1) g x) = chiC P.χQ i g * AI.actC g (Φ x) := by
  first | exact @GlobalTheory.Cyc.Graded.graded_iso | exact GlobalTheory.Cyc.Graded.graded_iso | (intros; apply GlobalTheory.Cyc.Graded.graded_iso <;> assumption)
