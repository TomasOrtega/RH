import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorOfRationalLocalDuality
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FBlochKatoAnnihilatorOfRationalLocalDuality.lean&line=118#L118)
-/
theorem _root_.GlobalTheory.T.blochKatoAnnihilator_of_rationalLocalDuality : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), GlobalTheory.Published.BlochKato.RationalDuality (P.PD K) → bkACore (P.PD K) := by
  first | exact @GlobalTheory.bkACore_of_rationalDuality | exact GlobalTheory.bkACore_of_rationalDuality | (intros; apply GlobalTheory.bkACore_of_rationalDuality <;> assumption)
