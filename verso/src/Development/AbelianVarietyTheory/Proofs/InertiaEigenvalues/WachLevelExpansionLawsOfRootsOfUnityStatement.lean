import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionLawsOfRootsOfUnity
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NL.Expansion.levLaws` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWachLevelExpansionLawsOfRootsOfUnity.lean&line=72#L72)
-/
theorem _root_.GlobalTheory.T.wachLevelExpansionLaws_of_rootsOfUnity : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; LevLaws W := by
  first | exact @GlobalTheory.NL.Expansion.levLaws | exact GlobalTheory.NL.Expansion.levLaws | (intros; apply GlobalTheory.NL.Expansion.levLaws <;> assumption)
