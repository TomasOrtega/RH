import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFullFaithfulExactPsi
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.fontaine_litFont_assembled` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFontaineFullFaithfulExactPsi.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.fontaine_fullFaithful_exact_psi : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.InvariantsGenerators.LitFont D HW F := by
  first | exact @GlobalTheory.fontaine_litFont_assembled | exact GlobalTheory.fontaine_litFont_assembled | (intros; apply GlobalTheory.fontaine_litFont_assembled <;> assumption)
