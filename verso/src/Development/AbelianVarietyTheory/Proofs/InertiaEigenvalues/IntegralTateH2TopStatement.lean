import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralTateH2Top
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIntegralTateH2Top.lean&line=290#L290)
-/
theorem _root_.GlobalTheory.T.integral_tate_H2_top : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.admH2 i := by
  first | exact @GlobalTheory.IntTateTop.admH2_of_duality | exact GlobalTheory.IntTateTop.admH2_of_duality | (intros; apply GlobalTheory.IntTateTop.admH2_of_duality <;> assumption)
