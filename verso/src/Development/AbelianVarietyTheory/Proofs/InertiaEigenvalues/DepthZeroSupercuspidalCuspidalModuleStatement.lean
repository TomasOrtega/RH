import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroSupercuspidalCuspidalModule
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DepthZeroCusp.depthZeroCuspidal` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FDepthZeroSupercuspidalCuspidalModule.lean&line=274#L274)
-/
theorem _root_.GlobalTheory.T.depthZeroSupercuspidal_cuspidalModule : ∀ (g : ℕ) [Fact g.Prime], TameGen.DepthZeroCuspidal g := by
  first | exact @GlobalTheory.DepthZeroCusp.depthZeroCuspidal | exact GlobalTheory.DepthZeroCusp.depthZeroCuspidal | (intros; apply GlobalTheory.DepthZeroCusp.depthZeroCuspidal <;> assumption)
