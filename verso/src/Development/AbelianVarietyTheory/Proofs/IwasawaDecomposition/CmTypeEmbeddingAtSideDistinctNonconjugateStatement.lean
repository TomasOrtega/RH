import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmTypeEmbeddingAtSideDistinctNonconjugate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeightCounting.FormsStep.kEmbT_cmDist` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FCmTypeEmbeddingAtSideDistinctNonconjugate.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.cmTypeEmbeddingAtSide_distinct_nonconjugate : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (b : Bool), GlobalTheory.AlgWtF.CMDist (kEmbT D T i b) := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.kEmbT_cmDist | exact GlobalTheory.HeightCounting.FormsStep.kEmbT_cmDist | (intros; apply GlobalTheory.HeightCounting.FormsStep.kEmbT_cmDist <;> assumption)
