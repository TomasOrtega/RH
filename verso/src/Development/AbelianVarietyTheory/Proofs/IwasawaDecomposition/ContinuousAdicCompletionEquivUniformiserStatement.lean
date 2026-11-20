import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAdicCompletionEquivUniformiser
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLeOneIffOfContinuousStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnifMap.unif_to_unif` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FContinuousAdicCompletionEquivUniformiser.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.continuous_adicCompletion_equiv_uniformiser : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 F))
    (w : HeightOneSpectrum (𝓞 E)) (i : v.adicCompletion F ≃+* w.adicCompletion E), Continuous i →
    ∀ ϖ : v.adicCompletion F, Valued.v ϖ = WithZero.exp (-1 : ℤ) → Valued.v (i ϖ) = WithZero.exp (-1 : ℤ) := by
  first | exact @GlobalTheory.UnifMap.unif_to_unif | exact GlobalTheory.UnifMap.unif_to_unif | (intros; apply GlobalTheory.UnifMap.unif_to_unif <;> assumption)
