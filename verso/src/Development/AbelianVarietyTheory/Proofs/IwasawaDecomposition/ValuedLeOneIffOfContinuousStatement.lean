import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLeOneIffOfContinuous
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IsoInteg.valued_le_one_iff_of_continuous` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FValuedLeOneIffOfContinuous.lean&line=81#L81)
-/
theorem _root_.GlobalTheory.T.valued_le_one_iff_of_continuous_ringEquiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 F))
    (w : HeightOneSpectrum (𝓞 E)) (i : v.adicCompletion F ≃+* w.adicCompletion E), Continuous i →
    ∀ a : v.adicCompletion F, Valued.v (i a) ≤ 1 ↔ Valued.v a ≤ 1 := by
  first | exact @GlobalTheory.IsoInteg.valued_le_one_iff_of_continuous | exact GlobalTheory.IsoInteg.valued_le_one_iff_of_continuous | (intros; apply GlobalTheory.IsoInteg.valued_le_one_iff_of_continuous <;> assumption)
