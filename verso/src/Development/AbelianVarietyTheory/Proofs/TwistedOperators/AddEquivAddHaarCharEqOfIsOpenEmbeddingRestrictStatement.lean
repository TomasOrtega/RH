import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharEqOfIsOpenEmbeddingRestrict
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HaarOpenEmb.addEquivAddHaarChar_eq_of_isOpenEmbedding` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FAddEquivAddHaarCharEqOfIsOpenEmbeddingRestrict.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.addEquivAddHaarChar_eq_of_isOpenEmbedding_restrict : ∀ (G G' : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [AddCommGroup G'] [TopologicalSpace G'] [IsTopologicalAddGroup G'] [LocallyCompactSpace G'] [T2Space G'] [SecondCountableTopology G'] [MeasurableSpace G'] [BorelSpace G'] (j : G' →+ G), IsOpenEmbedding j → ∀ (e : G ≃ₜ+ G) (e' : G' ≃ₜ+ G'), (∀ x, e (j x) = j (e' x)) → addEquivAddHaarChar e = addEquivAddHaarChar e' := by
  first | exact @GlobalTheory.HaarOpenEmb.addEquivAddHaarChar_eq_of_isOpenEmbedding | exact GlobalTheory.HaarOpenEmb.addEquivAddHaarChar_eq_of_isOpenEmbedding | (intros; apply GlobalTheory.HaarOpenEmb.addEquivAddHaarChar_eq_of_isOpenEmbedding <;> assumption)
