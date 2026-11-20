import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FWeightExponentsEmbeddingsDegree.lean&line=86#L86)
-/
theorem _root_.GlobalTheory.T.weightExponents_embeddings_degree : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, InR D j → ∀ w : WeightFamilies.Wt D j, DF (Q.Dw j) (wtA w) = WeightAlgebra.DF w ∧ Function.Injective (DV.tauEmb D) ∧ (∀ τ, InPsi Q.H τ ↔ ∃ t, τ = DV.tauEmb D t) ∧ (∀ τ, ¬ InPsi Q.H τ ↔ ∃ t, τ = ComplexEmbedding.conjugate (DV.tauEmb D t)) ∧ ∀ t i, wtA w (DV.tauEmb D t, i) = ext0 (w.aP t) i ∧ wtA w (ComplexEmbedding.conjugate (DV.tauEmb D t), i) = ext0 (w.aM t) i := by
  first | exact @GlobalTheory.WeightExponents.weight_exponents | exact GlobalTheory.WeightExponents.weight_exponents | (intros; apply GlobalTheory.WeightExponents.weight_exponents <;> assumption)
