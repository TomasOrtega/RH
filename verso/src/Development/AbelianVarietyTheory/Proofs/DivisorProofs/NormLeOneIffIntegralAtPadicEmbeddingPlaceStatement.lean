import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeOneIffIntegralAtPadicEmbeddingPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamGApply
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FrameRead.norm_le_one_iff_integral_at` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNormLeOneIffIntegralAtPadicEmbeddingPlace.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.norm_le_one_iff_integral_at_padicEmbedding_place : ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 K)) (e0 : K →+* PadicAlgCl l), AtPlace w e0 → ∀ x : K, ‖e0 x‖ ≤ 1 ↔ ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∃ r : 𝓞 K, (s : K) * x = r := by
  first | exact @GlobalTheory.FrameRead.norm_le_one_iff_integral_at | exact GlobalTheory.FrameRead.norm_le_one_iff_integral_at | (intros; apply GlobalTheory.FrameRead.norm_le_one_iff_integral_at <;> assumption)
