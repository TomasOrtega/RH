import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzL2EuclideanIdentification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchwartzL2EuclideanIdentification.lean&line=68#L68)
-/
theorem _root_.GlobalTheory.T.schwartz_L2_euclidean_identification : ∀ (l : Type) [Fintype l] [DecidableEq l], ∃ (e : 𝓢(l → ℝ, ℂ) ≃L[ℂ] Sch l) (u : Lp ℂ 2 (volume : Measure (l → ℝ)) ≃ₗᵢ[ℂ] L2 l), (∀ φ (x : EuclideanSpace ℝ l), e φ x = φ x.ofLp) ∧ ∀ φ : 𝓢(l → ℝ, ℂ), u (φ.toLp 2) = (e φ).toLp 2 := by
  first | exact @GlobalTheory.EuclidTransport.exists_schwartz_L2_transport | exact GlobalTheory.EuclidTransport.exists_schwartz_L2_transport | (intros; apply GlobalTheory.EuclidTransport.exists_schwartz_L2_transport <;> assumption)
