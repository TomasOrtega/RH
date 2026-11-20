import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureIndependentChoices
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FThetaMeasureIndependentChoices.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.theta_measure_independent_choices : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ μ' : Measure (HA (AF F) σ J)) (𝓕 𝓕' : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → IsHaarH F E σ M J μ' → IsFDH F E σ M J μ' 𝓕' → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), thetaMeas σ J μ 𝓕 {X | gramE σ J X = T} = thetaMeas σ J μ' 𝓕' {X | gramE σ J X = T} := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThetaIndep.thetaMeas_gram_indep | exact GlobalTheory.CompanionTheory.SW.ThetaIndep.thetaMeas_gram_indep | (intros; apply GlobalTheory.CompanionTheory.SW.ThetaIndep.thetaMeas_gram_indep <;> assumption)
