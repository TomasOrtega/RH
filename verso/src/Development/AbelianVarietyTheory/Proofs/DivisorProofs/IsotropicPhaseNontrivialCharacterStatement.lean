import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPhaseNontrivialCharacter
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqZeroOfMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsotropicPhaseNontrivialCharacter.lean&line=215#L215)
-/
theorem _root_.GlobalTheory.T.isotropic_phase_nontrivial_character : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r' s' : ℕ), B.IsGood σ → W.IsSkew σ B r' s' →
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ w : Fin d₁ → E, w ≠ 0 → ∃ g ∈ unip σ W H', B.ψ (GlobalTheory.IsoPhase.phase σ W H' w g) ≠ 1 := by
  first | exact @GlobalTheory.IsoPhaseNonzero.exists_phase_ne_one | exact GlobalTheory.IsoPhaseNonzero.exists_phase_ne_one | (intros; apply GlobalTheory.IsoPhaseNonzero.exists_phase_ne_one <;> assumption)
