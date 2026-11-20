import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetAdaptedBasis
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsUnitDetAdaptedBasis.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.isUnit_det_adapted_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) {m : ℕ} (W : Spc F E (m + 2)) (r s : ℕ), W.IsSkew σ B r s →
    ∀ (W₁ : Spc F E m) (H : Plane E (m + 2) m) (i₀ i₁ : ℕ), H.IsAdapted σ B W W₁ i₀ i₁ → IsUnit (basQ H).det := by
  first | exact @GlobalTheory.QhtUnip.BasisUnit.isUnit_det_basQ | exact GlobalTheory.QhtUnip.BasisUnit.isUnit_det_basQ | (intros; apply GlobalTheory.QhtUnip.BasisUnit.isUnit_det_basQ <;> assumption)
