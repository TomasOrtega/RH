import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneLeftInverse
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAdaptedPlaneLeftInverse.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.adapted_plane_left_inverse : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d d₁ r' s' i₀ i₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁), W.IsSkew σ B r' s' → H'.IsAdapted σ B W W₁ i₀ i₁ → ∃ L : Matrix (Fin d₁) (Fin d) E, L * H'.ι = 1 := by
  first | exact @GlobalTheory.PlaneLeftInv.exists_leftInv | exact GlobalTheory.PlaneLeftInv.exists_leftInv | (intros; apply GlobalTheory.PlaneLeftInv.exists_leftInv <;> assumption)
