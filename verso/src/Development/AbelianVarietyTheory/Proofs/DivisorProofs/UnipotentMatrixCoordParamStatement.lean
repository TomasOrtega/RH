import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentMatrixCoordParam
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.UnipDom
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThK.UnipDom.exists_continuous_mat_eq_plane` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnipotentMatrixCoordParam.lean&line=109#L109)
-/
theorem _root_.GlobalTheory.T.unipotent_matrix_coord_param : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁), IsCMExt F E σ → (∀ i j, σ (Y.J j i) = -Y.J i j) → IsIsoPlane σ B H Y Y₁ → ∃ Ψ : (Fin n₁ → AE F E) × AE F E → Matrix (Fin n) (Fin n) (AE F E), Continuous Ψ ∧ ∀ u ∈ unip σ Y H, mat u = Ψ (coA σ Y.J H u, coC σ Y.J H u) := by
  first | exact @GlobalTheory.ThK.UnipDom.exists_continuous_mat_eq_plane | exact GlobalTheory.ThK.UnipDom.exists_continuous_mat_eq_plane | (intros; apply GlobalTheory.ThK.UnipDom.exists_continuous_mat_eq_plane <;> assumption)
