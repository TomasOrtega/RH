import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSndImageMulMemOpenGroupScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsOpenSndImageMulMemOpenGroupScheme.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.isOpen_snd_image_mul_mem_open_groupScheme : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ U : G.left.Opens, IsOpen {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y} := by
  first | exact @GlobalTheory.IdCompOpen.isOpen_snd_image | exact GlobalTheory.IdCompOpen.isOpen_snd_image | (intros; apply GlobalTheory.IdCompOpen.isOpen_snd_image <;> assumption)
