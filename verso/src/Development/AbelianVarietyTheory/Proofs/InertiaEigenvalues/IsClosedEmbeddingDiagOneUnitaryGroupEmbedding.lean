import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step

/- English proof (translation)
Establish `hc : Continuous (embHom r E)`. Express the relevant statement in the definitionally equal form `Continuous fun g : Matrix (Fin r) (Fin r) E => Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g 0 0 (1 : Matrix (Fin 1) (Fin 1) E))`. Conclude with `(continuous_id.matrix_fromBlocks continuous_const continuous_const continuous_const).matrix_reindex _ _`. Establish `hl : Function.LeftInverse (fun M : Matrix (Fin (r + 1)) (Fin (r + 1)) E => M.submatrix (Fin.castAdd 1) (Fin.castAdd 1)) (embHom r E)`. Introduce `g`.

Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `(Matrix.fromBlocks g 0 0 (1 : Matrix (Fin 1) (Fin 1) E)) (finSumFinEquiv.symm (Fin.castAdd 1 i)) (finSumFinEquiv.symm (Fin.castAdd 1 j)) = g i j`. Rewrite using `[finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd]`. Both sides reduce to the same expression. Conclude with `hl.isClosedEmbedding (continuous_id.matrix_submatrix _ _) hc`.
-/
theorem isClosedEmbedding_embHom (r : ℕ) (E : Type) [CommRing E] [TopologicalSpace E] [T2Space E] :
    Topology.IsClosedEmbedding (embHom r E) := by
  have hc : Continuous (embHom r E) := by
    change Continuous fun g : Matrix (Fin r) (Fin r) E =>
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g 0 0 (1 : Matrix (Fin 1) (Fin 1) E))
    exact (continuous_id.matrix_fromBlocks continuous_const continuous_const continuous_const).matrix_reindex _ _
  have hl : Function.LeftInverse
      (fun M : Matrix (Fin (r + 1)) (Fin (r + 1)) E => M.submatrix (Fin.castAdd 1) (Fin.castAdd 1))
      (embHom r E) := by
    intro g
    ext i j
    change (Matrix.fromBlocks g 0 0 (1 : Matrix (Fin 1) (Fin 1) E))
      (finSumFinEquiv.symm (Fin.castAdd 1 i)) (finSumFinEquiv.symm (Fin.castAdd 1 j)) = g i j
    rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd]
    rfl
  exact hl.isClosedEmbedding (continuous_id.matrix_submatrix _ _) hc

/- English proof (translation)
Establish `: (Matrix.unitaryGroup (Fin r) E : Set (Matrix (Fin r) (Fin r) E)) = {M | M * Mᴴ = 1}`. Use extensionality with `M`. Conclude with `Matrix.mem_unitaryGroup_iff`. Rewrite using `[this]`. Conclude with `isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose) continuous_const`.
-/
theorem isClosed_unitaryGroup (r : ℕ) (E : Type) [NormedField E] [StarRing E] [ContinuousStar E] :
    IsClosed (Matrix.unitaryGroup (Fin r) E : Set (Matrix (Fin r) (Fin r) E)) := by
  have : (Matrix.unitaryGroup (Fin r) E : Set (Matrix (Fin r) (Fin r) E)) = {M | M * Mᴴ = 1} := by
    ext M
    exact Matrix.mem_unitaryGroup_iff
  rw [this]
  exact isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose) continuous_const

/- English proof (translation)
Establish `h1 : Topology.IsClosedEmbedding (Subtype.val : Matrix.unitaryGroup (Fin (r + 1)) E → Matrix (Fin (r + 1)) (Fin (r + 1)) E)` using `(isClosed_unitaryGroup (r + 1) E).isClosedEmbedding_subtypeVal`. Establish `h0 : Topology.IsClosedEmbedding (Subtype.val : Matrix.unitaryGroup (Fin r) E → Matrix (Fin r) (Fin r) E)` using `(isClosed_unitaryGroup r E).isClosedEmbedding_subtypeVal`. Rewrite using `[← h1.of_comp_iff]`. Conclude with `(isClosedEmbedding_embHom r E).comp h0`.
-/
theorem isClosedEmbedding_uEmb (r : ℕ) (E : Type) [NormedField E] [StarRing E] [ContinuousStar E] :
    Topology.IsClosedEmbedding (GlobalTheory.JR.Step.uEmb r E) := by
  have h1 : Topology.IsClosedEmbedding
      (Subtype.val : Matrix.unitaryGroup (Fin (r + 1)) E → Matrix (Fin (r + 1)) (Fin (r + 1)) E) :=
    (isClosed_unitaryGroup (r + 1) E).isClosedEmbedding_subtypeVal
  have h0 : Topology.IsClosedEmbedding
      (Subtype.val : Matrix.unitaryGroup (Fin r) E → Matrix (Fin r) (Fin r) E) :=
    (isClosed_unitaryGroup r E).isClosedEmbedding_subtypeVal
  rw [← h1.of_comp_iff]
  exact (isClosedEmbedding_embHom r E).comp h0

end GlobalTheory.JR.Step
