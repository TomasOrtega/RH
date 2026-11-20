import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComapMulVecCompactOpen
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FComapMulVecCompactOpen.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.isCompact_isOpen_comap_mulVecLin : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (g : Matrix (Fin n) (Fin n) k), IsUnit g → ∀ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → IsCompact ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) ∧ IsOpen ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) := by
  first | exact @GlobalTheory.CompanionTheory.Dblock.ComapLat.comap_mulVec_compact_open | exact GlobalTheory.CompanionTheory.Dblock.ComapLat.comap_mulVec_compact_open | (intros; apply GlobalTheory.CompanionTheory.Dblock.ComapLat.comap_mulVec_compact_open <;> assumption)
