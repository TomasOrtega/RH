import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularStabilizerPointMatrixBlockDiagonal
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PointStab.stab_blockDiag` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FUnitriangularStabilizerPointMatrixBlockDiagonal.lean&line=87#L87)
-/
theorem _root_.GlobalTheory.T.unitriangularStabilizer_pointMatrix_blockDiagonal : ∀ {K : Type} [Field K] (sig : K →+* K), (∀ x, sig (sig x) = x) → ∀ (r : ℕ) (w : Formalism.MainNotions.S.Point K (r + 1)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K), Formalism.MainNotions.S.ZhatOM Z = Formalism.MainNotions.S.ptMat w → (∀ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) K, Formalism.MainNotions.S.IsUpUni s → Formalism.MainNotions.S.IsUpUni s' → (s.map sig).transpose * Z * s' = Z → ∀ a b : Fin (r + 1), Formalism.L2.SG.RealObj.blkOf w.1 a.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 b.1 → s' a b = 0) ∧ ∀ s' : Matrix (Fin (r + 1)) (Fin (r + 1)) K, Formalism.MainNotions.S.IsUpUni s' → (∀ a b : Fin (r + 1), Formalism.L2.SG.RealObj.blkOf w.1 a.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 b.1 → s' a b = 0) → ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) K, Formalism.MainNotions.S.IsUpUni s ∧ (s.map sig).transpose * Z * s' = Z := by
  first | exact @GlobalTheory.PointStab.stab_blockDiag | exact GlobalTheory.PointStab.stab_blockDiag | (intros; apply GlobalTheory.PointStab.stab_blockDiag <;> assumption)
