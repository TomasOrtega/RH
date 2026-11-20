import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMulFirstFactorLagrangianAl
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SplitDblGen.diagonalFixingDoubling_mul_firstFactor_lagrangian` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FDiagonalFixingDoublingMulFirstFactorLagrangianAl.lean&line=73#L73)
-/
theorem _root_.GlobalTheory.T.diagonalFixingDoublingMatrix_mul_fromBlocks_mul_diagCols : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (c : AE F E) (K K' : Matrix (Fin d) (Fin d) (AE F E)),
    K * K' = 1 → K' * K = 1 → (c * c) • (K - 1) = K - 1 →
    GlobalTheory.SplitDblGen.diagonalFixingDoublingMatrix c d * Matrix.fromBlocks K 0 0 1 * diagCols (E := AE F E) (Fin d) =
      GlobalTheory.SplitDblGen.nMat c K K' * diagCols (E := AE F E) (Fin d) * GlobalTheory.SplitDblGen.tMat c K := by
  first | exact @GlobalTheory.SplitDblGen.diagonalFixingDoubling_mul_firstFactor_lagrangian | exact GlobalTheory.SplitDblGen.diagonalFixingDoubling_mul_firstFactor_lagrangian | (intros; apply GlobalTheory.SplitDblGen.diagonalFixingDoubling_mul_firstFactor_lagrangian <;> assumption)
