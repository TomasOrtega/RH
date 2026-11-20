import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitValueZeroDiagonalNorm
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceEmbeddingPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComponentRationalIdeleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWeilActionDiagonalStatement
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSplitValueZeroDiagonalNorm.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.split_value_zero_diagonal_norm : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → L.IsSp → ∀ (g : GL (Fin 2) (Qv v)) (κ : Kˣ),
    L.val (dg2 (nv v κ) 1 * g) 0 = c0 L κ * mp (nv v κ) (1 / 2) * L.val g 0 := by
  first | exact @GlobalTheory.CompanionTheory.FexTheta.value_zero_diagonal_norm | exact GlobalTheory.CompanionTheory.FexTheta.value_zero_diagonal_norm | (intros; apply GlobalTheory.CompanionTheory.FexTheta.value_zero_diagonal_norm <;> assumption)
