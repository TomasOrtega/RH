import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusDetLongWeylBlock
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lpart
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.DeterminantLongWeyl.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FModulusDetLongWeylBlock.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.modulus_det_long_weyl_block : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (h : GL (Fin 2) F), mp (GeneralLinearGroup.det (w3 * tinv (em h))) 1 = mp (GeneralLinearGroup.det h) (-1) := by
  first | exact @GlobalTheory.CompanionTheory.DeterminantLongWeyl.main | exact GlobalTheory.CompanionTheory.DeterminantLongWeyl.main | (intros; apply GlobalTheory.CompanionTheory.DeterminantLongWeyl.main <;> assumption)
