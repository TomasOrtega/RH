import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricHeckeGenericEigenvalueMapMul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupportParahoricBiTransformingDoubleCosets
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ParHecke.genVal_map_mul` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FParahoricHeckeGenericEigenvalueMapMul.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.parahoricHeckeGenericEigenvalue_map_mul : ∀ (q r N n : ℕ) (B : Multiset ℂˣ) (c : ℂˣ), genVal q r N (B.map (· * c)) n = (c : ℂ) ^ n * genVal q r N B n := by
  first | exact @GlobalTheory.ParHecke.genVal_map_mul | exact GlobalTheory.ParHecke.genVal_map_mul | (intros; apply GlobalTheory.ParHecke.genVal_map_mul <;> assumption)
