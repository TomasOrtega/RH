import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanPrimitiveCorankOneSublatticesBound
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenericAdmissibleFamilyOfSteps
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mass.PrimMeanCorankOne.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FMeanPrimitiveCorankOneSublatticesBound.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.mean_primitive_corank_one_sublattices_bound : ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ), UnitaryVolumeMass.stMassRatio D → Formalism.MainNotions.BridgeLemma₂.PrimitiveMeanCorankOne D large₂ u u' C' Cl Cg cb Cu cT CT C0 A := by
  first | exact @GlobalTheory.Mass.PrimMeanCorankOne.main | exact GlobalTheory.Mass.PrimMeanCorankOne.main | (intros; apply GlobalTheory.Mass.PrimMeanCorankOne.main <;> assumption)
