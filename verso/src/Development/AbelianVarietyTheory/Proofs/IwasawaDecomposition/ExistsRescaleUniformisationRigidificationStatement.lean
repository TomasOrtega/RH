import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRescaleUniformisationRigidification
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeyAtIffExistsKeyAtVia
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolFibreIdCompCancel
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RigRescale.exists_rescale_rig` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsRescaleUniformisationRigidification.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.exists_rescale_uniformisation_rigidification : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g) (rig : LB.Gen (L.pull (eSec A))), L.IsLB → rig.IsGen → ∃ (u' : HolUnif A L g) (lam : ℂ), lam ≠ 0 ∧ u'.ex = u.ex ∧ u'.Λ = u.Λ ∧ u'.IsRig rig ∧ ∀ i z, u'.fr i z = lam * u.fr i z := by
  first | exact @GlobalTheory.RigRescale.exists_rescale_rig | exact GlobalTheory.RigRescale.exists_rescale_rig | (intros; apply GlobalTheory.RigRescale.exists_rescale_rig <;> assumption)
