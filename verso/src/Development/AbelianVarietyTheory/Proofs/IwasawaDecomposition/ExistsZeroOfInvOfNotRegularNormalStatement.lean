import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsZeroOfInvOfNotRegularNormal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsZeroOfInvOfNotRegularNormal.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.exists_zero_of_inv_of_not_regular_normal : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ (x : X) (f : X.functionField), ¬ RegAt x f → ∃ z : X, z ⤳ x ∧ ZeroAt z f⁻¹ := by
  first | exact @GlobalTheory.NormalPole.exists_zeroAt_inv | exact GlobalTheory.NormalPole.exists_zeroAt_inv | (intros; apply GlobalTheory.NormalPole.exists_zeroAt_inv <;> assumption)
