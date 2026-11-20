import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerOfInducedBundleGenerated
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPowerOfInducedBundleGenerated.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.power_of_induced_bundle_generated : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p) (q : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced M L q cf → Y.ample A.D → ∃ m : ℕ, 1 ≤ m ∧ GlobalTheory.IsGenerated ((L.pow m).B.pull M.j) := by
  first | exact @GlobalTheory.TrueGeo.InducedGen.exists_isGenerated_pow | exact GlobalTheory.TrueGeo.InducedGen.exists_isGenerated_pow | (intros; apply GlobalTheory.TrueGeo.InducedGen.exists_isGenerated_pow <;> assumption)
