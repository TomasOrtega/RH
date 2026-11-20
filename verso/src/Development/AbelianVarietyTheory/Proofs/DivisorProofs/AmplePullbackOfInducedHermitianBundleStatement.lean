import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmplePullbackOfInducedHermitianBundle
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open NumberField CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.Mean4O

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAmplePullbackOfInducedHermitianBundle.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.ample_pullback_of_induced_hermitian_bundle : ∀ {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} (V : Cover Y) (A : Adl C Y) (L : HermLB V.p) (k : ℕ), 0 < k → V.Induces A L k → Y.ample A.D → IsAmpleLB (L.B.pull V.j) := by
  first | exact @GlobalTheory.Mean4O.Cover.isAmpleLB_pull_of_induces | exact GlobalTheory.Mean4O.Cover.isAmpleLB_pull_of_induces | (intros; apply GlobalTheory.Mean4O.Cover.isAmpleLB_pull_of_induces <;> assumption)
