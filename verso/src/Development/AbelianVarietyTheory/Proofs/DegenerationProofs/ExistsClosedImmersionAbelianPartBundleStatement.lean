import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClosedImmersionAbelianPartBundle
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FExistsClosedImmersionAbelianPartBundle.lean&line=83#L83)
-/
theorem _root_.GlobalTheory.T.exists_closedImmersion_abelianPart_bundle : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (N : ℕ), 4 ≤ N → Φ.Pol N → ∃ (m : ℕ) (t : Fin m → Φ.N₀.Sec), ImmBy Φ.E.B.hom Φ.N₀ t Set.univ) := by
  first | exact @GlobalTheory.VeryAmpleMove.exists_immBy_abelianPart | exact GlobalTheory.VeryAmpleMove.exists_immBy_abelianPart | (intros; apply GlobalTheory.VeryAmpleMove.exists_immBy_abelianPart <;> assumption)
