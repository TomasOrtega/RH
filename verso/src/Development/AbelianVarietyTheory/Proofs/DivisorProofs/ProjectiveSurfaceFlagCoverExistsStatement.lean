import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveSurfaceFlagCoverExists
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagCover.flagCoverExists` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FProjectiveSurfaceFlagCoverExists.lean&line=97#L97)
-/
theorem _root_.GlobalTheory.T.projective_surface_flag_cover_exists : ∀ (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)] [IsIntegral T], IsProjSurface k T → FlagCoverExists k T := by
  first | exact @GlobalTheory.FlagCover.flagCoverExists | exact GlobalTheory.FlagCover.flagCoverExists | (intros; apply GlobalTheory.FlagCover.flagCoverExists <;> assumption)
