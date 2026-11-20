import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PrincipalLevelEqHalfMarkingStabilizer
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Member.finCong_iff_half_and_kfHalf` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUnitaryExistence%2FPrincipalLevelEqHalfMarkingStabilizer.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.principalLevel_eq_halfMarking_stabilizer : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (V : HSp D), (∀ k : GA D V, FinCong V l.M k ↔ ∀ b ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E), ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec (halfVec V b z) - halfVec V b z = l.M • y) ∧ ∀ Kf : Subgroup (GA D V), IsLevelK V l.M Kf → KfHalf V Kf l.M (l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) := by
  first | exact @GlobalTheory.Member.finCong_iff_half_and_kfHalf | exact GlobalTheory.Member.finCong_iff_half_and_kfHalf | (intros; apply GlobalTheory.Member.finCong_iff_half_and_kfHalf <;> assumption)
