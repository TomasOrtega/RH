import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordinateLatticeSelfDualIsFullRank
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrLink
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.St.G.coordLat_isLat` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FCoordinateLatticeSelfDualIsFullRank.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.coordinateLattice_selfDual_isFullRank : ∀ (D : D7) (X : HidaSetting D), IsLat ((VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E))) := by
  first | exact @GlobalTheory.St.G.coordLat_isLat | exact GlobalTheory.St.G.coordLat_isLat | (intros; apply GlobalTheory.St.G.coordLat_isLat <;> assumption)
