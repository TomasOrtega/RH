import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CntPrimLatticeImageIsometry
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LoopC.cntPrim_gmap_isom` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FCntPrimLatticeImageIsometry.lean&line=81#L81)
-/
theorem _root_.GlobalTheory.T.cntPrim_latticeImage_isometry : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), ∀ γ ∈ Formalism.HermitianLatticesTheory.isom h, ∀ (L : Submodule (𝓞 K) V) (j de : ℕ), cntPrim h (Formalism.HermitianLatticesTheory.gmap γ L) j de = cntPrim h L j de := by
  first | exact @GlobalTheory.LoopC.cntPrim_gmap_isom | exact GlobalTheory.LoopC.cntPrim_gmap_isom | (intros; apply GlobalTheory.LoopC.cntPrim_gmap_isom <;> assumption)
