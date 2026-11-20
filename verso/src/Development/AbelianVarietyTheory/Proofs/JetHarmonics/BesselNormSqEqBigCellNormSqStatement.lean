import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselNormSqEqBigCellNormSq
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.Jets.TauZero
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.jN2_eq_normSq_base.besselNormSq_eq_bigCellNormSq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FBesselNormSqEqBigCellNormSq.lean&line=83#L83)
-/
theorem _root_.GlobalTheory.T.jN2_eq_normSq_base : ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TBB.jN2 p F = B.normSq p.T.base F := by
  first | exact @GlobalTheory.jN2_eq_normSq_base.besselNormSq_eq_bigCellNormSq | exact GlobalTheory.jN2_eq_normSq_base.besselNormSq_eq_bigCellNormSq | (intros; apply GlobalTheory.jN2_eq_normSq_base.besselNormSq_eq_bigCellNormSq <;> assumption)
