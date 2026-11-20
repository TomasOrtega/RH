import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionGlTwoHolds
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.GTorus
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIwasawaDecompositionGlTwoHolds.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.iwasawa_decomposition_gl_two_holds : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (g : GL (Fin 2) F), ∃ (x : F) (m n : ℤ), ∃ κ ∈ GLnLocal.integralGL F 2, g = Ad3.uni2 x * Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ := by
  first | exact @GlobalTheory.CompanionTheory.GIntIw.iwasawa_decomposition_gl_two | exact GlobalTheory.CompanionTheory.GIntIw.iwasawa_decomposition_gl_two | (intros; apply GlobalTheory.CompanionTheory.GIntIw.iwasawa_decomposition_gl_two <;> assumption)
