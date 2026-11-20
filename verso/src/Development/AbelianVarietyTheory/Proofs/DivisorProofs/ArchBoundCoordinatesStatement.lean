import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchBoundCoordinates
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchAt
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThetaDecay.Coord.coord_bound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FArchBoundCoordinates.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.arch_bound_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ K : ℝ, 0 ≤ K ∧
    ∀ (y : AE F E) (B : ℝ), 0 ≤ B → (∀ (w : InfinitePlace F) (τ : EmbOver E w), ‖piInf τ y‖ ≤ B) →
    ∀ r w, ‖archAt F w ((coB F E).repr y r)‖ ≤ K * B := by
  first | exact @GlobalTheory.ThetaDecay.Coord.coord_bound | exact GlobalTheory.ThetaDecay.Coord.coord_bound | (intros; apply GlobalTheory.ThetaDecay.Coord.coord_bound <;> assumption)
