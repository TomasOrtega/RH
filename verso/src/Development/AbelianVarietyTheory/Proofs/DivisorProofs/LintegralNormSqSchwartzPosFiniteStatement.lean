import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqSchwartzPosFinite
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.schwartzBruhat_matrix_lintegral_sq_ne_zero_ne_top` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLintegralNormSqSchwartzPosFinite.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.lintegral_norm_sq_schwartz_pos_finite : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a d : ℕ}
    (Φ : Matrix (Fin a) (Fin d) k → ℂ), Φ ∈ SB (Matrix (Fin a) (Fin d) k) → Φ ≠ 0 →
    ∀ ν : @Measure (Matrix (Fin a) (Fin d) k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν ≠ 0 ∧ ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν ≠ ⊤ := by
  first | exact @GlobalTheory.schwartzBruhat_matrix_lintegral_sq_ne_zero_ne_top | exact GlobalTheory.schwartzBruhat_matrix_lintegral_sq_ne_zero_ne_top | (intros; apply GlobalTheory.schwartzBruhat_matrix_lintegral_sq_ne_zero_ne_top <;> assumption)
