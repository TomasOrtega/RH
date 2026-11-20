import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnipotentTriangularOfPeriodCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGenericComponentPointsOffMeagre
open NumberField
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PeriodUnipotent.exists_unipotent_of_pc_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsUnipotentTriangularOfPeriodCoordinatesEq.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.exists_unipotentTriangular_of_periodCoordinates_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x x' : Frame X.Ψ r), x ∈ X.dom → x' ∈ X.dom → (∀ v ∈ X.Λ, ∀ τ a, GlobalTheory.GenericFrames.pc X x' v τ a = GlobalTheory.GenericFrames.pc X x v τ a) → ∃ b ∈ Bor X.Ψ r, (∀ τ i, b τ i i = 1) ∧ x' = rmul x b := by
  first | exact @GlobalTheory.PeriodUnipotent.exists_unipotent_of_pc_eq | exact GlobalTheory.PeriodUnipotent.exists_unipotent_of_pc_eq | (intros; apply GlobalTheory.PeriodUnipotent.exists_unipotent_of_pc_eq <;> assumption)
