import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalMetric
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsCubicalMetric.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.exists_cubical_metric : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ (j : Fl g → Pt E g → ℂ) (r : E → ℂ), IsFactor B τ (stdLat g) j → (∃ ι, IsBundleIso B τ (stdLat g) (mulPullFactor (-1) j) j ι) → IsRigidification B r → InducesPolarisation B τ (stdLat g) j → ∃ h, IsCubicalMetric B τ j r h := by
  first | exact @GlobalTheory.CubicalExist.exists_cubicalMetric | exact GlobalTheory.CubicalExist.exists_cubicalMetric | (intros; apply GlobalTheory.CubicalExist.exists_cubicalMetric <;> assumption)
