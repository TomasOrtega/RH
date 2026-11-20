import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPlaceOverJLineOfUpperHalfPlanePoint
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open Matrix GlobalTheory.KZ
open Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KZ.ValAt.exists_place` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsPlaceOverJLineOfUpperHalfPlanePoint.lean&line=221#L221)
-/
theorem _root_.GlobalTheory.T.exists_place_over_jLine_of_upperHalfPlane_point : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (τ : ℂ), τ ∈ Hs → ∃ W : ValuationSubring X.K, X.OverY W ∧ ∀ x : X.K, W.valuation x = 1 → ∀ φ : ℂ → ℂ, X.an x = (φ : Mero) → meromorphicOrderAt φ τ = 0 := by
  first | exact @GlobalTheory.KZ.ValAt.exists_place | exact GlobalTheory.KZ.ValAt.exists_place | (intros; apply GlobalTheory.KZ.ValAt.exists_place <;> assumption)
