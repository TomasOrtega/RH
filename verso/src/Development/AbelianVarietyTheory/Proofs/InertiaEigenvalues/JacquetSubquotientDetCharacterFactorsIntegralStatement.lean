import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetSubquotientDetCharacterFactorsIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LevelType.factor_eq_det_of_isSubquotient_jac` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FJacquetSubquotientDetCharacterFactorsIntegral.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.jacquetSubquotient_detCharacter_factors_integral : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n β : Type) [Fintype n] [DecidableEq n] [Fintype β] [LinearOrder β] (c : β → ℕ) (f : (Σ j, Fin (c j)) ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL n F) V) (ψ : Fˣ →* ℂˣ) (s : ∀ j, IrrRep (GL (Fin (c j)) F)), Nonempty (σ.Equiv (detRep n ψ)) → IsSubquotient (piTensor fun j => (s j).ρ) (jac f σ) → ∀ j, ∀ g ∈ KO F (Fin (c j)), ∀ v, (s j).ρ g v = (ψ (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
  first | exact @GlobalTheory.LevelType.factor_eq_det_of_isSubquotient_jac | exact GlobalTheory.LevelType.factor_eq_det_of_isSubquotient_jac | (intros; apply GlobalTheory.LevelType.factor_eq_det_of_isSubquotient_jac <;> assumption)
