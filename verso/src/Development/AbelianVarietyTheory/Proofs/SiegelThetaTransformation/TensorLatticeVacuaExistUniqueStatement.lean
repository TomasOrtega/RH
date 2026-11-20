import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SW.TensVac.vacua` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSiegelThetaTransformation%2FTensorLatticeVacuaExistUnique.lean&line=558#L558)
-/
theorem _root_.GlobalTheory.T.tensorLattice_vacua_exist_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L, SelfD X L → ∀ (M : ℕ), ∀ Λ ∈ Vset E n M, (∃ v, IsVac X bas w (tens Λ L) v) ∧ (∀ v v', IsVac X bas w (tens Λ L) v → IsSB v' → (∀ y ∈ tens Λ L, epsW X w y • heisG X bas y v' = v') → v' = ip v' v • v) ∧ (∀ φ : TF n g, IsSB φ → ∀ v, IsVac X bas w (tens Λ L) v → projA X bas w (tens Λ L) φ = ip φ v • v) ∧ ∀ L', SelfD X L' → ∀ Λ' ∈ Vset E n M, ∀ v v', IsVac X bas w (tens Λ L) v → IsVac X bas w (tens Λ' L') v' → ((tens Λ' L').relIndex (tens Λ L) : ℝ) * ‖ip v v'‖ ^ 2 = 1 := by
  first | exact @GlobalTheory.SW.TensVac.vacua | exact GlobalTheory.SW.TensVac.vacua | (intros; apply GlobalTheory.SW.TensVac.vacua <;> assumption)
