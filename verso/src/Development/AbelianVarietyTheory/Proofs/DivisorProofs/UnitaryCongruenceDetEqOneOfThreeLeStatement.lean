import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCongruenceDetEqOneOfThreeLe
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnitaryCongruenceDetEqOneOfThreeLe.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.unitaryCongruence_det_eq_one_of_three_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E), 3 ≤ M → G.det ≠ 0 → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → IsUStab G Λ γ → (∀ x ∈ Λ, ∃ y ∈ Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = M • y) → (γ : Matrix (Fin r) (Fin r) E).det = 1 := by
  first | exact @GlobalTheory.UnitaryCongruenceDetAny.det_eq_one | exact GlobalTheory.UnitaryCongruenceDetAny.det_eq_one | (intros; apply GlobalTheory.UnitaryCongruenceDetAny.det_eq_one <;> assumption)
