import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryMatrixMajorantOperatorNormLeDefinite
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnitaryMatrixMajorantOperatorNormLeDefinite.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.unitaryMatrix_majorantOperatorNorm_le_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (X.p0 = 0 ∨ X.p0 = r) → ∀ x ∈ X.dom, ∀ β : GL (Fin r) E, (∀ v w, herm X.Gm (Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) v) (Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) w) = herm X.Gm v w) → ∀ τ : X.Ψ, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.OpNormLe X x τ (β : Matrix (Fin r) (Fin r) E) (Real.exp (1 / (3 * (r : ℝ)))) := by
  first | exact @GlobalTheory.DefiniteOpNorm.opNormLe_definite | exact GlobalTheory.DefiniteOpNorm.opNormLe_definite | (intros; apply GlobalTheory.DefiniteOpNorm.opNormLe_definite <;> assumption)
