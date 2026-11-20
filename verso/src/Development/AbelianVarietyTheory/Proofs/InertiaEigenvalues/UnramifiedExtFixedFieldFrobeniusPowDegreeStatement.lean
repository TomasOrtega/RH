import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedExtFixedFieldFrobeniusPowDegree
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PMon.UnrDeg.fixed_field_deg` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FUnramifiedExtFixedFieldFrobeniusPowDegree.lean&line=91#L91)
-/
theorem _root_.GlobalTheory.T.unramifiedExt_fixedField_frobeniusPow_degree : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∃ (E : FinExt l) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), E.1 ≤ MaximalUnramifiedExtension l ∧ Module.finrank ℚ_[l] ↥E.1 = r ∧ (∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c ↔ (c : Om l) ∈ E.1) ∧ (∀ k, fr l r (ω k) = ω k) ∧ LinearIndependent ℚ_[l] ω ∧ (∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → ∃ a : Fin r → ℚ_[l], c = ∑ k, a k • ω k) ∧ (Matrix.of fun m k : Fin r => fr l m (ω k)).det ≠ 0 := by
  first | exact @GlobalTheory.PMon.UnrDeg.fixed_field_deg | exact GlobalTheory.PMon.UnrDeg.fixed_field_deg | (intros; apply GlobalTheory.PMon.UnrDeg.fixed_field_deg <;> assumption)
