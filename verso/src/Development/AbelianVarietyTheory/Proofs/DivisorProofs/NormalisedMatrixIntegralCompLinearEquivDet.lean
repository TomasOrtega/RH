import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedOpenCompactEqIntegralDivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionDistribHaarCharEqAbsHalfSqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCompLinearMapMatrixNonarchLocalFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactIntegralMatrixAddSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompLinearAutLocallyConstantCompactSupportMatrixStatement

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open MeasureTheory

/- English proof (translation)
Introduce `E _ _ w a b L φ hL hU hc`. Take `⟨Λ, hΛo, hΛc, hΛ⟩` from `GlobalTheory.T.exists_open_compact_integralMatrixAddSubgroup E w a b`. Take `⟨hU', hc', hlc⟩` from `GlobalTheory.T.comp_linearAut_locallyConstant_compactSupport_matrix E w a b L φ hL hU hc`. Use `letI : MeasurableSpace (Matrix (Fin a) (Fin b) (w.adicCompletion E)) := borel _`. Use `haveI : BorelSpace (Matrix (Fin a) (Fin b) (w.adicCompletion E)) := ⟨rfl⟩`.

Set `μ : Measure (Matrix (Fin a) (Fin b) (w.adicCompletion E))` to `Measure.addHaar`. Establish `hμ : μ.IsAddHaarMeasure` using `inferInstance`. Rewrite using `[hΛ, GlobalTheory.T.haarIntegralNormalizedOpenCompact_eq_integral_div _ μ hμ Λ hΛo hΛc _ hU' hc', GlobalTheory.T.haarIntegralNormalizedOpenCompact_eq_integral_div _ μ hμ Λ hΛo hΛc _ hU hc, GlobalTheory.T.integral_comp_linearMap_matrix_nonarchLocalField _ a b L hL φ μ hμ, GlobalTh …`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.LeviDesc.hint_comp_linear : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ) (L : Matrix (Fin a) (Fin b) (w.adicCompletion E) →ₗ[w.adicCompletion E] Matrix (Fin a) (Fin b) (w.adicCompletion E)) (φ : Matrix (Fin a) (Fin b) (w.adicCompletion E) → ℂ), LinearMap.det L ≠ 0 → (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, φ (x + y) = φ x) → HasCompactSupport φ → hint (intMat a b w) (fun X => φ (L (Multiplicative.toAdd X))) = (absHalf w (LinearMap.det L) ^ 2)⁻¹ * hint (intMat a b w) (fun X => φ (Multiplicative.toAdd X)) := by
  intro E _ _ w a b L φ hL hU hc
  obtain ⟨Λ, hΛo, hΛc, hΛ⟩ := GlobalTheory.T.exists_open_compact_integralMatrixAddSubgroup E w a b
  obtain ⟨hU', hc', hlc⟩ := GlobalTheory.T.comp_linearAut_locallyConstant_compactSupport_matrix E w a b L φ hL hU hc
  letI : MeasurableSpace (Matrix (Fin a) (Fin b) (w.adicCompletion E)) := borel _
  haveI : BorelSpace (Matrix (Fin a) (Fin b) (w.adicCompletion E)) := ⟨rfl⟩
  let μ : Measure (Matrix (Fin a) (Fin b) (w.adicCompletion E)) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  rw [hΛ, GlobalTheory.T.haarIntegralNormalizedOpenCompact_eq_integral_div _ μ hμ Λ hΛo hΛc _ hU' hc', GlobalTheory.T.haarIntegralNormalizedOpenCompact_eq_integral_div _ μ hμ Λ hΛo hΛc _ hU hc,
    GlobalTheory.T.integral_comp_linearMap_matrix_nonarchLocalField _ a b L hL φ μ hμ, GlobalTheory.T.adicCompletion_distribHaarChar_eq_absHalf_sq E w _ hL]
  ring
